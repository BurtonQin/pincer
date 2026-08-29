use rustc_hir::def_id::DefId;
use rustc_middle::mir::{Body, Place, PlaceElem, ProjectionElem};
use rustc_middle::ty::{Ty, TyCtxt, TyKind};
use rustc_abi::FieldIdx;

use crate::util::type_util;

use super::function::FuncDef;

pub trait PlaceExt<'tcx> {
    /// Returns true if the base local of `self` is a function parameter.
    fn is_from_param(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> bool;

    /// Returns the interior pointer field of a box.
    /// Callers must ensure that `self` is a box.
    /// ty: The type of the box.
    fn box_ptr_field(&self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Place<'tcx>;

    /// Transforms box dereference into box's interior pointer access.
    fn expand_box_deref(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> Place<'tcx>;

    /// Returns `true` if `self` is place projected out from an array.
    fn is_projection_of_array(&self) -> bool;

    /// Returns true if this place's base [`Local`] corresponds to code that is visible in the source.
    fn is_source_visible(&self, tcx: TyCtxt, body: &Body) -> bool;

    /// Returns the specialized type of the place
    fn specialized_ty(&self, tcx: TyCtxt<'tcx>, func: FuncDef<'tcx>) -> Ty<'tcx>;

    /// Checks whether a `Place` is valid:
    /// - The `local` must exist in the `Body::local_decls`.
    /// - Each projection must be valid based on type information.
    fn is_valid(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool;

    fn remove_deref_elem(&self, tcx: TyCtxt<'tcx>) -> Place<'tcx>;

    /// Returns the base place being dereferenced.
    /// Return None if the given place is not indirect.
    fn base_place_of_deref(&self, tcx: TyCtxt<'tcx>) -> Option<Place<'tcx>>;
}

impl<'tcx> PlaceExt<'tcx> for Place<'tcx> {
    fn is_from_param(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
        let arg_count = tcx.optimized_mir(def_id).arg_count;
        let i = self.local.as_usize();
        i > 0 && i <= arg_count
    }

    fn box_ptr_field(&self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Place<'tcx> {
        let get_first_field = |ty: Ty<'tcx>| {
            if let TyKind::Adt(def, args) = ty.kind() {
                let variant = def.variants().iter().next().unwrap();
                let field_ty = variant.fields.iter().next().unwrap().ty(tcx, args);
                (FieldIdx::from_u32(0), field_ty)
            } else {
                unreachable!("Expected ADT type, found {:?}", ty)
            }
        };
        
        let (field_unique, ty_unique) = get_first_field(ty);
        let (field_nonnull, ty_nonnull) = get_first_field(ty_unique);
        let (field_ptr, ty_ptr) = get_first_field(ty_nonnull);
        let box_ptr_projection = vec![
            ProjectionElem::Field(field_unique, ty_unique),
            ProjectionElem::Field(field_nonnull, ty_nonnull),
            ProjectionElem::Field(field_ptr, ty_ptr),
        ];
        self.project_deeper(box_ptr_projection.as_slice(), tcx)
    }


    fn expand_box_deref(&self, tcx: TyCtxt<'tcx>, def_id: DefId) -> Place<'tcx> {
        if self.is_indirect() {
            assert!(matches!(self.projection[0], ProjectionElem::Deref));
            let local = self.local;
            let local_ty = Place::from(local).ty(tcx.optimized_mir(def_id), tcx).ty;
            if local_ty.is_box() {
                let box_ptr = Place::from(local).box_ptr_field(tcx, local_ty);
                box_ptr.project_deeper(&self.projection[1..], tcx)
            } else {
                self.clone()
            }
        } else {
            self.clone()
        }
    }

    fn is_projection_of_array(&self) -> bool {
        self.projection.iter().any(|proj_elem| {
            matches!(
                proj_elem,
                ProjectionElem::Index(_) | ProjectionElem::Subslice { .. }
            )
        })
    }

    fn is_source_visible(&self, _tcx: TyCtxt, body: &Body) -> bool {
        let local = self.local;
        let local_info = &body.local_decls[local];
        let is_loc = local_info.is_user_variable();
        let from_desugaring = local_info.from_compiler_desugaring();
        let from_expansion = local_info.source_info.span.from_expansion();
    
        // The assumption is that for a place to be source visible it needs to:
        // 1. Be a local declaration.
        // 2. Not be from a compiler desugaring.
        // 3. Not be from a macro expansion (basically also a desugaring).
        is_loc && !from_desugaring && !from_expansion
      }

    fn specialized_ty(&self, tcx: TyCtxt<'tcx>, func: FuncDef<'tcx>) -> Ty<'tcx> {
        type_util::place_ty(tcx, self, func)
    }

    fn is_valid(&self, tcx: TyCtxt<'tcx>, body: &Body<'tcx>) -> bool {
        // Check if the local is within valid range
        if self.local.as_usize() >= body.local_decls.len() {
            return false;
        }

        // Start with the base type of the local
        let mut ty = body.local_decls[self.local].ty;

        // Traverse each projection step and validate it
        for proj in self.projection.iter() {
            ty = match proj {
                PlaceElem::Deref => {
                    // Ensure it is a pointer type
                    // Box is not considered a pointer here while it can be dereferenced directly.
                    if ty.is_any_ptr() {
                        type_util::get_dereferenced_type(ty)
                    } else {
                        return false;
                    }
                }
                PlaceElem::Field(field, _) => {
                    // Ensure it is a struct, tuple, or enum variant
                    match ty.kind() {
                        TyKind::Adt(def, _) if def.is_struct() || def.is_union() => {
                            let variant = def.variants().iter().next().expect("at least one variant");
                            if field.index() >= variant.fields.len() {
                                return false; // Out-of-bounds field access
                            }
                        }
                        TyKind::Tuple(tuple_types) => {
                            if field.index() >= tuple_types.len() {
                                return false; // Out-of-bounds tuple field
                            }
                        }
                        _ => {
                            if ty.is_closure() || ty.is_coroutine() {
                                let closure_field_types = type_util::closure_field_types(ty);
                                if field.index() >= closure_field_types.len() {
                                    return false;
                                }
                            } else {
                                return false; // Invalid field access
                            }
                        }
                    };
                    type_util::get_field_type(tcx, ty, field.index().into())
                }
                PlaceElem::Index(_) 
                | PlaceElem::ConstantIndex { .. } => {
                    // Ensure it is an array or slice
                    match ty.kind() {
                        TyKind::Array(inner_ty, _) | TyKind::Slice(inner_ty) => *inner_ty,
                        _ => return false, // Invalid indexing
                    }
                }
                PlaceElem::Subslice { .. } => {
                    match ty.kind() {
                        TyKind::Array(..) | TyKind::Slice(..) => ty, // keeps the same type
                        _ => return false,
                    }
                }
                PlaceElem::Downcast(_, variant_idx) => {
                    // Ensure it's an enum and the variant index is valid
                    match ty.kind() {
                        TyKind::Adt(def, _) if def.is_enum() => {
                            if variant_idx.as_usize() >= def.variants().len() {
                                return false; // Invalid variant index
                            }
                            type_util::get_downcast_type(tcx, ty, variant_idx)
                        }
                        _ => return false, // Downcast on non-enum
                    }
                }
                PlaceElem::OpaqueCast(ty) | PlaceElem::UnwrapUnsafeBinder(ty) => ty,
            };
        }

        true
    }

    fn remove_deref_elem(&self, tcx: TyCtxt<'tcx>) -> Place<'tcx> {
        if self.is_indirect() {
            Place {
                local: self.local,
                projection: tcx.mk_place_elems(&self.projection[1..]),
            }
        } else {
            self.clone()
        }
    }

    fn base_place_of_deref(&self, tcx: TyCtxt<'tcx>) -> Option<Place<'tcx>> {
        if self.is_indirect() {
            let deref_idx = self.projection.iter().position(|elem| matches!(elem, PlaceElem::Deref)).unwrap();
            Some(Place {
                local: self.local,
                projection: tcx.mk_place_elems(&self.projection[..deref_idx]),
            })
        } else {
            None
        }
    }
    
}



#[test]
fn test_base_place_of_deref() {
    use crate::util::test_util::compile;
    use rustc_middle::mir;

    let rust_code = r#"
        fn main() {}
    "#;

    compile(rust_code.to_string(), |tcx| {
        let local = mir::Local::from_u32(0);
        let place = Place::from(local);
        let deref_place = tcx.mk_place_deref(place);
        let base_place = deref_place.base_place_of_deref(tcx).unwrap();
        assert_eq!(base_place, place);
        let index_place = tcx.mk_place_index(place, local);
        let deref_place = tcx.mk_place_deref(index_place);
        let proj_place = tcx.mk_place_index(deref_place, local);
        let base_place = proj_place.base_place_of_deref(tcx).unwrap();
        assert_eq!(base_place, index_place);
    });
}
