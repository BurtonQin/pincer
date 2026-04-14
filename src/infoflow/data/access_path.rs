use log::*;
use std::fmt::{Debug, Formatter, Result};

use multimap::MultiMap;
use rustc_middle::mir::{Local, Location, Place, PlaceElem};
use rustc_middle::ty::Ty;
use std::collections::HashSet;

use super::access_elem::{try_to_eval_possible_types, AccessElem, AccessElems};
use crate::analysis_context::AnalysisContext;
use crate::infoflow::Unit;
use crate::mir::function::FuncDef;
use crate::mir::place_ext::PlaceExt;
use crate::mir::projection::ProjectionIdx;
use crate::util::{self, type_util};


#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct AccessPath<'tcx> {
    pub func_def: FuncDef<'tcx>,
    pub local: Local,
    pub access_elems: AccessElems<'tcx>,
    pub deactivation_point: Option<Location>,
    /// Only set when the path corresponds to a heap fact.
    pub alloc_trace: Option<&'tcx [Unit<'tcx>]>,
}

impl<'tcx> Debug for AccessPath<'tcx> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        let func_name = util::parse_func_name_from_def_id(self.func_def.def_id);
        let suffix = if self.is_heap_pointer() { "¤" } else { "" };
        if self.access_elems.is_empty() {
            write!(f, "{}::{:?}{}", func_name, self.local, suffix)
        } else {
            let elems: String = self
                .access_elems
                .iter()
                .map(|x| format!(".{x:?}"))
                .collect();
            write!(f, "{}::{:?}{}{}", func_name, self.local, elems, suffix)
        }
    }
}

impl<'tcx> AccessPath<'tcx> {
    pub fn new(
        func_def: FuncDef<'tcx>,
        local: Local,
        access_elems: AccessElems<'tcx>,
    ) -> AccessPath<'tcx> {
        AccessPath {
            func_def,
            local,
            access_elems,
            deactivation_point: None,
            alloc_trace: None,
        }
    }

    pub fn access_elems(&self) -> AccessElems<'tcx> {
        self.access_elems
    }

    pub fn is_inactive(&self) -> bool {
        self.deactivation_point.is_some()
    }

    pub fn is_heap_pointer(&self) -> bool {
        self.alloc_trace.is_some()
    }

    /// Returns true if the base local is a function parameter.
    pub fn is_from_param(&self, tcx: rustc_middle::ty::TyCtxt<'tcx>) -> bool {
        Place::from(self.local).is_from_param(tcx, self.func_def.def_id)
    }

    /// Returns true if the base local is the return place (_0).
    pub fn is_from_ret(&self) -> bool {
        self.local.as_usize() == 0
    }

    pub fn deactivate_at(&self, deactivation_point: Location) -> AccessPath<'tcx> {
        AccessPath {
            deactivation_point: Some(deactivation_point),
            alloc_trace: None,
            ..*self
        }
    }

    pub fn activate(&self) -> AccessPath<'tcx> {
        AccessPath {
            deactivation_point: None,
            ..*self
        }
    }

    pub fn with_alloc_site(
        &self,
        acx: &AnalysisContext<'tcx>,
        alloc_site: Unit<'tcx>,
    ) -> AccessPath<'tcx> {
        assert!(!self.is_inactive());
        AccessPath {
            alloc_trace: Some(acx.mk_units(&[alloc_site])),
            ..*self
        }
    }

    pub fn get_alloc_site(&self) -> Option<Unit<'tcx>> {
        self.alloc_trace.and_then(|trace| trace.first().cloned())
    }

    pub fn extend_alloc_trace(
        &self,
        acx: &AnalysisContext<'tcx>,
        unit: Unit<'tcx>,
    ) -> AccessPath<'tcx> {
        AccessPath {
            alloc_trace: Some(acx.append_unit(self.alloc_trace.unwrap(), unit)),
            ..*self
        }
    }

    pub fn pop_alloc_trace(&self) -> AccessPath<'tcx> {
        let trace = self
            .alloc_trace
            .expect("pop_alloc_trace requires alloc_trace");
        assert!(!trace.is_empty());
        let alloc_trace = if trace.len() == 1 {
            None
        } else {
            Some(&trace[..trace.len() - 1])
        };
        AccessPath {
            alloc_trace,
            ..*self
        }
    }

    pub fn discard_alloc_trace(&self) -> AccessPath<'tcx> {
        AccessPath {
            alloc_trace: None,
            ..*self
        }
    }

    pub fn from_rustc_place(
        acx: &AnalysisContext<'tcx>,
        func_def: FuncDef<'tcx>,
        place: &Place<'tcx>,
    ) -> AccessPath<'tcx> {
        let local = place.local;
        let access_elems = if place.projection.is_empty() {
            acx.mk_access_elems(&[])
        } else if *place.projection.first().unwrap() == PlaceElem::Deref {
            let local_ty = type_util::place_ty(acx.tcx,&Place::from(local), func_def);
            let local_deref_ty = type_util::get_dereferenced_type(local_ty);
            let proj_idx = acx
                .get_projection_idx(
                    local_deref_ty,
                    acx.tcx.mk_place_elems(&place.projection[1..]),
                )
                .unwrap_or_else(|| {
                    panic!(
                        "Indexing error: fail to index {:?} of {:?}",
                        &place.projection[1..],
                        local_deref_ty
                    )
                });
            acx.mk_access_elems(&[AccessElem::Deref, AccessElem::AggTyProj(proj_idx)])
        } else {
            let local_ty = type_util::place_ty(acx.tcx,&Place::from(local), func_def);
            let proj_idx = acx
                .get_projection_idx(local_ty, place.projection)
                .unwrap_or_else(|| {
                    panic!(
                        "Indexing error: fail to index {:?} of {:?}",
                        place.projection, local_ty
                    )
                });
            acx.mk_access_elems(&[AccessElem::AggTyProj(proj_idx)])
        };
        AccessPath::new(func_def, local, access_elems)
    }

    pub fn from_rustc_place_with_elems(
        acx: &AnalysisContext<'tcx>,
        func_def: FuncDef<'tcx>,
        place: &Place<'tcx>,
        elems: AccessElems<'tcx>,
    ) -> AccessPath<'tcx> {
        Self::from_rustc_place(acx, func_def, place).project_deeper(acx, elems)
    }

    pub fn project_deeper(&self, acx: &AnalysisContext<'tcx>, elems: AccessElems<'tcx>) -> Self {
        if self.access_elems.is_empty() {
            return AccessPath {
                access_elems: elems,
                ..*self
            };
        }
        if elems.is_empty() {
            return *self;
        }
        if self.has_ref_elem() {
            if elems.first().unwrap().is_deref() {
                return self.remove_ref_elem().project_deeper(acx, &elems[1..]);
            } else {
                warn!(
                    "Error: cannot project {:?} from {:?}.",
                    elems, self.access_elems
                );
            }
        }
        if self.access_elems.last().unwrap().is_deref() {
            if elems.first().unwrap().is_ref() {
                assert!(elems.len() == 1);
                return AccessPath {
                    access_elems: &self.access_elems[..self.access_elems.len() - 1],
                    ..*self
                };
            }
        }
        match (self.access_elems.last().unwrap(), elems.first().unwrap()) {
            (AccessElem::AggTyProj(idx1), AccessElem::AggTyProj(idx2)) => {
                let mut access_elems = self.access_elems[..self.access_elems.len() - 1].to_vec();
                access_elems.push(AccessElem::AggTyProj(ProjectionIdx::from_usize(
                    idx1.index() + idx2.index(),
                )));
                access_elems.extend_from_slice(&elems[1..]);
                AccessPath {
                    access_elems: acx.mk_access_elems(&access_elems),
                    ..*self
                }
            }
            _ => {
                let mut access_elems = self.access_elems.to_vec();
                access_elems.extend_from_slice(elems);
                AccessPath {
                    access_elems: acx.mk_access_elems(&access_elems),
                    ..*self
                }
            }
        }
    }

    pub fn is_valid(&self, _acx: &AnalysisContext<'tcx>) -> bool {
        // No consecutive AggTyProj elements allowed.
        // Ref can only appear at the last position.
        for i in 0..self.access_elems.len().saturating_sub(1) {
            if self.access_elems[i].is_agg_ty_proj() && self.access_elems[i + 1].is_agg_ty_proj() {
                return false;
            }
            if self.access_elems[i] == AccessElem::Ref {
                return false;
            }
        }
        true
    }

    pub fn is_indirect(&self) -> bool {
        self.access_elems.iter().any(|elem| elem.is_deref())
    }

    /// Returns the number of dereference elements in the access path.
    pub fn deref_count(&self) -> usize {
        self.access_elems
            .iter()
            .filter(|elem| elem.is_deref())
            .count()
    }

    /// Returns true if the access path's last access element is a reference.
    /// The reference element should only appear at the end of a valid access path.
    pub fn has_ref_elem(&self) -> bool {
        self.access_elems.last().map_or(false, |elem| elem.is_ref())
    }

    pub fn remove_ref_elem(&self) -> AccessPath<'tcx> {
        if self.has_ref_elem() {
            AccessPath {
                access_elems: &self.access_elems[..self.access_elems.len() - 1],
                ..*self
            }
        } else {
            *self
        }
    }

    /// Check if the base of this access path is a projection of the given place.
    /// A place can only be the form of p.j and (*p).j, where p is a local
    /// and j is list of projection elements except for dereference.
    pub fn is_projection_of(&self, acx: &AnalysisContext<'tcx>, place: &Place<'tcx>) -> bool {
        if self.local != place.local {
            return false;
        }
        let place_ty = type_util::place_ty(acx.tcx,place, self.func_def);
        let max_proj_idx = acx.max_projection_idx_of_type(place_ty);
        let path = AccessPath::from_rustc_place(acx, self.func_def, place);
        if path.access_elems.is_empty() {
            if let Some(AccessElem::AggTyProj(idx)) = self.access_elems.first() {
                return idx.index() <= max_proj_idx.index();
            }
            return true;
        }
        if self.access_elems.len() < path.access_elems.len() {
            return false;
        }
        let mut i = 0;
        if path.access_elems[i].is_deref() {
            if !self.access_elems[i].is_deref() {
                return false;
            }
            i += 1;
        }
        if let Some(AccessElem::AggTyProj(idx1)) = path.access_elems.get(i) {
            if let Some(AccessElem::AggTyProj(idx2)) = self.access_elems.get(i) {
                if idx2.index() >= idx1.index()
                    && idx2.index() <= idx1.index() + max_proj_idx.index()
                {
                    return true;
                }
            }
            return false;
        } else {
            // The path is a dereference place
            assert_eq!(path.access_elems.len(), 1);
            if let Some(AccessElem::AggTyProj(idx)) = self.access_elems.get(1) {
                return idx.index() <= max_proj_idx.index();
            }
            return true;
        }
    }

    /// If this access path is a projection of the given place, return the projection
    /// after the base in the access path. Otherwise, return None.
    pub fn projection_after_base(
        &self,
        acx: &AnalysisContext<'tcx>,
        place: &Place<'tcx>,
    ) -> Option<AccessElems<'tcx>> {
        if !self.is_projection_of(acx, place) {
            return None;
        }
        let path = AccessPath::from_rustc_place(acx, self.func_def, place);
        if path.access_elems.is_empty() {
            return Some(self.access_elems);
        }

        if self.access_elems.len() < path.access_elems.len() {
            return None;
        }

        let mut i = 0;
        if path.access_elems[i].is_deref() {
            if !self.access_elems[i].is_deref() {
                return None;
            }
            i += 1;
        }

        if let Some(AccessElem::AggTyProj(idx1)) = path.access_elems.get(i) {
            if let Some(AccessElem::AggTyProj(idx2)) = self.access_elems.get(i) {
                let place_ty = type_util::place_ty(acx.tcx,place, self.func_def);
                let max_proj_idx = acx.max_projection_idx_of_type(place_ty);
                if idx2.index() >= idx1.index()
                    && idx2.index() <= idx1.index() + max_proj_idx.index()
                {
                    let mut split_proj = vec![AccessElem::AggTyProj(ProjectionIdx::from_usize(
                        idx2.index() - idx1.index(),
                    ))];
                    split_proj.extend_from_slice(&self.access_elems[i + 1..]);
                    return Some(acx.mk_access_elems(&split_proj));
                }
            }
            return None;
        } else {
            // The path is a dereference place
            return Some(&self.access_elems[i..]);
        }
    }

    /// Derive a new access path with the given base.
    /// For example, if the current access path is x.f.g.h, the old base is x.f
    /// and the new base is y.k, then the new access path is y.k.g.h.
    pub fn derive_with_new_base(
        &self,
        acx: &AnalysisContext<'tcx>,
        old_base: &Place<'tcx>,
        new_base: &Place<'tcx>,
    ) -> AccessPath<'tcx> {
        let proj_after_base = self
            .projection_after_base(acx, old_base)
            .expect("access path must be a projection of old_base");
        AccessPath::from_rustc_place_with_elems(acx, self.func_def, new_base, proj_after_base)
    }

    pub fn derive_with_new_base_in_func(
        &self,
        acx: &AnalysisContext<'tcx>,
        old_base: &Place<'tcx>,
        new_base: &Place<'tcx>,
        new_func: FuncDef<'tcx>,
    ) -> AccessPath<'tcx> {
        let proj_after_base = self
            .projection_after_base(acx, old_base)
            .expect("access path must be a projection of old_base");
        AccessPath::from_rustc_place_with_elems(acx, new_func, new_base, proj_after_base)
    }

    /// A given place (e.g., x.f.g) can be indirectly accessed if it or its prefix (x, x.f or x.f.g)
    /// has had its address taken.
    /// Returns a list of prefix places that have had their address taken, along with the location
    /// of the address-taking.
    pub fn get_address_taken_prefixes(
        &self,
        acx: &AnalysisContext<'tcx>,
    ) -> MultiMap<Place<'tcx>, Location> {
        let mut ret = MultiMap::new();
        let mut reference_set = acx.reference_set.borrow_mut();
        for (place, locs) in reference_set
            .get_ref_locations(self.func_def.def_id, acx.tcx)
            .location_map
            .iter_all()
        {
            if self.is_projection_of(acx, place) {
                ret.insert_many(place.clone(), locs.iter().cloned());
            }
        }
        ret
    }

    /// Returns the first dereference base and remaining projection of the access path.
    /// For example, given an access path *(*(*x.f).g).h, the result is (x.f, [Deref, ...]).
    pub fn deref_base_and_proj(&self) -> Option<(AccessPath<'tcx>, AccessElems<'tcx>)> {
        let pos = self.access_elems.iter().position(|e| e.is_deref())?;
        Some((
            AccessPath {
                access_elems: &self.access_elems[..pos],
                alloc_trace: None,
                ..*self
            },
            &self.access_elems[pos..],
        ))
    }

    /// Removes the access elements from the last dereference element to the end.
    /// For example, given an access path *(*(*x.f).g).h, the result is *(*x.f).g.
    pub fn truncate_from_last_deref(&self) -> Option<AccessPath<'tcx>> {
        let pos = self.access_elems.iter().rposition(|e| e.is_deref())?;
        Some(AccessPath {
            access_elems: &self.access_elems[..pos],
            alloc_trace: None,
            ..*self
        })
    }

    pub fn try_to_eval_possible_types(
        &self,
        acx: &AnalysisContext<'tcx>,
    ) -> Option<HashSet<Ty<'tcx>>> {
        if self.has_ref_elem() {
            return None;
        }
        let local_ty = type_util::place_ty(acx.tcx,&Place::from(self.local), self.func_def);
        try_to_eval_possible_types(acx, local_ty, self.access_elems)
    }

    pub fn try_to_eval_possible_pointer_types(
        &self,
        acx: &AnalysisContext<'tcx>,
    ) -> Option<Vec<Ty<'tcx>>> {
        self.try_to_eval_possible_types(acx)
            .map(|tys| tys.iter().filter(|ty| ty.is_any_ptr()).cloned().collect())
    }
}


#[cfg(test)]
mod test {
    use crate::infoflow::data::{access_elem::AccessElem, access_path::AccessPath};
    use crate::mir::function::FuncDef;
    use crate::mir::projection::ProjectionIdx;
    use crate::util::test_util::{compile, get_func, get_place, initialize_analysis_context};
    use crate::util::type_util;
    use crate::analysis_context::AnalysisContext;
    use rustc_middle::ty::TyCtxt;

    fn setup_main<'tcx>(tcx: TyCtxt<'tcx>) -> (AnalysisContext<'tcx>, FuncDef<'tcx>) {
        let acx = initialize_analysis_context(tcx);
        let main_def_id = get_func(tcx, "main").unwrap();
        let main_func_def = FuncDef {
            def_id: main_def_id,
            generic_args: tcx.mk_args(&[]),
        };
        (acx, main_func_def)
    }

    #[test]
    fn test_is_projection_of() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
            }
            pub struct Bar<T> {
                f: T,
            }
            pub fn main() {
                let bar: Bar<Option<i32>> = Bar { f: Some(0) };
                let foo = Foo { f: bar };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let (acx, func_def) = setup_main(tcx);
            let main_body = tcx.optimized_mir(func_def.def_id);

            let foo_place = get_place(tcx, func_def.def_id, "foo").unwrap();
            let bar_place = get_place(tcx, func_def.def_id, "bar").unwrap();
            let foo_ty = type_util::specialize_generic_args(
                tcx,
                foo_place.ty(main_body, tcx).ty,
                tcx.mk_args(&[]),
            );
            let bar_ty = type_util::get_field_type(tcx, foo_ty, 0);
            let option_ty = type_util::get_field_type(tcx, bar_ty, 0);

            // Build nested field places: foo.f, foo.f.f, foo.f.f@Some, foo.f.f@Some.0
            let foo_f = tcx.mk_place_field(foo_place, 0usize.into(), bar_ty);
            let foo_f_f = tcx.mk_place_field(foo_f, 0usize.into(), option_ty);
            let foo_f_f_some = tcx.mk_place_downcast(
                foo_f_f,
                option_ty.ty_adt_def().unwrap(),
                1usize.into(),
            );
            let foo_f_f_some_0 = tcx.mk_place_field(foo_f_f_some, 0usize.into(), tcx.types.i32);

            let path_foo_f = AccessPath::from_rustc_place(&acx, func_def, &foo_f);
            let path_foo_f_f = AccessPath::from_rustc_place(&acx, func_def, &foo_f_f);
            let path_deep = AccessPath::from_rustc_place(&acx, func_def, &foo_f_f_some_0);

            // A local is trivially a projection of itself
            let foo_path = AccessPath::from_rustc_place(&acx, func_def, &foo_place);
            assert!(foo_path.is_projection_of(&acx, &foo_place));

            // Nested fields are projections of their parent local
            assert!(path_foo_f.is_projection_of(&acx, &foo_place));
            assert!(path_foo_f_f.is_projection_of(&acx, &foo_place));
            assert!(path_deep.is_projection_of(&acx, &foo_place));

            // Deeper paths are projections of intermediate field places
            assert!(path_foo_f_f.is_projection_of(&acx, &foo_f));
            assert!(path_deep.is_projection_of(&acx, &foo_f));

            // Not a projection of a different local
            assert!(!path_foo_f.is_projection_of(&acx, &bar_place));
            assert!(!path_deep.is_projection_of(&acx, &bar_place));
        };

        compile(rust_code.to_string(), test_fn);
    }

    #[test]
    fn test_projection_after_base() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
            }
            pub struct Bar<T> {
                g: i32,
                f: T,
            }
            pub fn main() {
                let bar: Bar<Option<i32>> = Bar { g: 2, f: Some(0) };
                let foo = Foo { f: bar };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let (acx, func_def) = setup_main(tcx);
            let main_body = tcx.optimized_mir(func_def.def_id);

            let foo_place = get_place(tcx, func_def.def_id, "foo").unwrap();
            let bar_place = get_place(tcx, func_def.def_id, "bar").unwrap();
            let foo_ty = type_util::specialize_generic_args(
                tcx,
                foo_place.ty(main_body, tcx).ty,
                tcx.mk_args(&[]),
            );
            let bar_ty = type_util::get_field_type(tcx, foo_ty, 0);
            let option_ty = type_util::get_field_type(tcx, bar_ty, 1);

            let foo_f = tcx.mk_place_field(foo_place, 0usize.into(), bar_ty);
            let foo_f_f = tcx.mk_place_field(foo_f, 1usize.into(), option_ty);
            let foo_f_f_some = tcx.mk_place_downcast(
                foo_f_f,
                option_ty.ty_adt_def().unwrap(),
                1usize.into(),
            );
            let foo_f_f_some_0 = tcx.mk_place_field(foo_f_f_some, 0usize.into(), tcx.types.i32);

            let path_foo_f = AccessPath::from_rustc_place(&acx, func_def, &foo_f);
            let path_foo_f_f = AccessPath::from_rustc_place(&acx, func_def, &foo_f_f);
            let path_deep = AccessPath::from_rustc_place(&acx, func_def, &foo_f_f_some_0);

            // Projection after the local base returns the full access elements
            let proj = path_foo_f.projection_after_base(&acx, &foo_place).unwrap();
            assert_eq!(proj, path_foo_f.access_elems);

            let proj = path_foo_f_f.projection_after_base(&acx, &foo_place).unwrap();
            assert_eq!(proj, path_foo_f_f.access_elems);

            let proj = path_deep.projection_after_base(&acx, &foo_place).unwrap();
            assert_eq!(proj, path_deep.access_elems);

            // Extended path with deref: projection after base has correct length
            let extended = path_deep.project_deeper(
                &acx,
                acx.mk_access_elems(&[
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(2)),
                ]),
            );
            let proj = extended.projection_after_base(&acx, &foo_place).unwrap();
            assert_eq!(proj.len(), 3);

            // Not a projection of a different local
            assert!(path_foo_f.projection_after_base(&acx, &bar_place).is_none());
            assert!(path_deep.projection_after_base(&acx, &bar_place).is_none());
        };

        compile(rust_code.to_string(), test_fn);
    }

    #[test]
    fn test_derive_with_new_base() {
        let rust_code = r#"
            pub struct Foo<T> {
                g: i32,
                f: Bar<T>,
            }
            pub struct Bar<T> {
                g: i32,
                f: T,
            }
            pub fn main() {
                let bar: Bar<Option<i32>> = Bar { g: 2, f: Some(0) };
                let foo = Foo { g: 2, f: bar };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let (acx, func_def) = setup_main(tcx);
            let main_body = tcx.optimized_mir(func_def.def_id);

            let foo_place = get_place(tcx, func_def.def_id, "foo").unwrap();
            let bar_place = get_place(tcx, func_def.def_id, "bar").unwrap();
            let foo_ty = type_util::specialize_generic_args(
                tcx,
                foo_place.ty(main_body, tcx).ty,
                tcx.mk_args(&[]),
            );
            let bar_ty = type_util::get_field_type(tcx, foo_ty, 1);
            let foo_f = tcx.mk_place_field(foo_place, 1usize.into(), bar_ty);

            // Build path: foo + [AggTyProj(1), Deref, AggTyProj(2)]
            // Represents foo.f.*.proj2
            let foo_path = AccessPath::from_rustc_place(&acx, func_def, &foo_place);
            let extended = foo_path.project_deeper(
                &acx,
                acx.mk_access_elems(&[
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(1)),
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(2)),
                ]),
            );

            // Derive with new base: foo.f -> bar
            // Projection after foo.f is [Deref, AggTyProj(2)]
            // Result should be bar with [Deref, AggTyProj(2)]
            let derived = extended.derive_with_new_base(&acx, &foo_f, &bar_place);
            assert_eq!(derived.local, bar_place.local);
            assert_eq!(derived.access_elems.len(), 2);
            assert_eq!(derived.access_elems[0], AccessElem::Deref);
            assert_eq!(
                derived.access_elems[1],
                AccessElem::AggTyProj(ProjectionIdx::from_u32(2))
            );

            // Derive from the local itself: foo -> bar preserves all access elements
            let derived_from_root = extended.derive_with_new_base(&acx, &foo_place, &bar_place);
            assert_eq!(derived_from_root.local, bar_place.local);
            assert_eq!(derived_from_root.access_elems.len(), extended.access_elems.len());
        };

        compile(rust_code.to_string(), test_fn);
    }

    #[test]
    fn test_get_address_taken_prefixes() {
        let rust_code = r#"
            pub struct Foo {
                g: i32,
                f: Bar,
            }
            pub struct Bar {
                g: i32,
                f: String,
            }
            pub fn main() {
                let bar = Bar { g: 2, f: "Hello World".to_string() };
                let foo = Foo { g: 2, f: bar };
                let p = &foo;
                let q = &foo.f;
                let r = &foo.f.f;
                let s = &foo.f.g;
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let (acx, func_def) = setup_main(tcx);
            let main_body = tcx.optimized_mir(func_def.def_id);

            let foo_place = get_place(tcx, func_def.def_id, "foo").unwrap();
            let bar_place = get_place(tcx, func_def.def_id, "bar").unwrap();
            let foo_ty = type_util::specialize_generic_args(
                tcx,
                foo_place.ty(main_body, tcx).ty,
                tcx.mk_args(&[]),
            );
            let bar_ty = type_util::get_field_type(tcx, foo_ty, 1);
            let string_ty = type_util::get_field_type(tcx, bar_ty, 1);
            let foo_f = tcx.mk_place_field(foo_place, 1usize.into(), bar_ty);
            let foo_f_f = tcx.mk_place_field(foo_f, 1usize.into(), string_ty);

            // Deeper paths should have more address-taken prefixes
            let path_foo_f_f = AccessPath::from_rustc_place(&acx, func_def, &foo_f_f);
            let path_foo_f = AccessPath::from_rustc_place(&acx, func_def, &foo_f);
            let path_foo = AccessPath::from_rustc_place(&acx, func_def, &foo_place);
            let path_bar = AccessPath::from_rustc_place(&acx, func_def, &bar_place);

            let prefixes_foo_f_f = path_foo_f_f.get_address_taken_prefixes(&acx);
            let prefixes_foo_f = path_foo_f.get_address_taken_prefixes(&acx);
            let prefixes_foo = path_foo.get_address_taken_prefixes(&acx);
            let prefixes_bar = path_bar.get_address_taken_prefixes(&acx);

            assert!(prefixes_foo_f_f.len() >= prefixes_foo_f.len());
            assert!(prefixes_foo_f.len() >= prefixes_foo.len());
            assert!(prefixes_foo.len() >= 1);
            // bar has no address-taken prefixes (no &bar in the code)
            assert!(prefixes_bar.is_empty());
        };

        compile(rust_code.to_string(), test_fn);
    }

    #[test]
    fn test_truncate_and_deref_base() {
        let rust_code = r#"
            pub struct Outer {
                f: Inner,
            }
            pub struct Inner {
                x: i32,
                y: i32,
            }
            pub fn main() {
                let outer = Outer { f: Inner { x: 1, y: 2 } };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let (acx, func_def) = setup_main(tcx);

            let outer_place = get_place(tcx, func_def.def_id, "outer").unwrap();
            let base = AccessPath::from_rustc_place(&acx, func_def, &outer_place);

            // Non-indirect path: both return None
            assert!(base.truncate_from_last_deref().is_none());
            assert!(base.deref_base_and_proj().is_none());

            // AggTyProj only: still no deref
            let field_path = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[AccessElem::AggTyProj(ProjectionIdx::from_u32(0))]),
            );
            assert!(!field_path.is_indirect());
            assert!(field_path.truncate_from_last_deref().is_none());
            assert!(field_path.deref_base_and_proj().is_none());

            // Single deref: [Deref, AggTyProj(1)]
            let single_deref = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(1)),
                ]),
            );
            assert_eq!(single_deref.deref_count(), 1);
            let truncated = single_deref.truncate_from_last_deref().unwrap();
            assert!(truncated.access_elems.is_empty());
            let (deref_base, proj) = single_deref.deref_base_and_proj().unwrap();
            assert!(deref_base.access_elems.is_empty());
            assert_eq!(proj, single_deref.access_elems);

            // Prefix before deref: [AggTyProj(1), Deref, AggTyProj(2)]
            let prefixed = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(1)),
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(2)),
                ]),
            );
            // truncate removes from last deref onward
            let truncated = prefixed.truncate_from_last_deref().unwrap();
            assert_eq!(truncated.access_elems.len(), 1);
            assert_eq!(
                truncated.access_elems[0],
                AccessElem::AggTyProj(ProjectionIdx::from_u32(1))
            );
            // deref_base_and_proj splits at first deref
            let (deref_base, proj) = prefixed.deref_base_and_proj().unwrap();
            assert_eq!(deref_base.access_elems.len(), 1);
            assert_eq!(proj.len(), 2);
            assert_eq!(proj[0], AccessElem::Deref);

            // Multiple derefs: [Deref, AggTyProj(1), Deref, AggTyProj(2)]
            let multi_deref = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(1)),
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(2)),
                ]),
            );
            assert_eq!(multi_deref.deref_count(), 2);
            // truncate_from_last_deref removes from the LAST deref
            let truncated = multi_deref.truncate_from_last_deref().unwrap();
            assert_eq!(truncated.access_elems.len(), 2);
            assert_eq!(truncated.access_elems[0], AccessElem::Deref);
            assert_eq!(
                truncated.access_elems[1],
                AccessElem::AggTyProj(ProjectionIdx::from_u32(1))
            );
            // deref_base_and_proj splits at the FIRST deref
            let (deref_base, proj) = multi_deref.deref_base_and_proj().unwrap();
            assert!(deref_base.access_elems.is_empty());
            assert_eq!(proj.len(), 4);
        };

        compile(rust_code.to_string(), test_fn);
    }

    #[test]
    fn test_ref_elem() {
        let rust_code = r#"
            pub struct Wrapper {
                val: i32,
                data: i64,
            }
            pub fn main() {
                let w = Wrapper { val: 1, data: 42 };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let (acx, func_def) = setup_main(tcx);

            let w_place = get_place(tcx, func_def.def_id, "w").unwrap();
            let base = AccessPath::from_rustc_place(&acx, func_def, &w_place);

            // Base path: no ref
            assert!(!base.has_ref_elem());
            assert_eq!(base.remove_ref_elem().access_elems, base.access_elems);

            // Path with projection only: no ref
            let field_path = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[AccessElem::AggTyProj(ProjectionIdx::from_u32(0))]),
            );
            assert!(!field_path.has_ref_elem());

            // Path with deref: no ref
            let deref_path = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[
                    AccessElem::Deref,
                    AccessElem::AggTyProj(ProjectionIdx::from_u32(1)),
                ]),
            );
            assert!(!deref_path.has_ref_elem());

            // Add Ref at the end
            let ref_path = deref_path.project_deeper(
                &acx,
                acx.mk_access_elems(&[AccessElem::Ref]),
            );
            assert!(ref_path.has_ref_elem());
            assert_eq!(ref_path.access_elems.len(), deref_path.access_elems.len() + 1);

            // remove_ref_elem strips the trailing Ref
            let stripped = ref_path.remove_ref_elem();
            assert!(!stripped.has_ref_elem());
            assert_eq!(stripped.access_elems, deref_path.access_elems);

            // project_deeper with Deref on Ref-ending path: Ref and Deref cancel
            let canceled = ref_path.project_deeper(
                &acx,
                acx.mk_access_elems(&[AccessElem::Deref]),
            );
            assert!(!canceled.has_ref_elem());
            assert_eq!(canceled.access_elems, deref_path.access_elems);

            // project_deeper with Ref on Deref-ending path: Deref and Ref cancel
            let deref_ending = base.project_deeper(
                &acx,
                acx.mk_access_elems(&[AccessElem::Deref]),
            );
            let ref_cancel = deref_ending.project_deeper(
                &acx,
                acx.mk_access_elems(&[AccessElem::Ref]),
            );
            assert!(!ref_cancel.has_ref_elem());
            assert!(ref_cancel.access_elems.is_empty());
        };

        compile(rust_code.to_string(), test_fn);
    }
}
