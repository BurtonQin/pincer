use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::RwLock;
use std::cmp::Ordering;

use rustc_index::IndexVec;
use rustc_middle::mir;
use rustc_middle::mir::PlaceElem;
use rustc_middle::ty::{List, Ty, TyCtxt, TyKind};

pub type PlaceElems<'tcx> = &'tcx List<PlaceElem<'tcx>>;
use crate::util::interners::SliceInterner;
use crate::util::type_util::is_zst;
use crate::util::type_util::{self, field_ty};

rustc_index::newtype_index! {
    pub struct ProjectionIdx {}
}

impl PartialOrd for ProjectionIdx {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.index().cmp(&other.index()))
    }
}

impl std::ops::Sub<usize> for ProjectionIdx {
    type Output = Self;

    #[inline]
    fn sub(self, other: usize) -> Self {
        Self::from_usize(self.index() + other)
    }
}

/// A subset of the PlaceElem enum, primarily about accessing fields, indices, or variants
/// of aggregate types, including structs, unions, enums, arrays, slices, and tuples.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug, Ord, PartialOrd)]
pub enum AggTyElem {
    /// Select the struct/union field with the given index.
    Field(usize),

    /// Index/ConstantIndex into a slice/array
    Index,

    /// "Downcast" to a variant of an ADT. Currently, MIR only introduces
    /// this for ADTs with more than one variant. The value is the ordinal of the variant.
    Downcast(usize),
}

pub type AggTyElems = Vec<AggTyElem>;

pub struct ProjectionIndexer<'tcx> {
    pub(crate) projections_cache: RwLock<HashMap<Ty<'tcx>, ProjectionIdxMap<'tcx>>>,
    pub(crate) max_projection_indices: RwLock<HashMap<Ty<'tcx>, ProjectionIdx>>,
}

impl<'tcx> Default for ProjectionIndexer<'tcx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'tcx> ProjectionIndexer<'tcx> {
    pub fn new() -> Self {
        Self {
            projections_cache: RwLock::new(HashMap::new()),
            max_projection_indices: RwLock::new(HashMap::new()),
        }
    }

    pub fn get_projection_idx(
        &self,
        tcx: TyCtxt<'tcx>,
        base_ty: Ty<'tcx>,
        projection: PlaceElems<'tcx>,
    ) -> Option<ProjectionIdx> {
        if self
            .projections_cache
            .read()
            .unwrap()
            .get(&base_ty)
            .is_none()
        {
            self.compute_projection_indices(tcx, base_ty);
        }

        let read_guard = self.projections_cache.read().unwrap();
        let proj_idx_map: &ProjectionIdxMap = read_guard.get(&base_ty).unwrap();

        let aggr_ty_elems = projection
            .iter()
            .filter_map(|elem| match elem {
                mir::PlaceElem::Field(idx, _ty) => Some(AggTyElem::Field(idx.into())),
                mir::PlaceElem::Index(_) | mir::PlaceElem::ConstantIndex { .. } => {
                    Some(AggTyElem::Index)
                }
                mir::PlaceElem::Downcast(_name, index) => Some(AggTyElem::Downcast(index.into())),
                mir::PlaceElem::Deref
                | mir::PlaceElem::Subslice { .. }
                | mir::PlaceElem::OpaqueCast(_)
                | mir::PlaceElem::Subtype(_) => None,
            })
            .collect::<AggTyElems>();

        proj_idx_map.proj_to_idx.get(&aggr_ty_elems).copied()
    }

    pub fn compute_projection_indices(&self, tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) {
        let compute_subprojection_indices =
            |field_ty: Ty<'tcx>,
             start_proj_idx: ProjectionIdx,
             pre_elems: AggTyElems,
             proj_idx_map: &mut ProjectionIdxMap<'tcx>| {
                if self
                    .projections_cache
                    .read()
                    .unwrap()
                    .get(&field_ty)
                    .is_none()
                {
                    // recursively compute the projection indices for the field type
                    self.compute_projection_indices(tcx, field_ty);
                }
                let read_guard = self.projections_cache.read().unwrap();
                let subfld_projs = read_guard.get(&field_ty).unwrap();
                let mut subfld_proj_idx = start_proj_idx;
                subfld_projs.proj_to_idx.iter().for_each(|(proj, idx)| {
                    let subfld_ty = subfld_projs.proj_ty.get(proj).unwrap().clone();
                    let mut subfld_proj = pre_elems.clone();
                    subfld_proj.extend_from_slice(&proj);
                    subfld_proj_idx = start_proj_idx + (*idx).into();
                    proj_idx_map.add(subfld_proj, subfld_ty, subfld_proj_idx);
                });
                subfld_proj_idx
            };

        let mut proj_idx = ProjectionIdx::from(0usize);
        let mut proj_idx_map = ProjectionIdxMap::new();
        // Add an empty projection
        proj_idx_map.add(vec![], ty, proj_idx);
        match ty.kind() {
            TyKind::Adt(adt_def, args) if adt_def.is_struct() => {
                // For simplicity, we consider the layout of structs aligns with
                // their defination. We index the fields by their orders.
                // To improve the soundness, we need to analyze the struct layout.
                let variant = adt_def
                    .variants()
                    .iter()
                    .next()
                    .expect("at least one variant");
                for (field_idx, field_def) in variant.fields.iter_enumerated() {
                    // Add the current field into proj_idx_map
                    let field = AggTyElem::Field(field_idx.into());
                    let field_ty = field_ty(tcx, field_def, args);
                    proj_idx_map.add(vec![field], field_ty, proj_idx);

                    // Construct subfields' projections and compute their indices
                    let last_proj_idx = compute_subprojection_indices(
                        field_ty,
                        proj_idx,
                        vec![field],
                        &mut proj_idx_map,
                    );
                    // If current field is zero-sized, the next field will
                    // share the same idx with current field
                    if !type_util::is_zst(tcx, field_ty) || last_proj_idx != proj_idx {
                        proj_idx = last_proj_idx + 1;
                    }
                }
            }
            TyKind::Adt(adt_def, args) if adt_def.is_union() => {
                // We simply assign ProjectionIdx(0) to each union field.
                // To handle unions more soundly, we need to compute the offset for each field and subfield.
                let variant = adt_def
                    .variants()
                    .iter()
                    .next()
                    .expect("at least one variant");
                for (field_idx, field_def) in variant.fields.iter_enumerated() {
                    // Add the current field into proj_idx_map
                    let field = AggTyElem::Field(field_idx.into());
                    let field_ty = field_ty(tcx, field_def, args);
                    proj_idx_map.add(vec![field], field_ty, proj_idx);

                    // Construct subfields' projections and compute their indices
                    compute_subprojection_indices(
                        field_ty,
                        proj_idx,
                        vec![field],
                        &mut proj_idx_map,
                    );
                }
            }
            TyKind::Adt(adt_def, args) if adt_def.is_enum() => {
                // For enums, we iterate over all variants and process their fields.
                proj_idx = proj_idx + 1usize.into();
                for (variant_idx, variant) in adt_def.variants().iter_enumerated() {
                    let downcast = AggTyElem::Downcast(variant_idx.into());
                    let downcast_ty = type_util::get_downcast_type(tcx, ty, variant_idx);
                    proj_idx_map.add(vec![downcast], downcast_ty, proj_idx);
                    for (field_idx, field_def) in variant.fields.iter_enumerated() {
                        // Add the current field into proj_idx_map
                        let field = AggTyElem::Field(field_idx.into());
                        let field_ty = field_ty(tcx, field_def, args);
                        proj_idx_map.add(vec![downcast, field], field_ty, proj_idx);

                        // Construct subfields' projections and compute their indices
                        let last_proj_idx = compute_subprojection_indices(
                            field_ty,
                            proj_idx,
                            vec![downcast, field],
                            &mut proj_idx_map,
                        );

                        if !type_util::is_zst(tcx, field_ty)
                            || last_proj_idx != proj_idx
                            || field_idx == variant.fields.last_index().unwrap()
                        {
                            proj_idx = last_proj_idx + 1;
                        }
                    }
                }
            }
            TyKind::Array(elem_ty, _) | TyKind::Slice(elem_ty) => {
                let index = AggTyElem::Index;
                proj_idx_map.add(vec![index], *elem_ty, proj_idx);
                compute_subprojection_indices(*elem_ty, proj_idx, vec![index], &mut proj_idx_map);
            }
            TyKind::Tuple(tuple_types) => {
                // Similar to structs
                tuple_types.iter().enumerate().for_each(|(i, field_ty)| {
                    // Add the current field into proj_idx_map
                    let field = AggTyElem::Field(i);
                    proj_idx_map.add(vec![field], field_ty, proj_idx);

                    // Construct subfields' projections and compute their indices
                    let last_proj_idx = compute_subprojection_indices(
                        field_ty,
                        proj_idx,
                        vec![field],
                        &mut proj_idx_map,
                    );

                    if !type_util::is_zst(tcx, field_ty) || last_proj_idx != proj_idx {
                        proj_idx = last_proj_idx + 1;
                    }
                });
            }
            TyKind::Closure(..) | TyKind::Coroutine(..) => {
                let closure_field_types = type_util::closure_field_types(ty);
                closure_field_types
                    .iter()
                    .enumerate()
                    .for_each(|(i, &field_ty)| {
                        // Add the current field into proj_idx_map
                        let field = AggTyElem::Field(i);
                        proj_idx_map.add(vec![field], field_ty, proj_idx);

                        // Construct subfields' projections and compute their indices
                        let last_proj_idx = compute_subprojection_indices(
                            field_ty,
                            proj_idx,
                            vec![field],
                            &mut proj_idx_map,
                        );

                        if !type_util::is_zst(tcx, field_ty) || last_proj_idx != proj_idx {
                            proj_idx = last_proj_idx + 1;
                        }
                    });
            }

            _ => {}
        }

        self.projections_cache
            .write()
            .unwrap()
            .insert(ty, proj_idx_map);
    }

    pub fn get_possible_types_of_projection(
        &self,
        tcx: TyCtxt<'tcx>,
        base_ty: Ty<'tcx>,
        projection_idx: ProjectionIdx,
    ) -> Option<HashSet<Ty<'tcx>>> {
        if self
            .projections_cache
            .read()
            .unwrap()
            .get(&base_ty)
            .is_none()
        {
            self.compute_projection_indices(tcx, base_ty);
        }

        let read_guard = self.projections_cache.read().unwrap();
        let proj_idx_map: &ProjectionIdxMap = read_guard.get(&base_ty).unwrap();

        proj_idx_map.get_types_of_proj_idx(projection_idx)
    }

    pub fn max_projection_idx_of_type(
        &self,
        tcx: TyCtxt<'tcx>,
        base_ty: Ty<'tcx>,
    ) -> ProjectionIdx {
        if let Some(max_idx) = self.max_projection_indices.read().unwrap().get(&base_ty) {
            return *max_idx;
        }

        if self
            .projections_cache
            .read()
            .unwrap()
            .get(&base_ty)
            .is_none()
        {
            self.compute_projection_indices(tcx, base_ty);
        }

        let read_guard = self.projections_cache.read().unwrap();
        let proj_idx_map: &ProjectionIdxMap = read_guard.get(&base_ty).unwrap();
        let max_idx = proj_idx_map
            .proj_to_idx
            .iter()
            .max_by_key(|&(_, v)| v.as_usize())
            .unwrap()
            .1;
        self.max_projection_indices
            .write()
            .unwrap()
            .entry(base_ty)
            .or_insert(*max_idx);
        *max_idx
    }
}

pub(crate) struct ProjectionIdxMap<'tcx> {
    pub(crate) proj_ty: BTreeMap<AggTyElems, Ty<'tcx>>,
    pub(crate) proj_to_idx: BTreeMap<AggTyElems, ProjectionIdx>,
    pub(crate) idx_to_proj: IndexVec<ProjectionIdx, Vec<AggTyElems>>,
}

impl<'tcx> Default for ProjectionIdxMap<'tcx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'tcx> ProjectionIdxMap<'tcx> {
    pub fn new() -> Self {
        Self {
            proj_ty: BTreeMap::new(),
            proj_to_idx: BTreeMap::new(),
            idx_to_proj: IndexVec::new(),
        }
    }

    pub fn add(&mut self, proj: AggTyElems, ty: Ty<'tcx>, idx: ProjectionIdx) {
        self.proj_ty.insert(proj.clone(), ty);
        self.proj_to_idx.insert(proj.clone(), idx);
        self.idx_to_proj
            .ensure_contains_elem(idx, Vec::default)
            .push(proj);
    }

    pub fn get_types_of_proj_idx(&self, idx: ProjectionIdx) -> Option<HashSet<Ty<'tcx>>> {
        self.idx_to_proj.get(idx).map(|projs| {
            projs.iter().map(|proj| self.proj_ty.get(proj).unwrap().clone()).collect()
        })
    }
}

pub type PlaceElemsAndTy<'tcx> = (PlaceElems<'tcx>, Ty<'tcx>);

pub struct ZeroByteOffsetProjectionsCache<'tcx> {
    pub(crate) place_elems_interner: SliceInterner<'tcx, PlaceElemsAndTy<'tcx>>,
    pub(crate) zero_byte_offset_projs_cache:
        RwLock<HashMap<Ty<'tcx>, &'tcx [PlaceElemsAndTy<'tcx>]>>,
}

impl<'tcx> Default for ZeroByteOffsetProjectionsCache<'tcx> {
    fn default() -> Self {
        Self::new()
    }
}

impl<'tcx> ZeroByteOffsetProjectionsCache<'tcx> {
    pub fn new() -> ZeroByteOffsetProjectionsCache<'tcx> {
        ZeroByteOffsetProjectionsCache {
            place_elems_interner: SliceInterner::new(),
            zero_byte_offset_projs_cache: RwLock::new(HashMap::default()),
        }
    }

    pub fn get_zero_byte_offset_projections(
        &self,
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
    ) -> &'tcx [PlaceElemsAndTy<'tcx>] {
        if let Some(projs) = self.zero_byte_offset_projs_cache.read().unwrap().get(&ty) {
            return projs;
        }
        let projs = self.compute_zero_byte_offset_projections(tcx, ty);
        let projs_slice = self.place_elems_interner.intern(tcx, projs.as_slice());
        self.zero_byte_offset_projs_cache
            .write()
            .unwrap()
            .insert(ty, projs_slice);
        projs_slice
    }

    pub fn compute_zero_byte_offset_projections(
        &self,
        tcx: TyCtxt<'tcx>,
        ty: Ty<'tcx>,
    ) -> Vec<PlaceElemsAndTy<'tcx>> {
        let mut projs = Vec::new();
        match ty.kind() {
            TyKind::Adt(adt_def, args) if adt_def.is_union() => {
                let variant = adt_def
                    .variants()
                    .iter()
                    .next()
                    .expect("at least one variant");
                for (field_idx, field_def) in variant.fields.iter_enumerated() {
                    let field_ty = field_ty(tcx, field_def, args);
                    let place_elem = PlaceElem::Field(field_idx, field_ty);
                    let field_proj = tcx.mk_place_elems(&[place_elem]);
                    projs.push((field_proj, field_ty));

                    // Recursively compute the zero byte offset projections of the field type.
                    let subfld_projs = self.get_zero_byte_offset_projections(tcx, field_ty);
                    for (subfld_proj, subfld_ty) in subfld_projs {
                        let full_proj = concat_place_elems(tcx, field_proj, subfld_proj);
                        projs.push((full_proj, *subfld_ty));
                    }
                }
            }
            TyKind::Adt(adt_def, args) if adt_def.is_struct() => {
                let variant = adt_def
                    .variants()
                    .iter()
                    .next()
                    .expect("at least one variant");
                // For simplicity, we consider the first field of the struct as its zero-byte-offset field.
                // When the first field is a zero-sized type, we add the second field into the result list.
                // To improve the soundness, we need to analyze the struct layout.
                for (field_idx, field_def) in variant.fields.iter_enumerated() {
                    let field_ty = field_ty(tcx, field_def, args);
                    let place_elem = PlaceElem::Field(field_idx, field_ty);
                    let field_proj = tcx.mk_place_elems(&[place_elem]);
                    projs.push((field_proj, field_ty));

                    if !is_zst(tcx, field_ty) {
                        // Recursively compute the zero byte offset projections of the field type.
                        let subfld_projs = self.get_zero_byte_offset_projections(tcx, field_ty);
                        for (subfld_proj, subfld_ty) in subfld_projs {
                            let full_proj = concat_place_elems(tcx, field_proj, subfld_proj);
                            projs.push((full_proj, *subfld_ty));
                        }
                        break;
                    }
                }
            }
            TyKind::Array(elem_ty, _) | TyKind::Slice(elem_ty) => {
                let place_elem = PlaceElem::ConstantIndex {
                    offset: 0,
                    min_length: 1,
                    from_end: false,
                };
                let field_proj = tcx.mk_place_elems(&[place_elem]);
                projs.push((field_proj, *elem_ty));

                let subfld_projs = self.get_zero_byte_offset_projections(tcx, *elem_ty);
                for (subfld_proj, subfld_ty) in subfld_projs {
                    let full_proj = concat_place_elems(tcx, field_proj, subfld_proj);
                    projs.push((full_proj, *subfld_ty));
                }
            }
            TyKind::Tuple(types) => {
                for (field_idx, field_ty) in types.iter().enumerate() {
                    let place_elem = PlaceElem::Field(field_idx.into(), field_ty);
                    let field_proj = tcx.mk_place_elems(&[place_elem]);
                    projs.push((field_proj, field_ty));

                    // Same as a struct, the first field can be a zero-sized type.
                    if !is_zst(tcx, field_ty) {
                        let subfld_projs = self.get_zero_byte_offset_projections(tcx, field_ty);
                        for (subfld_proj, subfld_ty) in subfld_projs {
                            let full_proj = concat_place_elems(tcx, field_proj, subfld_proj);
                            projs.push((full_proj, *subfld_ty));
                        }
                    }
                }
            }
            _ => {}
        }
        projs
    }
}

pub fn concat_place_elems<'tcx>(
    tcx: TyCtxt<'tcx>,
    first_elems: PlaceElems<'tcx>,
    second_elems: PlaceElems<'tcx>,
) -> PlaceElems<'tcx> {
    let new_elems = first_elems
        .iter()
        .chain(second_elems.iter())
        .collect::<Vec<_>>();
    tcx.mk_place_elems(&new_elems)
}

#[cfg(test)]
mod test {
    use core::assert_eq;

    use crate::mir::projection::{AggTyElem, ProjectionIdx, ProjectionIndexer};
    use crate::util::test_util::{compile, get_func, get_place};

    use rustc_middle::ty::TyCtxt;

    #[test]
    fn test_struct_projs() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
                g: Vec<T>,
            }
            pub struct Bar<T> {
                f: T,
            }
            pub fn main() {
                let bar: Bar<i32> = Bar { f: 0 };
                let foo: Foo<i32> = Foo { f: bar, g: vec![] };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let main_def_id = get_func(tcx, "main").unwrap();
            let main_body = tcx.optimized_mir(main_def_id);
            let foo_place = get_place(tcx, main_def_id, "foo").unwrap();
            let foo_ty = foo_place.ty(main_body, tcx).ty;
            let proj_indexer = ProjectionIndexer::new();
            proj_indexer.compute_projection_indices(tcx, foo_ty);
            let read_guard = proj_indexer.projections_cache.read().unwrap();
            let foo_proj_idx_map = read_guard.get(&foo_ty).unwrap();
            assert_eq!(
                foo_proj_idx_map
                    .proj_to_idx
                    .get(&vec![AggTyElem::Field(0), AggTyElem::Field(0)]),
                Some(&ProjectionIdx::from(0usize))
            );

            assert_eq!(
                foo_proj_idx_map.proj_to_idx.get(&vec![
                    AggTyElem::Field(1),
                    AggTyElem::Field(0),
                    AggTyElem::Field(0),
                    AggTyElem::Field(1)
                ]),
                Some(&ProjectionIdx::from(3usize))
            );
        };

        compile(rust_code.to_string(), test_fn);
    }

    #[test]
    fn test_max_proj_idx() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
                g: Vec<T>,
            }
            pub struct Bar<T> {
                f: T,
            }
            pub fn main() {
                let bar: Bar<i32> = Bar { f: 0 };
                let foo: Foo<i32> = Foo { f: bar, g: vec![] };
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let main_def_id = get_func(tcx, "main").unwrap();
            let main_body = tcx.optimized_mir(main_def_id);
            let foo_place = get_place(tcx, main_def_id, "foo").unwrap();
            let foo_ty = foo_place.ty(main_body, tcx).ty;
            let bar_place = get_place(tcx, main_def_id, "bar").unwrap();
            let bar_ty = bar_place.ty(main_body, tcx).ty;
            let proj_indexer = ProjectionIndexer::new();
            let foo_max_proj_idx = proj_indexer.max_projection_idx_of_type(tcx, foo_ty);
            assert_eq!(foo_max_proj_idx, ProjectionIdx::from(6usize));
            let bar_max_proj_idx = proj_indexer.max_projection_idx_of_type(tcx, bar_ty);
            assert_eq!(bar_max_proj_idx, ProjectionIdx::from(0usize));
        };

        compile(rust_code.to_string(), test_fn);
    }
}


