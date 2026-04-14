use std::fmt::{Debug, Formatter, Result};
use std::collections::HashSet;

use rustc_middle::ty::Ty;

use crate::infoflow::AnalysisContext;
use crate::mir::projection::ProjectionIdx;
use crate::util::type_util;

pub type AccessElems<'tcx> = &'tcx [AccessElem];

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub enum AccessElem {
    /// Given a path that denotes a reference, select the thing the reference points to.
    Deref,

    /// Take the address of an abstract object.
    Ref,

    /// Accessing fields, indices, or variants of aggregate types,
    /// represented by a ProjectionIdx
    AggTyProj(ProjectionIdx),
}

impl Debug for AccessElem {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        match self {
            AccessElem::Deref => f.write_str("<*>"),
            AccessElem::Ref => f.write_str("<&>"),
            AccessElem::AggTyProj(idx) => f.write_fmt(format_args!("proj_{}", idx.as_usize())),
        }
    }
}

impl AccessElem {
    pub fn is_deref(&self) -> bool {
        match self {
            AccessElem::Deref => true,
            _ => false,
        }
    }

    pub fn is_ref(&self) -> bool {
        match self {
            AccessElem::Ref => true,
            _ => false,
        }
    }

    pub fn is_agg_ty_proj(&self) -> bool {
        match self {
            AccessElem::AggTyProj(_) => true,
            _ => false,
        }
    }
}

/// Normalize the access elements.
/// Remove the consecutive deref and ref elems:
/// *(&x) -> x
pub fn normalize_access_elems(access_elems: &mut Vec<AccessElem>) {
    let mut i = 0;
    while i < access_elems.len() {
        if i + 1 < access_elems.len() {
            match (access_elems[i], access_elems[i + 1]) {
                (AccessElem::Ref, AccessElem::Deref) => {
                    access_elems.remove(i);
                    access_elems.remove(i);
                    continue;
                }
                _ => {}
            }
        }
        i += 1;
    }
}

pub fn split_at_deref<'tcx>(access_elems: AccessElems<'tcx>) -> Vec<AccessElems<'tcx>> {
    let mut result = Vec::new();
    let mut prev_idx = 0;

    for i in 0..access_elems.len() {
        if matches!(access_elems[i], AccessElem::Deref) {
            if prev_idx != i {
                result.push(&access_elems[prev_idx..i]);
                prev_idx = i
            }
        }
    }
    result.push(&access_elems[prev_idx..]);
    result
}

pub fn try_to_eval_possible_types<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
    access_elems: AccessElems<'tcx>,
) -> Option<HashSet<Ty<'tcx>>> {
    if access_elems.len() == 0 {
        return acx.get_possible_types_of_projection(base_ty, ProjectionIdx::from_usize(0));
    }
    match access_elems[0] {
        AccessElem::Deref => {
            if !base_ty.is_any_ptr() {
                return None;
            }
            let deref_ty = type_util::get_dereferenced_type(base_ty);
            acx.get_possible_types_of_projection(deref_ty, ProjectionIdx::from_usize(0))
                .map(|tys| {
                    tys.iter()
                        .filter_map(|ty| try_to_eval_possible_types(acx, *ty, &access_elems[1..]))
                        .flatten()
                        .collect::<HashSet<Ty<'tcx>>>()
                })
            // try_to_eval_possible_types(acx, deref_ty, &access_elems[1..])
        }
        AccessElem::AggTyProj(idx) => {
            acx.get_possible_types_of_projection(base_ty, idx)
                .map(|tys| {
                    tys.iter()
                        .filter_map(|ty| try_to_eval_possible_types(acx, *ty, &access_elems[1..]))
                        .flatten()
                        .collect::<HashSet<Ty<'tcx>>>()
                })
        }
        _ => None,
    }
}

pub fn try_to_eval_possible_pointer_types<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
    access_elems: AccessElems<'tcx>,
) -> Option<HashSet<Ty<'tcx>>> {
    let possible_tys = try_to_eval_possible_types(acx, base_ty, access_elems);
    possible_tys.map(|tys| {
        tys.iter().filter(|ty| ty.is_any_ptr()).cloned().collect()
    })
}