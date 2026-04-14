pub mod address_taken;
pub mod backward_call;
pub mod backward_return;
pub mod flow_origin;
pub mod forward_return;
pub mod indirect_reference;
pub mod load_or_store;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::{
    access_elem::{self, AccessElems},
    access_path::AccessPath,
};
use crate::infoflow::{aliasing, Unit};
use crate::mir::function::FuncDef;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum POAKind<'tcx> {
    AddressTakenPOA {
        unit: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    },
    BackwardCallPOA {
        callee: FuncDef<'tcx>,
        callee_start: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    },
    BackwardReturnPOA {
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    },
    ForwardReturnPOA {
        callsite: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    },
    IndirectReferencePOA {
        unit: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    },
    LoadOrStorePOA {
        unit: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    },
}

impl<'tcx> POAKind<'tcx> {
    pub fn new_address_taken_poa(unit: Unit<'tcx>, dtarget: AccessPath<'tcx>) -> POAKind<'tcx> {
        POAKind::AddressTakenPOA { unit, dtarget }
    }

    pub fn new_backward_call_poa(
        callee: FuncDef<'tcx>,
        callee_start: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    ) -> POAKind<'tcx> {
        POAKind::BackwardCallPOA {
            callee,
            callee_start,
            dtarget,
        }
    }

    pub fn new_backward_return_poa(
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    ) -> POAKind<'tcx> {
        POAKind::BackwardReturnPOA {
            callsite,
            return_site,
            dtarget,
        }
    }

    pub fn new_forward_return_poa(
        callsite: Unit<'tcx>,
        dtarget: AccessPath<'tcx>,
    ) -> POAKind<'tcx> {
        POAKind::ForwardReturnPOA {
            callsite,
            dtarget,
        }
    }

    pub fn new_indirect_reference_poa(unit: Unit<'tcx>, dtarget: AccessPath<'tcx>) -> POAKind<'tcx> {
        POAKind::IndirectReferencePOA { unit, dtarget }
    }

    pub fn new_load_or_store_poa(unit: Unit<'tcx>, dtarget: AccessPath<'tcx>) -> POAKind<'tcx> {
        POAKind::LoadOrStorePOA { unit, dtarget }
    }
}

pub struct POACache<'tcx> {
    pub(crate) cache: RefCell<HashMap<POAKind<'tcx>, HashSet<AccessPath<'tcx>>>>,
}

impl<'tcx> POACache<'tcx> {
    pub fn new() -> POACache<'tcx> {
        POACache {
            cache: RefCell::new(HashMap::new()),
        }
    }

    pub fn add_poa_results(&self, poa: POAKind<'tcx>, results: HashSet<AccessPath<'tcx>>) {
        self.cache.borrow_mut().insert(poa, results);
    }

    pub fn get_poa_results(&self, poa: &POAKind<'tcx>) -> Option<HashSet<AccessPath<'tcx>>> {
        self.cache.borrow().get(&poa).cloned()
    }
}



pub(super) fn find_aliases_recursively<'tcx>(
    acx: &AnalysisContext<'tcx>,
    unit: Unit<'tcx>,
    base_aliases: HashSet<AccessPath<'tcx>>,
    proj: AccessElems<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let mut out = HashSet::new();
    out.extend(base_aliases.iter().map(|ap| ap.project_deeper(acx, &proj)));

    // For each alias of the argument, append the projection to it. If the constructed path
    // involves multiple dereference, recursively search the aliases of the last-deref-base,
    // i.e. given a path `(*(*(*x).f).g).h`, we recursively search the aliases of `(*(*x).f).g`
    let mut change_set = base_aliases;
    let mut left_proj = proj;
    let split_proj = access_elem::split_at_deref(proj);
    for i in 0..split_proj.len() - 1 {
        let with_proj_set: Vec<AccessPath<'tcx>> = change_set
            .iter()
            .map(|ap| ap.project_deeper(acx, &split_proj[i]))
            .collect();
        let prev_aliases = with_proj_set
            .iter()
            .flat_map(|ap| aliasing::find_aliases_for_access_path(acx, *ap, unit));
        left_proj = &left_proj[split_proj[i].len()..];
        if i < split_proj.len() - 2 {
            change_set = HashSet::new();
            for alias in prev_aliases {
                let with_proj = alias.project_deeper(acx, left_proj);
                if out.contains(&with_proj) {
                    continue;
                }
                out.insert(with_proj);
                change_set.insert(alias);
            }
        } else {
            out.extend(prev_aliases.map(|ap| ap.project_deeper(acx, left_proj)));
        }
    }

    // Similar as in Load/Store POA, we need to consider if the target itself has its address taken.
    // TODO: to optimize as in Load/Store POA
    let mut set = HashSet::new();
    for target in &out {
        if target.access_elems.iter().filter(|e| e.is_deref()).count() < 2 {
            set.extend(address_taken::process_address_taken_poa(acx, &target, unit));
        }
    }
    out.extend(set);
    out
}
