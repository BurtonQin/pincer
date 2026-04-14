use std::collections::HashSet;
use log::*;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::data::access_elem::AccessElems;
use crate::infoflow::forward::forward_solver::ForwardSolver;
use crate::infoflow::points_of_aliasing::POAKind;
use crate::infoflow::{aliasing, points_of_aliasing, AccessPath, Unit};
use crate::mir::function::FuncDef;

/// Helps process the call points-of-aliasing in backward analysis.
pub fn process_backward_call_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    callee: FuncDef<'tcx>,
    callee_sp: Unit<'tcx>,
    fact_at_start: &AccessPath<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let poa = POAKind::new_backward_call_poa(callee, callee_sp, fact_at_start.clone());
    if let Some(poa_results) = acx.poa_cache.get_poa_results(&poa) {
        return poa_results;
    }

    trace!("Process backward call poa for {:?} at {:?}", fact_at_start, callee_sp);
    let base_ptr_and_proj = |ap: &AccessPath<'tcx>| {
        let deref_idx = ap.access_elems.iter().position(|elem| elem.is_deref()).unwrap();
        let base_ptr = AccessPath::new(ap.func_def, ap.local, &ap.access_elems[..deref_idx]);
        let proj = &ap.access_elems[deref_idx..];
        (base_ptr, proj)
    };

    let res = if fact_at_start.is_from_ret() {
        if !fact_at_start.is_indirect() {
            // CHECKME: The return value may have its address taken
            let mut set = HashSet::new();
            set.insert(*fact_at_start);
            set.extend(
                points_of_aliasing::address_taken::process_address_taken_poa(
                    acx,
                    fact_at_start,
                    callee_sp,
                ),
            );
            return set;
        }
        let (base_ptr, proj) = base_ptr_and_proj(fact_at_start);
        handle_backward_call_ret_poa(acx, callee_sp, base_ptr, proj)
    } else if fact_at_start.is_from_param(acx.tcx) {
        assert!(fact_at_start.is_indirect());
        let (base_ptr, proj) = base_ptr_and_proj(fact_at_start);
        handle_backward_call_arg_poa(acx, callee, callee_sp, base_ptr, proj)
    } else {
        unreachable!(
            "The fact at start of the call should be a projection 
            of either a return value or an argument"
        );
    };

    trace!("Results of backward call poa for {:?}: {:?}", fact_at_start, res);
    acx.poa_cache.add_poa_results(poa, res.clone());
    res
}

fn handle_backward_call_ret_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    callee_sp: Unit<'tcx>,
    ret_path: AccessPath<'tcx>,
    proj: AccessElems<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    assert!(!proj.is_empty());
    let ret_aliases = aliasing::find_aliases_for_access_path(acx, ret_path, callee_sp);
    points_of_aliasing::find_aliases_recursively(acx, callee_sp, ret_aliases, proj)
}

fn handle_backward_call_arg_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    callee: FuncDef<'tcx>,
    callee_sp: Unit<'tcx>,
    arg_path: AccessPath<'tcx>,
    proj: AccessElems<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    // Start a forward analysis from the callee's entry point for the local place
    // associated with the fact.
    // Since the local place may be reassigned within the callee, we must identify
    // pointers that retain the same points-to information as the original local
    // place at the callee's return site.
    // Then we start backward analysis from the paths that project from these pointers.
    let arg_aliases = argument_aliases_at_end_point(acx, callee, callee_sp, arg_path);
    points_of_aliasing::find_aliases_recursively(acx, callee_sp, arg_aliases, proj)
}

fn argument_aliases_at_end_point<'tcx>(
    acx: &AnalysisContext<'tcx>,
    func: FuncDef<'tcx>,
    end_point: Unit<'tcx>,
    arg_path: AccessPath<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let mut forward_solver = ForwardSolver::new(acx);
    let start_point = forward_solver.solver.tabulation_problem.icfg.get_start_points_of(func)[0];
    if start_point == end_point {
        let mut res = HashSet::new();
        res.insert(arg_path);
        return res;
    }
    let start_node = (start_point, arg_path);
    let mut arg_aliases = HashSet::new();
    if forward_solver
        .solver
        .end_summary(func, &start_node)
        .is_none()
    {
        forward_solver.start_propagation(arg_path, start_point, false);
    }
    let summary_edges = forward_solver
        .solver
        .end_summary(func, &start_node)
        .unwrap();
    for summary_edge in summary_edges {
        if summary_edge.get_target() == end_point {
            arg_aliases.insert(*summary_edge.fact_at_target());
        }
    }

    arg_aliases
}
