use log::*;
use smallvec::{smallvec, SmallVec};
use std::collections::HashSet;
use rustc_middle::mir::Place;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::cfg::backward_infoflow_cfg::BackwardInfoflowCFG;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::points_of_aliasing::{self, POAKind};
use crate::infoflow::Unit;

/// Processes the backward return points-of-aliasing.
/// When a backward analysis exits a callee, the outcoming access path may have
/// aliases at the callsite that also need to be tracked. This function finds
/// those aliases and returns path edges for continuing the backward analysis.
///
/// For example, given the following code:
/// ```text
/// 1.  let mut v = Vec::with_capacity(10);
/// 2.  let r = &mut v;
/// 3.  r.push(1);
/// 4.  let p = v.as_ptr();
/// ```
/// To find the flow origins of `p`, we start a backward analysis from line 4,
/// and determine that it flows from the interior pointer of `v` after analyzing
/// `as_ptr()`. Since `r` is a mutable reference to `v`, we also need to include
/// `*r` in the following backward analysis since the flow origin of `v`'s interior
/// pointer can also be modified by `*r`.
pub fn process_backward_return_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    bw_icfg: &BackwardInfoflowCFG<'tcx>,
    curr_query: Query<'tcx>,
    return_edge: PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    callsite: Unit<'tcx>,
    return_site: Unit<'tcx>,
) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
    let outcoming = *return_edge.fact_at_target();

    if bw_icfg.is_exit_node(return_site) {
        return smallvec![return_edge];
    }

    let poa = POAKind::new_backward_return_poa(callsite, return_site, outcoming);
    if let Some(poa_results) = acx.poa_cache.get_poa_results(&poa) {
        return dtargets_to_edges(&return_edge, return_site, poa_results);
    }

    // If the outcoming path contains a reference element, delegate to the
    // indirect reference POA handler.
    if outcoming.has_ref_elem() {
        assert!(outcoming.is_indirect());
        return points_of_aliasing::indirect_reference::process_indirect_reference_poa(
            acx, bw_icfg, curr_query, return_edge, &outcoming, callsite,
        );
    }

    trace!("Process backward return poa for {:?} at {:?}", outcoming, return_site);
    // For non-indirect paths, only address-taken aliases need to be considered.
    if !outcoming.is_indirect() {
        let mut res = points_of_aliasing::address_taken::process_address_taken_poa(acx, &outcoming, callsite);
        res.insert(outcoming);
        acx.poa_cache.add_poa_results(poa, res.clone());
        return dtargets_to_edges(&return_edge, return_site, res);
    }

    // For indirect paths without a reference element, find aliases of the base
    // argument at the callsite and extend them with the remaining projection.
    let arg_path =
        AccessPath::from_rustc_place(acx, callsite.func, &Place::from(outcoming.local));
    let query = Query::new(arg_path, callsite);
    let arg_aliases = aliasing::find_aliases(acx, query);
    let proj = outcoming.access_elems;
    let res = points_of_aliasing::find_aliases_recursively(acx, callsite, arg_aliases, proj);

    trace!("Results of backward return poa for {:?}: {:?}", outcoming, res);
    acx.poa_cache.add_poa_results(poa, res.clone());
    dtargets_to_edges(&return_edge, return_site, res)
}

fn dtargets_to_edges<'tcx>(
    return_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    return_site: Unit<'tcx>,
    dtargets: HashSet<AccessPath<'tcx>>,
) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
    dtargets
        .into_iter()
        .map(|dtarget| {
            PathEdge::new(
                return_edge.get_start(),
                *return_edge.fact_at_source(),
                return_site,
                dtarget,
            )
        })
        .collect()
}
