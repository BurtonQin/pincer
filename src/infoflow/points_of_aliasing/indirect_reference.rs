use log::*;
use smallvec::SmallVec;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::backward::backward_solver::BackwardSolver;
use crate::infoflow::cfg::backward_infoflow_cfg::BackwardInfoflowCFG;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::{aliasing, AccessPath, FlowOriginKind, Unit};

/// Helps process the indirect reference points-of-aliasing.
/// It is called only when the queried pointer is found to point to an indirect
/// accessed place.
/// For example, we are searching for aliases of `q` and we have `q = &(*p).f`.
/// We need to start a backward analysis for the base pointer `p` and
/// for each flow origin of `p`, we append the projection `f` after the origin
/// to obtain the flow origin of `q`.
/// The case can be more complex when we reach a indirect reference site at
/// a different function, like a function transitively called from the start
/// function of the query. In this case, if the base pointer `p` of the indirect
/// reference site `&(*p).f` originates from a paramater of its declaring function,
/// we need to further handle it when exiting this function.
pub fn process_indirect_reference_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    bw_icfg: &BackwardInfoflowCFG<'tcx>,
    curr_query: Query<'tcx>,
    curr_edge: PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    indirect_ref_path: &AccessPath<'tcx>,
    indirect_ref_unit: Unit<'tcx>,
) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
    trace!("processing indirect_ref_path: {:?} at {:?}", indirect_ref_path, indirect_ref_unit);
    assert!(
        indirect_ref_path.access_elems.len() > 1
            && indirect_ref_path.has_ref_elem()
    );

    // TODO: the indirect reference poa may be introduced after a backward function call.
    // Therefore the indirect reference path may be a path involving multiple dereferences.
    // For example
    // ```
    // let p = foo(q);
    // fn foo(q) {
    //     let r = *(q.f);
    //     return &(*r).g;
    // }
    // ```
    // In this case, we will add a indirect reference poa edge like `p -> &(*(*(q.f))).g`.
    // We need to handle this case.
    let (ap, proj_after_base) = indirect_ref_path.deref_base_and_proj().unwrap();
    let query = Query::new(ap, indirect_ref_unit);

    trace!("finding flow origins for base pointer {:?}", ap);
    let mut bw_solver = BackwardSolver::new(acx);
    let base_pointer_origins = aliasing::find_flow_origins(acx, &mut bw_solver, query);
    trace!("origins of base pointer {:?}: {:?}", ap, base_pointer_origins);

    let func = indirect_ref_unit.func;
    let end_point = bw_icfg.get_end_points_of(func)[0];
    let query_started_inside = is_in_query_origin_function(&curr_query, &curr_edge);

    let mut out = SmallVec::new();
    for origin in base_pointer_origins {
        let projected_path = match origin.kind {
            FlowOriginKind::Reference { ref_path, .. } => {
                let projected = ref_path.project_deeper(acx, proj_after_base);
                if !query_started_inside {
                    error!("curr_edge: {:?}", curr_edge);
                    error!(
                        "The queried pointer {:?}@{:?} may point to a local variable {:?} in another function {:?}",
                        curr_query.access_path,
                        curr_query.unit,
                        projected.remove_ref_elem(),
                        projected.func_def
                    );
                    continue;
                }
                trace!("Add flow origin: {:?}", origin);
                projected
            }
            FlowOriginKind::Allocation { path, .. } => {
                path.project_deeper(acx, proj_after_base)
            }
            FlowOriginKind::Parameter(path) => {
                path.project_deeper(acx, proj_after_base)
            }
        };
        out.push(PathEdge::new(
            curr_edge.get_start(),
            *curr_edge.fact_at_source(),
            end_point,
            projected_path,
        ));
    }
    out
}

fn is_in_query_origin_function<'tcx>(
    query: &Query<'tcx>,
    edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
) -> bool {
    query.unit.func == edge.fact_at_target().func_def
        && query.access_path == *edge.fact_at_source()
}
