use log::*;
use std::collections::HashSet;

use rustc_middle::mir::Place;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::backward::backward_solver::BackwardSolver;
use crate::infoflow::Unit;

use super::data::access_path::AccessPath;
use super::forward::forward_solver::ForwardSolver;
use super::{points_of_aliasing, PointerFlowOrigin};

pub mod query;

pub fn find_aliases_at_stmt<'tcx>(
    acx: &AnalysisContext<'tcx>,
    place: Place<'tcx>,
    unit: Unit<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let ap = AccessPath::from_rustc_place(acx, unit.func, &place);
    find_aliases_for_access_path(acx, ap, unit)
}

pub fn find_aliases_for_access_path<'tcx>(
    acx: &AnalysisContext<'tcx>,
    ap: AccessPath<'tcx>,
    unit: Unit<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let query = Query::new(ap, unit);
    find_aliases(acx, query)
}

pub fn find_aliases<'tcx>(
    acx: &AnalysisContext<'tcx>,
    query: Query<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    if acx.has_processed_query(&query) {
        return acx.get_aliases(&query);
    }

    acx.query_cache.add_query(query);

    let mut aliases = HashSet::new();

    debug!("Find aliases for query: {:?}", query);

    let mut backward_solver = BackwardSolver::new(acx);
    backward_solver.start_propagation(query, true);

    let flow_origins = acx.get_flow_origins(&query);
    debug!("Flow origins for {:?}: {:?}", query, flow_origins);

    let mut aliases_solver = ForwardSolver::new(acx);
    for origin in flow_origins {
        points_of_aliasing::flow_origin::process_flow_origin_poa(
            acx,
            &mut aliases_solver,
            origin,
            query.unit,
            &backward_solver.incomings(),
        );
    }

    if let Some(path_edges) = aliases_solver.path_edges_at_stmt(query.unit) {
        for path_edge in path_edges {
            let target = *path_edge.fact_at_target();
            if target.func_def == query.access_path.func_def {
                aliases.insert(target);
            }
        }
    }

    debug!("Aliases of query {:?}: {:?}", query, aliases);
    acx.query_cache.add_aliases(query, &aliases);
    acx.query_cache.mark_query_finished(&query);

    aliases
}

pub fn find_flow_origins<'analysis, 'cfg, 'tcx>(
    acx: &AnalysisContext<'tcx>,
    bw_solver: &mut BackwardSolver<'analysis, 'cfg, 'tcx>,
    query: Query<'tcx>,
) -> HashSet<PointerFlowOrigin<'tcx>>
where
    'analysis: 'cfg,
{
    if acx.has_processed_query(&query) {
        return acx.get_flow_origins(&query);
    }

    bw_solver.start_propagation(query, true);

    acx.get_flow_origins(&query)
}
