use core::assert_eq;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::forward::forward_solver::ForwardSolver;
use crate::infoflow::ifds::incomings::Incomings;
use crate::infoflow::{AccessPath, FlowOriginKind, PointerFlowOrigin, Unit};
use crate::mir::function::FuncDef;

/// When discovering the origin of a pointer flow, e.g. an allocation site during
/// the backward pass, we reach the point where the dataflow originates.
/// From this origin, we can initiate a forward analysis to track all access
/// paths that start from it, identifying aliases of the queried pointer variable.
pub fn process_flow_origin_poa<'analysis, 'cfg, 'tcx, 'bw>(
    _acx: &AnalysisContext<'tcx>,
    fw_solver: &mut ForwardSolver<'analysis, 'cfg, 'tcx, 'bw>,
    flow_origin: PointerFlowOrigin<'tcx>,
    query_unit: Unit<'tcx>,
    bw_incomings: &'bw Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>,
) where
    'analysis: 'cfg,
{
    match flow_origin.kind {
        FlowOriginKind::Allocation { path, .. } => {
            let start_units = fw_solver.solver.icfg().get_start_points_of(query_unit.func);
            let start_unit = *start_units.first().unwrap();
            fw_solver.start_propagation_along_path(path, start_unit, query_unit, bw_incomings, true);
        }
        FlowOriginKind::Parameter(path) => {
            assert_eq!(path.func_def, query_unit.func);
            let start_units = fw_solver.solver.icfg().get_start_points_of(query_unit.func);
            let start_unit = *start_units.first().unwrap();
            fw_solver.start_propagation_along_path(path, start_unit, query_unit, bw_incomings, false);
        }
        FlowOriginKind::Reference {
            ref_path,
            location: _,
        } => {
            assert_eq!(ref_path.func_def, query_unit.func);
            let start_units = fw_solver.solver.icfg().get_start_points_of(query_unit.func);
            let start_unit = *start_units.first().unwrap();
            fw_solver.start_propagation_along_path(ref_path, start_unit, query_unit, bw_incomings, true);
        }
    }
}
