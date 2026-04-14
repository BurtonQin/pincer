use log::*;
use std::collections::HashSet;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::{infoflow_cfg::InfoflowCFG, interprocedural_cfg::InterproceduralCFG};
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::forward::forward_problem::ForwardProblem;
use crate::infoflow::ifds::{
    ifds_solver::IFDSSolver, ifds_solver::PropagationType,
    ifds_tabulation_problem::IFDSTabulationProblem, incomings::Incomings, path_edge::PathEdge,
};
use crate::infoflow::Unit;
use crate::mir::function::FuncDef;

pub struct ForwardSolver<'analysis, 'cfg, 'tcx, 'bw> {
    pub acx: &'analysis AnalysisContext<'tcx>,
    pub(crate) solver: IFDSSolver<
        Unit<'tcx>,
        AccessPath<'tcx>,
        FuncDef<'tcx>,
        InfoflowCFG<'tcx>,
        ForwardProblem<'analysis, 'cfg, 'tcx, 'bw>,
    >,
    pub(crate) fw_propagation_count: u64,
}

impl<'analysis, 'cfg, 'tcx, 'bw> ForwardSolver<'analysis, 'cfg, 'tcx, 'bw>
where
    'analysis: 'cfg,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> ForwardSolver<'analysis, 'cfg, 'tcx, 'bw> {
        let forward_problem = ForwardProblem::new(acx);
        ForwardSolver {
            acx,
            solver: IFDSSolver::new(forward_problem),
            fw_propagation_count: 0,
        }
    }

    pub fn start_propagation_along_path(
        &mut self,
        d1: AccessPath<'tcx>,
        start_unit: Unit<'tcx>,
        end_unit: Unit<'tcx>,
        bw_incomings: &'bw Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>,
        skip_start: bool,
    ) {
        self.solver
            .tabulation_problem
            .forward_path_edge_functions
            .with_bw_incomings(bw_incomings);
        self.start_propagation_between_units(d1, start_unit, end_unit, skip_start);
    }

    pub fn start_propagation_between_units(
        &mut self,
        d1: AccessPath<'tcx>,
        start_unit: Unit<'tcx>,
        end_unit: Unit<'tcx>,
        skip_start: bool,
    ) {
        self.solver
            .tabulation_problem
            .forward_path_edge_functions
            .with_active_path(start_unit, end_unit);
        self.start_propagation(d1, start_unit, skip_start);
    }

    /// Starts the propagation at the provided statement (skip_start=false) or its successor
    /// (skip_start=true). Creates the initial path edge and adds it to the solver's worklist.
    pub fn start_propagation(&mut self, d1: AccessPath<'tcx>, start_unit: Unit<'tcx>, skip_start: bool) {
        debug!("Start forward analysis from {:?}@{:?}", d1, start_unit);
        let start_edge = PathEdge::new(start_unit, d1, start_unit, d1);
        if skip_start {
            let icfg = self.solver.tabulation_problem.interprocedural_cfg();
            let succs = icfg.get_succs_of(start_unit);
            for succ in succs {
                let edge = PathEdge::new(start_unit, d1, succ, d1);
                self.solver.propagate(edge, &start_edge, PropagationType::Normal, None);
            }
        } else {
            self.solver.propagate(start_edge.clone(), &start_edge, PropagationType::Normal, None);
        }
        self.await_execution();
    }

    pub fn await_execution(&mut self) {
        while !self.solver.worklist.is_empty() {
            let edge = self.solver.worklist.pop_front().unwrap();
            self.fw_propagation_count += 1;
            self.solver.process_path_edge(&edge);
        }
    }

    pub fn path_edges_at_stmt(
        &self,
        stmt: Unit<'tcx>,
    ) -> Option<&HashSet<PathEdge<Unit<'tcx>, AccessPath<'tcx>>>> {
        self.solver
            .tabulation_problem
            .path_edges
            .path_edges_at_stmt(stmt, stmt.func)
    }
}
