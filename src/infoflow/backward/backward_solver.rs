use log::*;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::backward::backward_problem::BackwardProblem;
use crate::infoflow::aliasing::query::QueryList;
use crate::infoflow::cfg::{
    backward_infoflow_cfg::BackwardInfoflowCFG, interprocedural_cfg::InterproceduralCFG,
};
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::{
    ifds_solver::IFDSSolver, ifds_solver::PropagationType,
    ifds_tabulation_problem::IFDSTabulationProblem, incomings::Incomings, path_edge::PathEdge,
};
use crate::infoflow::{points_of_aliasing, Unit};
use crate::mir::function::FuncDef;

pub struct BackwardSolver<'analysis, 'cfg, 'tcx> {
    pub acx: &'analysis AnalysisContext<'tcx>,
    pub(crate) solver: IFDSSolver<
        Unit<'tcx>,
        AccessPath<'tcx>,
        FuncDef<'tcx>,
        BackwardInfoflowCFG<'tcx>,
        BackwardProblem<'analysis, 'cfg, 'tcx>,
    >,
    pub queries: QueryList<'tcx>,
    pub(crate) bw_propagation_count: u64,
}

impl<'analysis, 'cfg, 'tcx> BackwardSolver<'analysis, 'cfg, 'tcx>
where
    'analysis: 'cfg,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> BackwardSolver<'analysis, 'cfg, 'tcx> {
        let queries = QueryList::new();
        let backward_problem = BackwardProblem::new(acx, queries.clone());
        BackwardSolver {
            acx,
            queries,
            solver: IFDSSolver::new(backward_problem),
            bw_propagation_count: 0,
        }
    }

    pub fn start_propagation(&mut self, query: Query<'tcx>, skip_start: bool) {
        self.queries.add_query(query);
        let (d1, stmt) = (query.access_path, query.unit);
        let start_edge = PathEdge::new(stmt, d1, stmt, d1);
        debug!("Start backward analysis from {:?}@{:?}", d1, stmt);

        // If the queried pointer has its address taken
        let aliases =
            points_of_aliasing::address_taken::process_address_taken_poa(self.acx, &d1, stmt);

        if skip_start {
            let icfg = self.solver.tabulation_problem.interprocedural_cfg();
            let succs = icfg.get_succs_of(stmt);
            for succ in succs {
                let edge = PathEdge::new(stmt, d1, succ, d1);
                self.solver.propagate(edge, &start_edge, PropagationType::Normal, None);

                for alias in &aliases {
                    let edge = PathEdge::new(stmt, d1, succ, alias.clone());
                    self.solver.propagate(edge, &start_edge, PropagationType::Normal, None);
                }
            }
        } else {
            self.solver.propagate(start_edge.clone(), &start_edge, PropagationType::Normal, None);
            for alias in &aliases {
                let alias_edge = PathEdge::new(stmt, d1, stmt, alias.clone());
                self.solver.propagate(alias_edge, &start_edge, PropagationType::Normal, None);
            }
        }

        self.await_execution();

        // Finish the query
        self.queries.pop();
    }

    pub fn await_execution(&mut self) {
        while !self.solver.worklist.is_empty() {
            let edge = self.solver.worklist.pop_front().unwrap();
            self.bw_propagation_count += 1;
            self.solver.process_path_edge(&edge);
        }
    }

    pub fn incomings(&self) -> &Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>> {
        &self.solver.tabulation_problem.incomings
    }

    pub fn curr_query(&self) -> Query<'tcx> {
        self.queries.curr_query()
    }
}
