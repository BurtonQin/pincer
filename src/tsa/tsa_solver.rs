use rustc_middle::ty::TyCtxt;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::CFGQueries;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::ifds_solver::{IFDSSolver, PropagationType};
use crate::infoflow::ifds::ifds_tabulation_problem::IFDSTabulationProblem;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::mir::function::FuncDef;
use crate::tsa::state::TypeState;
use crate::tsa::state_transition::TypeStateTransition;
use crate::tsa::tsa_problem::TypeStateAnalysisProblem;
use crate::tsa::{TSAPathEdgeNode, TSAPathEdgeData};

pub struct TypeStateAnalysisSolver<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    pub(crate) acx: &'analysis AnalysisContext<'tcx>,
    pub(crate) solver: IFDSSolver<
        N,
        TSAPathEdgeData<'tcx, S>,
        FuncDef<'tcx>,
        I,
        TypeStateAnalysisProblem<'analysis, 'cfg, 'tcx, N, I, S, T>,
    >,
    pub(crate) propagation_count: u64,
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    TypeStateAnalysisSolver<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    'analysis: 'cfg,
    N: TSAPathEdgeNode<'tcx> + 'analysis,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState + 'analysis,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>> + 'analysis,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>, icfg: &'cfg I, trans: T) -> Self {
        let tsa_problem = TypeStateAnalysisProblem::new(acx, icfg, trans);
        TypeStateAnalysisSolver {
            acx,
            solver: IFDSSolver::new(tsa_problem),
            propagation_count: 0,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    pub fn tabulation_problem(
        &self,
    ) -> &TypeStateAnalysisProblem<'analysis, 'cfg, 'tcx, N, I, S, T> {
        &self.solver.tabulation_problem
    }

    pub fn start_propagation(
        &mut self,
        initial_seed: (N, TSAPathEdgeData<'tcx, S>),
        skip_start: bool,
    ) {
        let (start_node, state) = initial_seed;
        if skip_start {
            let cfg = self.solver.tabulation_problem.interprocedural_cfg();
            let succs = cfg.get_succs_of(start_node);
            let start_edge = PathEdge::new(start_node, state.clone(), start_node, state.clone());
            for succ in succs {
                let edge = PathEdge::new(start_node, state.clone(), succ, state.clone());
                self.solver.propagate(edge, &start_edge, PropagationType::Normal, None);
            }
        } else {
            let start_edge = PathEdge::new(start_node, state.clone(), start_node, state);
            self.solver
                .propagate(start_edge.clone(), &start_edge, PropagationType::Normal, None);
        }

        self.await_execution();
    }

    fn await_execution(&mut self) {
        while !self.solver.worklist.is_empty() {
            let edge = self.solver.worklist.pop_front().unwrap();
            self.propagation_count += 1;
            self.solver.process_path_edge(&edge);
        }
    }
}
