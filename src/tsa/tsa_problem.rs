use std::cell::{Ref, RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::CFGQueries;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::{
    flow_graph::FlowGraph,
    ifds_tabulation_problem::IFDSTabulationProblem,
    incomings::Incomings,
    path_edge::PathEdge,
    path_edge_functions::PathEdgeFunctions,
    path_edges::{PathEdgeStore, PathEdges},
    summaries::Summaries,
};
use crate::infoflow::Direction;
use crate::mir::function::FuncDef;
use crate::tsa::state::TypeState;
use crate::tsa::state_transition::TypeStateTransition;
use crate::tsa::tsa_path_edge_functions::TypeStateAnalysisPathEdgeFunctions;
use crate::tsa::{TSAPathEdgeNode, TSAPathEdgeData};

pub struct TypeStateAnalysisProblem<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    pub(crate) icfg: &'cfg I,
    pub(crate) tsa_path_edge_functions:
        TypeStateAnalysisPathEdgeFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>,
    pub(crate) path_edges:
        PathEdgeStore<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>>,
    pub(crate) incomings:
        Incomings<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>>,
    pub(crate) summaries:
        Rc<RefCell<Summaries<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>>>>,
    pub(crate) flow_graph: FlowGraph<
        'cfg,
        N,
        TSAPathEdgeData<'tcx, S>,
        FuncDef<'tcx>,
        I,
    >,
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    TypeStateAnalysisProblem<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    'analysis: 'cfg,
    N: TSAPathEdgeNode<'tcx> + 'analysis,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState + 'analysis,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>> + 'analysis,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>, icfg: &'cfg I, trans: T) -> Self {
        let summaries = Rc::new(RefCell::new(Summaries::new()));
        TypeStateAnalysisProblem {
            icfg,
            tsa_path_edge_functions: TypeStateAnalysisPathEdgeFunctions::new(acx, icfg, trans),
            path_edges: PathEdgeStore::new(),
            incomings: Incomings::new(),
            summaries: Rc::clone(&summaries),
            flow_graph: FlowGraph::new(icfg, summaries),
        }
    }

    pub fn flow_graph(&self) -> &FlowGraph<
        'cfg,
        N,
        TSAPathEdgeData<'tcx, S>,
        FuncDef<'tcx>,
        I,
    > {
        &self.flow_graph
    }
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    IFDSTabulationProblem<
        N,
        TSAPathEdgeData<'tcx, S>,
        FuncDef<'tcx>,
        I,
    > for TypeStateAnalysisProblem<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    fn interprocedural_cfg(&self) -> &I {
        self.icfg
    }

    /// Returns initial seeds to be used for the analysis.
    /// This is a mapping of statements to initial analysis facts.
    fn initial_seeds(
        &self,
    ) -> HashMap<N, HashSet<TSAPathEdgeData<'tcx, S>>> {
        todo!()
    }

    fn path_edge_functions(
        &self,
    ) -> &impl PathEdgeFunctions<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>>
    {
        &self.tsa_path_edge_functions
    }

    fn path_edges(
        &self,
    ) -> &impl PathEdges<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>> {
        &self.path_edges
    }

    fn path_edges_mut(
        &mut self,
    ) -> &mut impl PathEdges<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>> {
        &mut self.path_edges
    }

    fn incomings(
        &self,
    ) -> &Incomings<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>> {
        &self.incomings
    }

    fn incomings_mut(
        &mut self,
    ) -> &mut Incomings<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>> {
        &mut self.incomings
    }

    fn summaries(
        &self,
    ) -> Ref<Summaries<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>>>
    {
        self.summaries.borrow()
    }

    fn summaries_mut(
        &self,
    ) -> RefMut<Summaries<N, TSAPathEdgeData<'tcx, S>, FuncDef<'tcx>>>
    {
        self.summaries.borrow_mut()
    }

    fn add_flow_edge(
        &mut self,
        from_node: (N, TSAPathEdgeData<'tcx, S>),
        to_node: (N, TSAPathEdgeData<'tcx, S>),
    ) {
        self.flow_graph.add_edge(from_node, to_node);
    }

    fn on_solver_add_incoming(
        &mut self,
        _callee: FuncDef<'tcx>,
        _pair: &(N, TSAPathEdgeData<'tcx, S>),
        _path_edge: &PathEdge<N, TSAPathEdgeData<'tcx, S>>,
    ) {
    }

    fn get_direction(&self) -> Direction {
        Direction::Forward
    }
}
