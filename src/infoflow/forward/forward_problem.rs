use std::cell::{Ref, RefCell, RefMut};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::{
    cfg::{infoflow_cfg::InfoflowCFG, CFGConfig},
    data::access_path::AccessPath,
    forward::forward_path_edge_functions::ForwardPathEdgeFunctions,
    ifds::{
        ifds_tabulation_problem::IFDSTabulationProblem,
        incomings::Incomings,
        path_edge::PathEdge,
        path_edge_functions::PathEdgeFunctions,
        path_edges::{PathEdgeStore, PathEdges},
        summaries::Summaries,
    },
    Direction, Unit,
};
use crate::mir::function::FuncDef;

pub struct ForwardProblem<'analysis, 'cfg, 'tcx, 'bw> {
    pub(crate) icfg: &'cfg InfoflowCFG<'tcx>,
    pub(crate) forward_path_edge_functions: ForwardPathEdgeFunctions<'analysis, 'tcx, 'bw>,
    pub(crate) path_edges: PathEdgeStore<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>,
    pub(crate) incomings: Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>,
    pub(crate) summaries: Rc<RefCell<Summaries<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>>>,
}

impl<'analysis, 'cfg, 'tcx, 'bw> ForwardProblem<'analysis, 'cfg, 'tcx, 'bw>
where
    'analysis: 'cfg,
{
    pub fn new(
        acx: &'analysis AnalysisContext<'tcx>,
    ) -> ForwardProblem<'analysis, 'cfg, 'tcx, 'bw> {
        ForwardProblem {
            icfg: acx.get_fw_icfg(CFGConfig::default()),
            forward_path_edge_functions: ForwardPathEdgeFunctions::new(acx),
            path_edges: PathEdgeStore::new(),
            incomings: Incomings::new(),
            summaries: Rc::clone(&acx.fw_summaries),
        }
    }
}

impl<'analysis, 'cfg, 'tcx, 'bw>
    IFDSTabulationProblem<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>, InfoflowCFG<'tcx>>
    for ForwardProblem<'analysis, 'cfg, 'tcx, 'bw>
{
    fn interprocedural_cfg(&self) -> &InfoflowCFG<'tcx> {
        self.icfg
    }

    /// Seeds are provided via `start_propagation()` on the solver, not through this method.
    fn initial_seeds(&self) -> HashMap<Unit<'tcx>, HashSet<AccessPath<'tcx>>> {
        unreachable!()
    }

    fn path_edge_functions(
        &self,
    ) -> &impl PathEdgeFunctions<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>> {
        &self.forward_path_edge_functions
    }

    fn path_edges(&self) -> &impl PathEdges<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>> {
        &self.path_edges
    }

    fn path_edges_mut(
        &mut self,
    ) -> &mut impl PathEdges<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>> {
        &mut self.path_edges
    }

    fn incomings(&self) -> &Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>> {
        &self.incomings
    }

    fn incomings_mut(&mut self) -> &mut Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>> {
        &mut self.incomings
    }

    fn summaries(&self) -> Ref<Summaries<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>> {
        self.summaries.borrow()
    }

    fn summaries_mut(&self) -> RefMut<Summaries<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>> {
        self.summaries.borrow_mut()
    }

    fn add_flow_edge(
        &mut self, 
        _from_node: (Unit<'tcx>, AccessPath<'tcx>), 
        _to_node: (Unit<'tcx>, AccessPath<'tcx>)
    ) {
    }

    fn on_solver_add_incoming(
        &mut self,
        _callee: FuncDef<'tcx>,
        _pair: &(Unit<'tcx>, AccessPath<'tcx>),
        _path_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) {
    }

    fn get_direction(&self) -> Direction {
        Direction::Forward
    }
}
