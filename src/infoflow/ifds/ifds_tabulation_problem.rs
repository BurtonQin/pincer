use std::cell::{Ref, RefMut};
use std::collections::{HashMap, HashSet};

use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::ifds::{
    incomings::Incomings,
    path_edge::{PathEdge, PathEdgeData, PathEdgeNode},
    path_edge_functions::PathEdgeFunctions,
    path_edges::PathEdges,
    summaries::Summaries,
};
use crate::infoflow::Direction;

/// A tabulation problem for solving in an IFDSSolver as described
/// by the Reps, Horwitz, Sagiv 1995 (RHS95) paper.
/// N: The type of nodes in the interprocedural control-flow graph. Typically Unit.
/// D: The type of data-flow facts to be computed by the tabulation problem.
/// F: The type of objects used to represent functions. Typically FuncDef.
/// I: The type of inter-procedural control-flow graph being used.
pub trait IFDSTabulationProblem<N, D, F, I: InterproceduralCFG<N, F>>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash,
{
    /// Returns the interprocedural control-flow graph which this problem is computed over.
    fn interprocedural_cfg(&self) -> &I;

    /// Returns initial seeds to be used for the analysis.
    /// This is a mapping of statements to initial analysis facts.
    fn initial_seeds(&self) -> HashMap<N, HashSet<D>>;

    /// This must be a data-flow fact of type D, but must not
    /// be part of the domain of data-flow facts. Typically this will be a
    /// singleton object of type {@link D} that is used for nothing else.
    /// It must holds that this object does not equals any object
    /// within the domain.
    // fn zero_value(&self) -> D;

    fn path_edge_functions(&self) -> &impl PathEdgeFunctions<N, D, F>;

    fn path_edges(&self) -> &impl PathEdges<N, D, F>;

    fn path_edges_mut(&mut self) -> &mut impl PathEdges<N, D, F>;

    fn incomings(&self) -> &Incomings<N, D, F>;

    fn incomings_mut(&mut self) -> &mut Incomings<N, D, F>;

    fn summaries(&self) -> Ref<Summaries<N, D, F>>;

    fn summaries_mut(&self) -> RefMut<Summaries<N, D, F>>;

    fn register(&mut self, edge: PathEdge<N, D>) {
        self.path_edges_mut().register(edge);
    }

    fn add_flow_edge(&mut self, _from_node: (N, D), _to_node: (N, D)) {}

    fn on_solver_add_incoming(&mut self, _callee: F, _pair: &(N, D), _path_edge: &PathEdge<N, D>) {}

    fn get_direction(&self) -> Direction;
}
