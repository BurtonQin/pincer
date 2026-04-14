use crate::infoflow::ifds::path_edge::{PathEdge, PathEdgeData, PathEdgeNode};
use crate::mir::ContainingFunction;
use std::collections::{HashMap, HashSet};

pub trait PathEdges<N, D, F> {
    fn has_already_processed(&self, edge: &PathEdge<N, D>) -> bool;
    fn register(&mut self, edge: PathEdge<N, D>);
}

pub struct PathEdgeStore<N, D, F>
where
    F: std::cmp::Eq + std::hash::Hash,
    N: PathEdgeNode,
    D: PathEdgeData,
{
    stmt_to_path_edges: HashMap<F, PerFunctionPathEdges<N, D>>,
}

impl<N, D, F> Default for PathEdgeStore<N, D, F>
where
    F: std::cmp::Eq + std::hash::Hash,
    N: PathEdgeNode,
    D: PathEdgeData,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<N, D, F> PathEdgeStore<N, D, F>
where
    F: std::cmp::Eq + std::hash::Hash,
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub fn new() -> PathEdgeStore<N, D, F> {
        PathEdgeStore {
            stmt_to_path_edges: HashMap::new(),
        }
    }

    pub fn get_or_create(&mut self, func: F) -> &mut PerFunctionPathEdges<N, D> {
        self.stmt_to_path_edges.entry(func).or_default()
    }

    pub fn path_edges_at_stmt(&self, stmt: N, func: F) -> Option<&HashSet<PathEdge<N, D>>> {
        self.stmt_to_path_edges
            .get(&func)
            .and_then(|per_func_path_edges| {
                per_func_path_edges
                    .stmt_to_path_edges
                    .get(&stmt)
                    .map(|per_stmt_path_edges| per_stmt_path_edges.get_path_edges())
            })
    }
}

impl<N, D, F> PathEdges<N, D, F> for PathEdgeStore<N, D, F>
where
    F: std::cmp::Eq + std::hash::Hash,
    N: PathEdgeNode + ContainingFunction<F>,
    D: PathEdgeData,
{
    fn has_already_processed(&self, edge: &PathEdge<N, D>) -> bool {
        let target = edge.get_target();
        let func = target.containing_function();
        if let Some(per_func_path_edges) = self.stmt_to_path_edges.get(&func) {
            per_func_path_edges.has_already_processed(&edge)
        } else {
            false
        }
    }

    fn register(&mut self, edge: PathEdge<N, D>) {
        let target = edge.get_target();
        let func = target.containing_function();
        let per_func_path_edges = self.get_or_create(func);
        per_func_path_edges.register(edge);
    }
}

#[derive(Debug)]
pub struct PerFunctionPathEdges<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub(crate) stmt_to_path_edges: HashMap<N, PerStatementPathEdges<N, D>>,
}

impl<N, D> Default for PerFunctionPathEdges<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<N, D> PerFunctionPathEdges<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub fn new() -> PerFunctionPathEdges<N, D> {
        PerFunctionPathEdges {
            stmt_to_path_edges: HashMap::new(),
        }
    }

    pub fn has_already_processed(&self, edge: &PathEdge<N, D>) -> bool {
        if let Some(per_stmt_path_edges) = self.stmt_to_path_edges.get(&edge.get_target()) {
            per_stmt_path_edges.has_already_processed(edge)
        } else {
            false
        }
    }

    pub fn register(&mut self, edge: PathEdge<N, D>) {
        let per_stmt_path_edges = self.get_or_create(edge.get_target());
        per_stmt_path_edges.register(edge);
    }

    pub fn get_or_create(&mut self, stmt: N) -> &mut PerStatementPathEdges<N, D> {
        self.stmt_to_path_edges.entry(stmt).or_default()
    }
}

#[derive(Debug)]
pub struct PerStatementPathEdges<N, D> {
    pub(crate) processed_path_edges: HashSet<PathEdge<N, D>>,
}

impl<N, D> Default for PerStatementPathEdges<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<N, D> PerStatementPathEdges<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub fn new() -> PerStatementPathEdges<N, D> {
        PerStatementPathEdges {
            processed_path_edges: HashSet::new(),
        }
    }

    pub fn has_already_processed(&self, edge: &PathEdge<N, D>) -> bool {
        self.processed_path_edges.contains(edge)
    }

    pub fn register(&mut self, edge: PathEdge<N, D>) {
        self.processed_path_edges.insert(edge);
    }

    pub fn get_path_edges(&self) -> &HashSet<PathEdge<N, D>> {
        &self.processed_path_edges
    }
}
