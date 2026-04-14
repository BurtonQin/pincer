use multimap::MultiMap;
use std::collections::HashMap;

use crate::infoflow::ifds::path_edge::{PathEdge, PathEdgeData, PathEdgeNode};

pub struct Summaries<N, D, F>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash,
{
    func_to_start_fact: HashMap<F, PerFunctionSummary<N, D>>,
}

impl<N, D, F> Summaries<N, D, F>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub fn new() -> Summaries<N, D, F> {
        Summaries {
            func_to_start_fact: HashMap::new(),
        }
    }

    pub fn add_end_summary(&mut self, func: F, edge: PathEdge<N, D>) {
        if !self.store_as_summary(func, &edge) {
            return;
        }
        let per_func_summary = self.get_or_create(func);
        per_func_summary.add_end_summary(edge);
    }

    pub fn end_summary(&self, func: F, start_node: &(N, D)) -> Option<&Vec<PathEdge<N, D>>> {
        if let Some(per_func_summary) = self.func_to_start_fact.get(&func) {
            per_func_summary.end_summary(start_node)
        } else {
            None
        }
    }

    /// Decides whether an edge should be stored as a summary.
    /// Currently always returns `true`, which over-approximates by storing summaries
    /// for all facts rather than only parameters/return values. This is sound but may
    /// retain more summaries than necessary.
    pub fn store_as_summary(&self, _func: F, _edge: &PathEdge<N, D>) -> bool {
        true
    }

    fn get_or_create(&mut self, func: F) -> &mut PerFunctionSummary<N, D> {
        self.func_to_start_fact.entry(func).or_default()
    }
}

pub struct PerFunctionSummary<N: PathEdgeNode, D: PathEdgeData> {
    start_node_to_summary: MultiMap<(N, D), PathEdge<N, D>>,
}

impl<N: PathEdgeNode, D: PathEdgeData> Default for PerFunctionSummary<N, D> {
    fn default() -> Self {
        Self::new()
    }
}

impl<N: PathEdgeNode, D: PathEdgeData> PerFunctionSummary<N, D> {
    pub fn new() -> PerFunctionSummary<N, D> {
        PerFunctionSummary {
            start_node_to_summary: MultiMap::new(),
        }
    }

    pub fn add_end_summary(&mut self, edge: PathEdge<N, D>) {
        self.start_node_to_summary
            .insert(edge.get_start_node().clone(), edge);
    }

    pub fn end_summary(&self, start_node: &(N, D)) -> Option<&Vec<PathEdge<N, D>>> {
        self.start_node_to_summary.get_vec(start_node)
    }
}
