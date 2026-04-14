use multimap::MultiMap;
use std::collections::HashMap;

use crate::infoflow::ifds::path_edge::{PathEdge, PathEdgeData, PathEdgeNode};

pub struct Incomings<N, D, F>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash,
{
    function_to_inc: HashMap<F, PerFunctionIncomings<N, D>>,
}

impl<N, D, F> Incomings<N, D, F>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash,
{
    pub fn new() -> Incomings<N, D, F> {
        Incomings {
            function_to_inc: HashMap::new(),
        }
    }

    pub fn incoming(&self, start_node: &(N, D), func: F) -> Option<&Vec<PathEdge<N, D>>> {
        if let Some(per_function) = self.function_to_inc.get(&func) {
            per_function.get_incomings(start_node)
        } else {
            None
        }
    }

    pub fn incoming_of(&self, func: F) -> std::collections::HashSet<PathEdge<N, D>> {
        if let Some(per_function) = self.function_to_inc.get(&func) {
            per_function.start_node_to_inc_edges.iter_all().flat_map(|(_, vec)| vec.clone()).collect()
        } else {
            std::collections::HashSet::new()
        }
    }

    pub fn has_incoming_from(&self, func: F, callsite: N) -> bool {
        if let Some(per_function) = self.function_to_inc.get(&func) {
            per_function
                .start_node_to_inc_edges
                .iter_all()
                .any(|(_, vec)| vec.iter().any(|v| v.get_target() == callsite))
        } else {
            false
        }
    }

    pub fn add_incoming(&mut self, callee: F, pair: (N, D), path_edge: PathEdge<N, D>) -> bool {
        let per_function = self.get_or_create(callee);
        per_function.add_incoming(pair, path_edge)
    }

    fn get_or_create(&mut self, func: F) -> &mut PerFunctionIncomings<N, D> {
        self.function_to_inc.entry(func).or_default()
    }
}

pub struct PerFunctionIncomings<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    start_node_to_inc_edges: MultiMap<(N, D), PathEdge<N, D>>,
}

impl<N, D> Default for PerFunctionIncomings<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    fn default() -> Self {
        PerFunctionIncomings::new()
    }
}

impl<N, D> PerFunctionIncomings<N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub fn new() -> PerFunctionIncomings<N, D> {
        PerFunctionIncomings {
            start_node_to_inc_edges: MultiMap::new(),
        }
    }

    pub fn add_incoming(&mut self, pair: (N, D), path_edge: PathEdge<N, D>) -> bool {
        // Check if the value already exists for the key
        if let Some(values) = self.start_node_to_inc_edges.get_vec(&pair) {
            if values.contains(&path_edge) {
                return false; // The pair already exists
            }
        }
        // Insert the new pair
        self.start_node_to_inc_edges.insert(pair, path_edge);
        true
    }

    pub fn get_incomings(&self, start_node: &(N, D)) -> Option<&Vec<PathEdge<N, D>>> {
        self.start_node_to_inc_edges.get_vec(&start_node)
    }
}
