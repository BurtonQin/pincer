use std::collections::hash_map::Entry;
use std::collections::HashMap;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::cell::RefCell;
use std::rc::Rc;

use petgraph::graph::{DefaultIx, EdgeIndex, NodeIndex};
use petgraph::visit::EdgeRef;
use petgraph::Graph;

use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::ifds::path_edge::{PathEdgeData, PathEdgeNode};
use crate::infoflow::ifds::summaries::Summaries;

// Unique identifiers for call graph nodes and edges.
pub type FGNodeId = NodeIndex<DefaultIx>;
pub type FGEdgeId = EdgeIndex<DefaultIx>;

/// A flow graph with nodes of data facts (N, D) in a IFDS analysis.
pub struct FlowGraph<'icfg, N, D, F, I>
where
    I: InterproceduralCFG<N, F>,
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::hash::Hash + std::cmp::Eq,
{
    pub icfg: &'icfg I,
    pub graph: Graph<(N, D), ()>,
    pub node_map: HashMap<(N, D), FGNodeId>,
    summaries: Rc<RefCell<Summaries<N, D, F>>>,
    phantom: PhantomData<F>,
}

impl<'icfg, N, D, F, I> FlowGraph<'icfg, N, D, F, I>
where
    N: PathEdgeNode + std::fmt::Debug,
    D: PathEdgeData + std::fmt::Debug,
    I: InterproceduralCFG<N, F>,
    F: std::hash::Hash + std::cmp::Eq + Copy,
{
    pub fn new(icfg: &'icfg I, summaries: Rc<RefCell<Summaries<N, D, F>>>) -> Self {
        FlowGraph {
            icfg,
            graph: Graph::new(),
            node_map: HashMap::new(),
            summaries,
            phantom: PhantomData,
        }
    }

    /// Add a new node to the flow graph if it does not exist.
    /// Return the node id corresponding to the node.
    pub fn add_node(&mut self, node: (N, D)) -> FGNodeId {
        match self.node_map.entry(node.clone()) {
            Entry::Occupied(o) => o.get().to_owned(),
            Entry::Vacant(v) => {
                let node_id = self.graph.add_node(node);
                *v.insert(node_id)
            }
        }
    }

    pub fn get_node_id(&self, node: &(N, D)) -> Option<FGNodeId> {
        self.node_map.get(node).cloned()
    }

    pub fn add_edge(&mut self, from_node: (N, D), to_node: (N, D)) -> FGEdgeId {
        let from_node_id = self.add_node(from_node);
        let to_node_id = self.add_node(to_node);
        self.graph.update_edge(from_node_id, to_node_id, ())
    }

    pub fn find_flow_path_between(
        &self,
        from_node: &(N, D),
        to_node: &(N, D),
    ) -> Option<Vec<&(N, D)>> {
        let from_node_id = self.get_node_id(from_node)?;
        let to_node_id = self.get_node_id(to_node)?;

        // Keep track of visited nodes to avoid cycles
        let mut visited = HashSet::new();
        // Single call stack for the current path
        let mut call_stack = Vec::new();
        // Current path being explored
        let mut current_path = Vec::new();

        if self.dfs(
            &self.graph,
            from_node_id,
            to_node_id,
            &mut visited,
            &mut call_stack,
            &mut current_path,
        ) {
            current_path.push(to_node_id);
            Some(
                current_path
                    .iter()
                    .map(|&id| self.graph.node_weight(id).unwrap())
                    .collect(),
            )
        } else {
            None
        }
    }

    fn dfs(
        &self,
        graph: &Graph<(N, D), ()>,
        current: FGNodeId,
        target: FGNodeId,
        visited: &mut HashSet<FGNodeId>,
        call_stack: &mut Vec<FGNodeId>,
        current_path: &mut Vec<FGNodeId>,
    ) -> bool {
        if current == target {
            return true;
        }

        current_path.push(current);

        for edge in graph.edges(current) {
            let next = edge.target();
            let current_data = graph.node_weight(current).unwrap();
            let next_data = graph.node_weight(next).unwrap();

            if self.is_return_flow(current_data, next_data) {
                // For return flows, validate against call stack
                if call_stack.is_empty()
                    || !self.is_valid_return(
                        &graph.node_weight(*call_stack.last().unwrap()).unwrap(),
                        next_data,
                    )
                {
                    continue;
                }
                // Pop the call site from stack
                let call_site = call_stack.pop().unwrap();
                if self.dfs(graph, next, target, visited, call_stack, current_path) {
                    return true;
                }
                // Restore call site to stack on backtrack
                call_stack.push(call_site);
            } else if self.is_call_flow(current_data, next_data) {
                // For call flows, push current node to stack
                call_stack.push(current);
                if self.dfs(graph, next, target, visited, call_stack, current_path) {
                    return true;
                }
                // Pop the call site from stack on backtrack
                call_stack.pop();
            } else {
                // For normal flows, just continue DFS
                if self.dfs(graph, next, target, visited, call_stack, current_path) {
                    return true;
                }
            }
        }

        current_path.pop();
        visited.remove(&current);
        false
    }

    // Helper functions for DFS
    pub fn is_call_flow(&self, from_node: &(N, D), to_node: &(N, D)) -> bool {
        if !self.icfg.is_call_node(from_node.0) {
            return false;
        }
        self.icfg.get_function_of(from_node.0) != self.icfg.get_function_of(to_node.0)
    }

    pub fn is_return_flow(&self, from_node: &(N, D), to_node: &(N, D)) -> bool {
        if !self.icfg.is_exit_node(from_node.0) {
            return false;
        }
        self.icfg.get_function_of(from_node.0) != self.icfg.get_function_of(to_node.0)
    }

    pub fn is_valid_return(&self, call_node: &(N, D), return_node: &(N, D)) -> bool {
        self.icfg
            .get_return_sites_of_call_at(call_node.0)
            .contains(&return_node.0)
    }

    pub fn is_call_to_return_flow(&self, from_node: &(N, D), to_node: &(N, D)) -> bool {
        if !self.icfg.is_call_node(from_node.0) {
            return false;
        }
        self.icfg.get_function_of(from_node.0) == self.icfg.get_function_of(to_node.0)
    }

    pub fn is_normal_flow(&self, from_node: &(N, D), to_node: &(N, D)) -> bool {
        if self.icfg.is_call_node(from_node.0) {
            return false;
        }
        !self.is_return_flow(from_node, to_node)
    }

    pub fn end_summary_targets(&self, func: F, start_node: &(N, D)) -> Option<Vec<(N, D)>> {
        let summaries = self.summaries.borrow();
        summaries.end_summary(func, start_node).map(|edges| {
            edges
                .iter()
                .map(|edge| edge.get_target_node().clone())
                .collect()
        })
    }
}

impl<'icfg, N, D, F, I> FlowGraph<'icfg, N, D, F, I>
where
    N: PathEdgeNode + std::fmt::Debug,
    D: PathEdgeData + std::fmt::Debug,
    I: InterproceduralCFG<N, F>,
    F: std::hash::Hash + std::cmp::Eq + Copy,
{
    pub fn find_intraprocedural_flow_paths_from(&self, from_node: (N, D)) -> HashSet<Vec<(N, D)>> {
        let mut visited = HashSet::new();
        self.find_intraprocedural_flow_paths_from_(from_node, &mut visited)
    }

    pub fn find_intraprocedural_flow_paths_from_(&self, from_node: (N, D), visited: &mut HashSet<(N, D)>) -> HashSet<Vec<(N, D)>> {
        let mut paths = HashSet::new();
        // Avoid infinite recursions.
        if visited.contains(&from_node) {
            let path = vec![from_node.clone()];
            paths.insert(path);
            return paths;
        }
        visited.insert(from_node.clone());

        // If the node has no edges, it is a terminal node.
        let from_node_id = self.get_node_id(&from_node).unwrap();
        if self.graph.edges(from_node_id).count() == 0 {
            let path = vec![from_node.clone()];
            paths.insert(path);
            return paths;
        }

        for edge in self.graph.edges(from_node_id) {
            let next = edge.target();
            let next_data = self.graph.node_weight(next).unwrap();
            if self.is_return_flow(&from_node, next_data) {
                let path = vec![from_node.clone()];
                paths.insert(path);
            } else if self.is_call_flow(&from_node, next_data) {
                if let Some(end_summary_targets) =
                    self.end_summary_targets(self.icfg.get_function_of(next_data.0), next_data)
                {
                    for summary_node in end_summary_targets {
                        let summary_node_id = self.get_node_id(&summary_node).unwrap();
                        for return_edge in self.graph.edges(summary_node_id) {
                            let return_node_id = return_edge.target();
                            let return_node = self.graph.node_weight(return_node_id).unwrap();
                            if self.is_return_flow(&summary_node, return_node)
                                && self.is_valid_return(&from_node, return_node)
                            {
                                let follow_paths =
                                    self.find_intraprocedural_flow_paths_from_(return_node.clone(), visited);
                                for mut follow_path in follow_paths {
                                    follow_path.insert(0, from_node.clone());
                                    paths.insert(follow_path);
                                }
                            }
                        }
                    }
                } else {
                    let path = vec![from_node.clone()];
                    paths.insert(path);
                }
            } else {
                let follow_paths = self.find_intraprocedural_flow_paths_from_(next_data.clone(), visited);
                for mut follow_path in follow_paths {
                    follow_path.insert(0, from_node.clone());
                    paths.insert(follow_path);
                }
            }
        }
        paths
    }
    
}
