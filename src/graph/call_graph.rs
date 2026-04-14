// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use petgraph::graph::{DefaultIx, EdgeIndex, NodeIndex};
use petgraph::Graph;
use smallvec::SmallVec;
use std::collections::hash_map::Entry;
use std::collections::{HashMap, HashSet};
use std::fmt::{self, Debug};
use std::hash::Hash;

use crate::mir::unit::BaseUnit;
use crate::mir::function::FuncDef;
use crate::util::chunked_queue::{self, ChunkedQueue};
use crate::util::dot::Dot;

// Unique identifiers for call graph nodes and edges.
pub type CGNodeId = NodeIndex<DefaultIx>;
pub type CGEdgeId = EdgeIndex<DefaultIx>;

pub type CallSite<'tcx> = BaseUnit<FuncDef<'tcx>>;

pub trait CGNodeValue: Copy + Clone + PartialEq + Eq + Hash + Debug {
    fn dot_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result;
}

pub trait CGEdgeValue: Copy + Clone + PartialEq + Eq + Hash + Debug {
    fn dot_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result;
}

impl<'tcx> CGNodeValue for FuncDef<'tcx> {
    fn dot_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{}", self.to_string()))
    }
}


impl<F> CGEdgeValue for BaseUnit<F> where 
    F: Copy + PartialEq + Eq + Hash + Debug 
{
    fn dot_fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_fmt(format_args!("{:?}", self.location))
    }
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
/// The type of a call graph edge.
pub enum CallType {
    // Calls resolved via static dispatch, including static Fn* trait calls.
    StaticDispatch,
    // Calls resolved via dynamic dispatch, excluding dynamic Fn* trait calls.
    DynamicDispatch,
    // Fn* trait calls resolved via dynamic dispatch.
    DynamicFnTrait,
    // function pointer calls.
    FnPtr,
}

#[derive(Clone)]
pub struct CallGraph<N: CGNodeValue, E: CGEdgeValue> {
    /// The graph structure capturing call relationships.
    pub graph: Graph<N, E>,
    /// A map from functions to their corresponding call graph nodes.
    pub func_to_node_id: HashMap<N, CGNodeId>,
    /// A map from call sites to call graph edges.
    pub callsite_to_edges: HashMap<E, HashSet<CGEdgeId>>,
    /// A map from functions to their corresponding callsites.
    pub func_to_callsites: HashMap<N, SmallVec<[E; 2]>>,  
    /// A queue of reachable nodes.
    pub(crate) reachable_funcs: ChunkedQueue<N>,
}

impl<N: CGNodeValue, E: CGEdgeValue> CallGraph<N, E> {
    pub fn new() -> Self {
        CallGraph {
            graph: Graph::<N, E>::new(),
            func_to_node_id: HashMap::new(),
            callsite_to_edges: HashMap::new(),
            func_to_callsites: HashMap::new(),
            reachable_funcs: ChunkedQueue::new(),
        }
    }

    /// Add a new function to the call graph.
    pub fn add_func(&mut self, func: N) {
        if let Entry::Vacant(e) = self.func_to_node_id.entry(func) {
            let node_id = self.graph.add_node(func);
            e.insert(node_id);
            self.add_reachable_func(func);
        }
    }

    /// Helper function to get a node or insert a new
    /// node if it does not exist in the map.
    fn get_or_insert_node(&mut self, func: N) -> CGNodeId {
        match self.func_to_node_id.entry(func) {
            Entry::Occupied(o) => o.get().to_owned(),
            Entry::Vacant(v) => {
                // Add the def_id to the reachable functions queue.
                self.reachable_funcs.push(func);
                let node_id = self.graph.add_node(func);
                *v.insert(node_id)
            }
        }
    }

    /// Add the def_id into the reachable functions queue.
    fn add_reachable_func(&mut self, func: N) {
        self.reachable_funcs.push(func);
    }

    pub fn get_callee_id_of_edge(&self, edge_id: EdgeIndex) -> Option<N> {
        let (_, callee_node) = self.edge_endpoints(edge_id)?;
        self.graph.node_weight(callee_node).copied()
    }

    pub fn edge_endpoints(&self, edge_id: EdgeIndex) -> Option<(CGNodeId, CGNodeId)> {
        self.graph.edge_endpoints(edge_id)
    }

    /// Get the set of callees for a callsite.
    pub fn get_callees<B: FromIterator<N>>(&self, callsite: &E) -> B {
        if let Some(edges) = self.callsite_to_edges.get(callsite) {
            edges
                .iter()
                .filter_map(|edge_id| match self.graph.edge_endpoints(*edge_id) {
                    Some((_, target)) => Some(*self.graph.node_weight(target).unwrap()),
                    None => None,
                })
                .collect::<B>()
        } else {
            B::from_iter(std::iter::empty())
        }
    }

    /// Get the set of callsites for a callee.
    pub fn get_callers(&self, func: &N) -> Option<&SmallVec<[E; 2]>> {
        self.func_to_callsites.get(&func)
    }

    /// Returns true if an edge to the callee already exists for the callsite.
    pub fn has_edge(&self, callsite: &E, callee_id: N) -> bool {
        self.callsite_to_edges.get(callsite).map_or(false, |edges| {
            edges.iter().any(|edge_id| {
                self.graph.edge_endpoints(*edge_id)
                    .and_then(|(_, target)| self.graph.node_weight(target).copied())
                    == Some(callee_id)
            })
        })
    }

    /// Adds a new edge to the call graph.
    /// The edge is a call from `caller_id` to `callee_id` at `callsite`.
    /// Returns false if the edge already existed, and true otherwise.
    pub fn add_edge(&mut self, callsite: E, caller_id: N, callee_id: N) -> bool {
        let caller_node = self.get_or_insert_node(caller_id);
        let callee_node = self.get_or_insert_node(callee_id);

        if self.has_edge(&callsite, callee_id) {
            return false;
        }

        let edge_id = self.graph.add_edge(caller_node, callee_node, callsite);
        self.callsite_to_edges
            .entry(callsite)
            .or_default()
            .insert(edge_id);
        self.func_to_callsites
            .entry(callee_id)
            .or_default()
            .push(callsite);
        true
    }

    /// Return a iterator for the reachable functions.
    pub fn reachable_funcs_iter(&self) -> chunked_queue::IterCopied<N> {
        self.reachable_funcs.iter_copied()
    }

    /// Produce a dot file representation of the call graph
    /// for displaying with Graphviz.
    pub fn to_dot(&self, dot_path: &std::path::Path) {
        let node_fmt = |node: &N, f: &mut fmt::Formatter| -> fmt::Result {
            node.dot_fmt(f)
        };
        let edge_fmt = |edge: &E, f: &mut fmt::Formatter| -> fmt::Result {
            edge.dot_fmt(f)
        };

        let output = format!(
            "{:?}",
            Dot::with_graph_fmt(&self.graph, &[], &node_fmt, &edge_fmt)
        );
        match std::fs::write(dot_path, output) {
            Ok(_) => (),
            Err(e) => panic!("Failed to write dot file output: {:?}", e),
        };
    }
}
