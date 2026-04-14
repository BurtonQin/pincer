use smallvec::SmallVec;

/// An interprocedural control-flow graph.
///
/// N: Nodes in the CFG
/// F: Function representation
pub trait InterproceduralCFG<N, F> {
    /// Returns the function containing a node.
    fn get_function_of(&self, n: N) -> F;
    /// Returns the predecessor nodes.
    fn get_preds_of(&self, n: N) -> SmallVec<[N; 2]>;
    /// Returns the successor nodes.
    fn get_succs_of(&self, n: N) -> SmallVec<[N; 2]>;
    /// Returns all callee functions for a given call.
    fn get_callees_of_call_at(&self, n: N) -> SmallVec<[F; 1]>;
    /// Returns all caller statements/nodes of a given functions.
    fn get_callers_of(&self, f: F) -> SmallVec<[N; 2]>;
    /// Returns the start point of a given function. There may be
    /// more than one start point in case of a backward analysis.
    fn get_start_points_of(&self, f: F) -> SmallVec<[N; 2]>;
    /// Returns the end point of a given function.
    fn get_end_points_of(&self, f: F) -> SmallVec<[N; 2]>;
    /// Returns all statements to which a call could return.
    fn get_return_sites_of_call_at(&self, n: N) -> SmallVec<[N; 2]>;
    /// Returns the predecessor statement to of a call
    fn get_preds_of_call_at(&self, n: N) -> SmallVec<[N; 2]>;
    /// Returns true if the given statement is a call site.
    fn is_call_node(&self, n: N) -> bool;
    /// Returns true if the given statement leads to a function return
    /// including UnwindTerminate and Unreachable in forward analysis
    fn is_exit_node(&self, n: N) -> bool;
    /// Returns true is this is a function's start statement.
    fn is_start_point(&self, n: N) -> bool;

    /// Returns whether an inter-procedural flow from `source` to `target` at `call_site` is feasible.
    /// - In process_exit: source=exit_node, target=return_site, call_site=caller's call node
    /// - In process_call: source=call_node, target=callee_start_point, call_site=call_node
    fn is_feasible_interprocedural_flow(&self, _call_site: N, _source: N, _target: N) -> bool {
        true
    }
}
