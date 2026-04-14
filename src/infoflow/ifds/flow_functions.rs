use smallvec::SmallVec;

use crate::infoflow::ifds::path_edge::PathEdge;

pub trait FlowFunctions<N, D, F>
where
    D: std::cmp::Eq,
{
    /// Returns the flow function that computes the flow for a normal statement,
    /// i.e., a statement that is neither a call nor an exit statement.
    /// curr: The current statement.
    /// succ: The successor for which the flow is computed. This value can
    ///       be used to compute a branched analysis that propagates
    ///       different values depending on where control0flow branches.
    fn get_normal_flow_function(&self, edge: &PathEdge<N, D>, succ: N) -> impl Fn(&D) -> SmallVec<[D; 1]>;

    /// Returns the flow function that computes the flow for a call statement.
    /// target_func: The concrete target method for which the flow is computed.
    fn get_call_flow_function(
        &self,
        edge: &PathEdge<N, D>,
        callee: F,
        first_stmt_in_callee: N,
    ) -> impl Fn(&D) -> SmallVec<[D; 1]>;

    /// Returns the flow function that computes the flow for a an exit from a
    /// funtion. An exit can be a return or a unwind.
    /// callee_func: The function from which exit_stmt returns.
    fn get_return_flow_function(
        &self,
        edge: &PathEdge<N, D>,
        incoming_edge: Option<&PathEdge<N, D>>,
        callsite: N,
        callee: F,
        return_site: N,
    ) -> impl Fn(&D) -> SmallVec<[D; 1]>;

    /// Returns the flow function that computes the flow from a call site to a
    /// successor statement just after the call.
    fn get_call_to_return_flow_function(
        &self,
        edge: &PathEdge<N, D>,
        return_site: N,
        callee: Option<F>,
    ) -> impl Fn(&D) -> SmallVec<[D; 1]>;

}
