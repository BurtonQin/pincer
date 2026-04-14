use smallvec::SmallVec;

use crate::infoflow::ifds::path_edge::PathEdge;

/// Path edge functions allow to modifying the set of path edges which flow out of statements. Thus
/// one can directly interfere the creation process and modify the outflowing edges to be generated.
///
/// N: The type of Statements to be used
/// D: The data flow fact
/// F: The generic for a function
pub trait PathEdgeFunctions<N, D, F> {
    fn normal_function(&self, prev_edge: &PathEdge<N, D>, succ: N)
        -> SmallVec<[PathEdge<N, D>; 1]>;

    fn call_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        callee: F,
        callee_sp: N,
    ) -> SmallVec<[PathEdge<N, D>; 1]>;

    fn balanced_return_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        return_site: N,
        callee: F,
        incoming_edge: &PathEdge<N, D>,
    ) -> SmallVec<[PathEdge<N, D>; 1]>;

    fn unbalanced_return_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        call_site: Option<N>,
        return_site: Option<N>,
        callee: F,
    ) -> SmallVec<[PathEdge<N, D>; 1]>;

    fn call_to_return_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        return_site: N,
        callee: Option<F>,
    ) -> SmallVec<[PathEdge<N, D>; 1]>;

    fn is_stubbed_call(&self, _callee: F) -> bool {
        false
    }

    fn stub_function_call(
        &self,
        _prev_edge: &PathEdge<N, D>,
        _callsite: N,
        _return_site: N,
        _callee: F,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        SmallVec::new()
    }

}
