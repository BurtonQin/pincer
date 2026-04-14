use smallvec::SmallVec;

use crate::infoflow::ifds::path_edge::{PathEdge, PathEdgeData, PathEdgeNode};
use crate::mir::function::FuncDef;

/// A handler for a specific category of stubbed function calls.
/// Each handler is responsible for one logical category (e.g., alloc, realloc, copy).
pub trait FunctionCallHandler<'tcx, N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    /// Returns true if this handler can stub the given callee.
    fn can_handle(&self, callee: FuncDef<'tcx>) -> bool;

    /// Produces the output path edges for the stubbed function call.
    fn handle(
        &self,
        prev_edge: &PathEdge<N, D>,
        callsite: N,
        return_site: N,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[PathEdge<N, D>; 1]>;
}

/// A composable stub dispatcher that dispatches to registered handlers.
pub struct FunctionCallStubs<'a, 'tcx, N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    handlers: Vec<Box<dyn FunctionCallHandler<'tcx, N, D> + 'a>>,
}

impl<'a, 'tcx, N, D> FunctionCallStubs<'a, 'tcx, N, D>
where
    N: PathEdgeNode,
    D: PathEdgeData,
{
    pub fn new(handlers: Vec<Box<dyn FunctionCallHandler<'tcx, N, D> + 'a>>) -> Self {
        FunctionCallStubs { handlers }
    }

    pub fn is_stubbed_call(&self, callee: FuncDef<'tcx>) -> bool {
        self.handlers.iter().any(|h| h.can_handle(callee))
    }

    pub fn stub_function_call(
        &self,
        prev_edge: &PathEdge<N, D>,
        callsite: N,
        return_site: N,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        for handler in &self.handlers {
            if handler.can_handle(callee) {
                return handler.handle(prev_edge, callsite, return_site, callee);
            }
        }
        SmallVec::new()
    }
}
