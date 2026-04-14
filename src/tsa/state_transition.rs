use std::collections::HashSet;
use smallvec::SmallVec;

use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::mir::function::FuncDef;
use crate::mir::unit::Unit;
use crate::tsa::state::{SymbState, TypeState};
use crate::tsa::TSAPathEdgeNode;
use rustc_middle::mir::Place;

pub trait TypeStateTransition<'tcx, S: TypeState, P: std::cmp::Eq + std::hash::Hash + Copy>:
    Copy + Clone
{
    fn is_transition_function(&self, callee: FuncDef<'tcx>) -> bool;

    fn on_transition_function_call(
        &self,
        in_state: &SymbState<'tcx, S, P>,
        callsite: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[SymbState<'tcx, S, P>; 1]>;

    fn on_unbalanced_return(
        &self,
        func: FuncDef<'tcx>,
        init_state: &SymbState<'tcx, S, P>,
        out_state: &SymbState<'tcx, S, P>,
    ) -> Option<SymbState<'tcx, S, P>>;

    fn on_mir_unavailable_callee(
        &self,
        in_state: &SymbState<'tcx, S, P>,
        callee: Option<FuncDef<'tcx>>,
        arg_aliases: &HashSet<&AccessPath<'tcx>>,
    ) -> Option<SymbState<'tcx, S, P>>;

    fn on_pointer_dereference(&self, state: &mut SymbState<'tcx, S, P>, deref_ptr: &Place<'tcx>);
}

/// Free function adapter: converts generic N to Unit via as_callsite(), then calls on_transition_function_call.
pub fn call_transition_function<'tcx, S, P, N, T>(
    trans: &T,
    prev_edge: &PathEdge<N, SymbState<'tcx, S, P>>,
    callsite: N,
    return_site: N,
    callee: FuncDef<'tcx>,
) -> SmallVec<[PathEdge<N, SymbState<'tcx, S, P>>; 1]>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy,
    N: TSAPathEdgeNode<'tcx>,
    T: TypeStateTransition<'tcx, S, P>,
{
    let sp = prev_edge.get_start();
    let d1 = prev_edge.fact_at_source();
    let d2 = prev_edge.fact_at_target();
    let res = trans.on_transition_function_call(d2, callsite.as_callsite(), callee);
    let mut out = SmallVec::new();
    for d3 in res.into_iter() {
        let succ_edge = PathEdge::new(sp, d1.clone(), return_site, d3);
        out.push(succ_edge);
    }
    out
}
