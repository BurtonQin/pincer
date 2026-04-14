use smallvec::{smallvec, SmallVec};
use std::collections::HashSet;
use rustc_middle::mir;

use crate::analysis_context::AnalysisContext;
use crate::mir::builtins::is_intrinsics_copy;
use crate::mir::function::FuncDef;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::function_call_handler::{FunctionCallHandler, FunctionCallStubs};
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::points_of_aliasing;
use crate::tsa::aliases_project_from;
use crate::tsa::state::{TypeState, SymbState, SymbStateSupport};
use crate::tsa::state_transition::TypeStateTransition;
use crate::tsa::{TSAPathEdgeNode, TSAPathEdge};

/// Creates a FunctionCallStubs with all TSA-analysis handlers registered.
pub fn tsa_call_stubs<'analysis, 'tcx, N, S, T>(
    acx: &'analysis AnalysisContext<'tcx>,
    trans: T,
) -> FunctionCallStubs<'analysis, 'tcx, N, SymbState<'tcx, S, AccessPath<'tcx>>>
where
    N: TSAPathEdgeNode<'tcx> + 'analysis,
    S: TypeState + 'analysis,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>> + 'analysis,
{
    FunctionCallStubs::new(vec![
        Box::new(TSAIntrinsicsCopyHandler::new(acx, trans)),
    ])
}

pub struct TSAIntrinsicsCopyHandler<'analysis, 'tcx, N, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    acx: &'analysis AnalysisContext<'tcx>,
    trans: T,
    marker: std::marker::PhantomData<(N, S)>,
}

impl<'analysis, 'tcx, N, S, T> TSAIntrinsicsCopyHandler<'analysis, 'tcx, N, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>, trans: T) -> Self {
        TSAIntrinsicsCopyHandler { acx, trans, marker: std::marker::PhantomData }
    }

    fn new_succ_edge(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        out_state: SymbState<'tcx, S, AccessPath<'tcx>>,
        return_site: N,
    ) -> TSAPathEdge<'tcx, S, N> {
        PathEdge::new(
            prev_edge.get_start(),
            prev_edge.fact_at_source().clone(),
            return_site,
            out_state,
        )
    }

    /// Stub the `std::intrinsics::copy` and `std::intrinsics::copy_nonoverlapping` functions.
    fn stub_intrinsics_copy(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        callsite: N,
        return_site: N,
        _callee: FuncDef<'tcx>,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        let mut state = prev_edge.fact_at_target().clone_owned();
        let callsite = callsite.as_callsite();

        let call_args = callsite.call_args(self.acx.tcx);
        let src_ptr = match call_args[0] {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => place,
            _ => return smallvec![self.new_succ_edge(prev_edge, state, return_site)],
        };
        let dst_ptr = match call_args[1] {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => place,
            _ => return smallvec![self.new_succ_edge(prev_edge, state, return_site)],
        };

        self.trans.on_pointer_dereference(&mut state, &src_ptr);
        self.trans.on_pointer_dereference(&mut state, &dst_ptr);
        if state.type_state.is_error_state() {
            return smallvec![self.new_succ_edge(prev_edge, state, return_site)];
        }

        let src_deref = self.acx.tcx.mk_place_deref(src_ptr);
        let dst_deref = self.acx.tcx.mk_place_deref(dst_ptr);
        let mut gen_set = HashSet::new();
        let src_aliases = aliases_project_from(self.acx, &state.aliases(), &src_deref);
        for alias in src_aliases.iter() {
            let new_alias = alias.derive_with_new_base(self.acx, &src_deref, &dst_deref);
            gen_set.insert(new_alias);

            gen_set.extend(
                points_of_aliasing::load_or_store::process_load_or_store_poa(
                    self.acx, &new_alias, callsite,
                ),
            );
            gen_set.retain(|alias| !alias.is_inactive());
        }

        for alias in gen_set {
            state.borrow_mut().aliases_mut().insert(alias);
        }

        return smallvec![self.new_succ_edge(prev_edge, state, return_site)];
    }
}

impl<'analysis, 'tcx, N, S, T> FunctionCallHandler<'tcx, N, SymbState<'tcx, S, AccessPath<'tcx>>>
    for TSAIntrinsicsCopyHandler<'analysis, 'tcx, N, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    fn can_handle(&self, callee: FuncDef<'tcx>) -> bool {
        is_intrinsics_copy(self.acx, callee)
    }

    fn handle(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        callsite: N,
        return_site: N,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        self.stub_intrinsics_copy(prev_edge, callsite, return_site, callee)
    }
}
