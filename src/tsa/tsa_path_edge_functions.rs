use log::*;
use smallvec::{smallvec, SmallVec};

use crate::infoflow::cfg::CFGQueries;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::data::access_path::AccessPath;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::ifds::default_path_edge_functions::DefaultPathEdgeFunctions;
use crate::infoflow::ifds::path_edge_functions::PathEdgeFunctions;
use crate::infoflow::ifds::function_call_handler::FunctionCallStubs;
use crate::mir::function::FuncDef;
use crate::mir::unit::{StatementOrTerminator, statement_or_terminator_at};
use crate::tsa::state::{SymbState, TypeState};
use crate::tsa::state_transition::{call_transition_function, TypeStateTransition};
use crate::tsa::tsa_call_handlers::tsa_call_stubs;
use crate::tsa::tsa_flow_functions::TypeStateAnalysisFlowFunctions;
use crate::tsa::{TSAPathEdgeNode, TSAPathEdge};

pub struct TypeStateAnalysisPathEdgeFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    pub acx: &'analysis AnalysisContext<'tcx>,
    icfg: &'cfg I,
    delegate: DefaultPathEdgeFunctions<
        'analysis,
        N,
        SymbState<'tcx, S, AccessPath<'tcx>>,
        FuncDef<'tcx>,
        TypeStateAnalysisFlowFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>,
    >,
    trans: T,
    call_stubs: FunctionCallStubs<'analysis, 'tcx, N, SymbState<'tcx, S, AccessPath<'tcx>>>,
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    TypeStateAnalysisPathEdgeFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    'analysis: 'cfg,
    N: TSAPathEdgeNode<'tcx> + 'analysis,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState + 'analysis,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>> + 'analysis,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>, icfg: &'cfg I, trans: T) -> Self {
        TypeStateAnalysisPathEdgeFunctions {
            acx,
            icfg,
            delegate: DefaultPathEdgeFunctions::new(
                TypeStateAnalysisFlowFunctions::new(acx, icfg, trans),
                |_| true,
            ),
            trans,
            call_stubs: tsa_call_stubs(acx, trans),
        }
    }
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    TypeStateAnalysisPathEdgeFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    fn is_target_in_error_state(&self, edge: &TSAPathEdge<'tcx, S, N>) -> bool {
        edge.fact_at_target().get_type_state().is_error_state()
    }
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    PathEdgeFunctions<N, SymbState<'tcx, S, AccessPath<'tcx>>, FuncDef<'tcx>>
    for TypeStateAnalysisPathEdgeFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    fn normal_function(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        succ: N,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        let out = self.delegate.normal_function(prev_edge, succ);
        debug!("Normal function edge: {:?}", prev_edge);
        for succ in &out {
            debug!("\tsucc: {:?}", succ);
        }
        out
    }

    fn call_function(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        callee: FuncDef<'tcx>,
        callee_sp: N,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        let out = self.delegate.call_function(prev_edge, callee, callee_sp);
        for succ in &out {
            debug!("Call Function Edge: {:?}", succ);
        }
        out
    }

    fn balanced_return_function(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        return_site: N,
        callee: FuncDef<'tcx>,
        incoming_edge: &TSAPathEdge<'tcx, S, N>,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        let out =
            self.delegate
                .balanced_return_function(prev_edge, return_site, callee, incoming_edge);
        for succ in &out {
            debug!("Balanced Return Function Edge: {:?}", prev_edge);
            debug!("\tsucc: {:?}", succ);
        }
        out
    }

    fn unbalanced_return_function(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        _call_site: Option<N>,
        _return_site: Option<N>,
        _callee: FuncDef<'tcx>,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        let (start_node, init_state) = prev_edge.get_start_node();
        let (exit_node, out_state) = prev_edge.get_target_node();

        // exit_node is always a return/resume terminator — as_callsite() is safe here
        let terminator = exit_node.as_callsite();

        let StatementOrTerminator::Terminator(terminator_kind) =
            statement_or_terminator_at(self.acx.tcx, terminator)
        else {
            unreachable!("Expected a Terminator node");
        };
        match terminator_kind {
            rustc_middle::mir::TerminatorKind::Return | rustc_middle::mir::TerminatorKind::UnwindResume => {
                if let Some(out) =
                    self.trans
                        .on_unbalanced_return(terminator.func, init_state, out_state)
                {
                    let ret = smallvec![TSAPathEdge::new(
                        *start_node,
                        init_state.clone(),
                        *exit_node,
                        out
                    )];
                    return ret;
                }
            }
            _ => {}
        }

        return smallvec![];
    }

    fn call_to_return_function(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        return_site: N,
        callee: Option<FuncDef<'tcx>>,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        self.delegate
            .call_to_return_function(prev_edge, return_site, callee)
    }

    fn is_stubbed_call(&self, callee: FuncDef<'tcx>) -> bool {
        self.trans.is_transition_function(callee)
            || self.call_stubs.is_stubbed_call(callee)
    }

    fn stub_function_call(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        callsite: N,
        return_site: N,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[TSAPathEdge<'tcx, S, N>; 1]> {
        if self.is_target_in_error_state(prev_edge) {
            return self
                .delegate
                .call_to_return_function(prev_edge, return_site, Some(callee));
        }

        // Ignore the unwind branches for the stubbed function calls.
        let is_unwind_branch = self.icfg.is_unwind_branch(callsite, return_site);
        if is_unwind_branch {
            return smallvec![];
        }

        if self.trans.is_transition_function(callee) {
            call_transition_function(&self.trans, prev_edge, callsite, return_site, callee)
        } else {
            self.call_stubs
                .stub_function_call(prev_edge, callsite, return_site, callee)
        }
    }
}
