use log::*;

use smallvec::{smallvec, SmallVec};

use crate::analysis_context::AnalysisContext;
use crate::infoflow;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::default_path_edge_functions::DefaultPathEdgeFunctions;
use crate::infoflow::ifds::incomings::Incomings;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::ifds::path_edge_functions::PathEdgeFunctions;
use crate::infoflow::{points_of_aliasing, Unit};
use crate::mir::function::FuncDef;

use super::forward_flow_functions::ForwardFlowFunctions;
use crate::infoflow::ifds::function_call_handler::FunctionCallStubs;
use super::forward_call_handlers::forward_call_stubs;

pub struct ForwardPathEdgeFunctions<'analysis, 'tcx, 'bw> {
    acx: &'analysis AnalysisContext<'tcx>,
    delegate: DefaultPathEdgeFunctions<
        'analysis,
        Unit<'tcx>,
        AccessPath<'tcx>,
        FuncDef<'tcx>,
        ForwardFlowFunctions<'analysis, 'tcx>,
    >,
    #[allow(unused)]
    active_path_start_point: Option<Unit<'tcx>>,
    active_path_end_point: Option<Unit<'tcx>>,
    bw_incomings: Option<&'bw Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>>,
    call_stubs: FunctionCallStubs<'analysis, 'tcx, Unit<'tcx>, AccessPath<'tcx>>,
}

impl<'analysis, 'tcx, 'bw> ForwardPathEdgeFunctions<'analysis, 'tcx, 'bw> {
    pub fn new(
        acx: &'analysis AnalysisContext<'tcx>,
    ) -> ForwardPathEdgeFunctions<'analysis, 'tcx, 'bw> {
        ForwardPathEdgeFunctions {
            acx,
            delegate: DefaultPathEdgeFunctions::new(
                ForwardFlowFunctions::new(acx),
                move |d| infoflow::retain_access_path(acx, d),
            ),
            active_path_start_point: None,
            active_path_end_point: None,
            bw_incomings: None,
            call_stubs: forward_call_stubs(acx),
        }
    }

    fn retain(&self, d: &AccessPath<'tcx>) -> bool {
        infoflow::retain_access_path(self.acx, d)
    }

    pub fn with_active_path(
        &mut self,
        active_path_start_point: Unit<'tcx>,
        active_path_end_point: Unit<'tcx>,
    ) {
        self.active_path_start_point = Some(active_path_start_point);
        self.active_path_end_point = Some(active_path_end_point);
    }

    pub fn with_bw_incomings(
        &mut self,
        bw_incomings: &'bw Incomings<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>,
    ) {
        self.bw_incomings = Some(bw_incomings);
    }

    pub fn on_active_path(&self, n: Unit<'tcx>) -> bool {
        if let Some(end_point) = &self.active_path_end_point {
            // only checks the path in the same function
            if n.func != end_point.func {
                true
            } else {
                let body = self.acx.tcx.optimized_mir(n.func.def_id);
                n.location == end_point.location || n.is_predecessor_of(end_point, body)
            }
        } else {
            true
        }
    }

    fn normal_function_extendor(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        normal_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        let mut out = SmallVec::new();
        let target = normal_edge.fact_at_target();
        out.push(*normal_edge);
        // Apply POA for facts transformed by an assignment.
        // Skip deactivated facts — they don't need POA.
        let source_fact = prev_edge.fact_at_target();
        if target != source_fact && !target.is_inactive() {
            let curr_unit = prev_edge.get_target();
            let poa_aliases = if self
                .delegate
                .flow_functions
                .is_store_poa_pending(target)
            {
                points_of_aliasing::load_or_store::process_load_or_store_poa(
                    self.acx, target, curr_unit,
                )
            } else {
                points_of_aliasing::address_taken::process_address_taken_poa(
                    self.acx, target, curr_unit,
                )
            };
            for alias in poa_aliases {
                if self.retain(&alias) {
                    out.push(PathEdge::new(
                        normal_edge.get_start(),
                        *normal_edge.fact_at_source(),
                        normal_edge.get_target(),
                        alias,
                    ));
                }
            }
        }
        out
    }

    fn return_function_extendor(
        &self,
        return_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        sp: Unit<'tcx>,
        d1: AccessPath<'tcx>,
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        let aliases = points_of_aliasing::forward_return::process_forward_return_poa(
            self.acx,
            *return_edge.fact_at_target(),
            callsite,
            return_site,
        );
        aliases
            .into_iter()
            .filter(|d| self.retain(d))
            .map(|d| PathEdge::new(sp, d1, return_site, d))
            .collect()
    }
}

impl<'analysis, 'tcx, 'bw> PathEdgeFunctions<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>
    for ForwardPathEdgeFunctions<'analysis, 'tcx, 'bw>
{
    fn normal_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        succ: Unit<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        if !self.on_active_path(succ) {
            return SmallVec::new();
        }
        trace!("Forward Normal {:?}", prev_edge);
        self.delegate.flow_functions.clear_store_poa_pending();
        let res = self.delegate.normal_function(prev_edge, succ);
        let mut out = SmallVec::new();
        for edge in res.iter() {
            out.extend(self.normal_function_extendor(prev_edge, edge));
        }
        out
    }

    fn call_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        callee: FuncDef<'tcx>,
        callee_sp: Unit<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        let out = self.delegate.call_function(prev_edge, callee, callee_sp);
        out
    }

    fn balanced_return_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        return_site: Unit<'tcx>,
        callee: FuncDef<'tcx>,
        incoming_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        if !self.on_active_path(return_site) {
            return SmallVec::new();
        }
        let mut out =
            self.delegate
                .balanced_return_function(prev_edge, return_site, callee, incoming_edge);
        let callsite = incoming_edge.get_target();
        let sp = incoming_edge.get_start();
        let d1 = *incoming_edge.fact_at_source();
        for edge in out.clone().iter() {
            // Skip POA if the edge's target fact is unchanged from the incoming edge's target.
            if incoming_edge.fact_at_target() == edge.fact_at_target() {
                continue;
            }
            out.extend(self.return_function_extendor(edge, sp, d1, callsite, return_site));
        }
        out
    }

    fn unbalanced_return_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        callsite: Option<Unit<'tcx>>,
        return_site: Option<Unit<'tcx>>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        // Retrieve the incoming set for the backward edges, to know, where the forward analysis can
        // return to in an unbalanced manner (forward analysis follows backward analysis, hence it
        // also should do so at returns.)
        if let Some(bw_incomings) = self.bw_incomings {
            if callsite.is_none() || return_site.is_none() {
                return smallvec![];
            }
            let (callsite, return_site) = (callsite.unwrap(), return_site.unwrap());
            if bw_incomings.has_incoming_from(callee, callsite) {
                let mut out = self.delegate.unbalanced_return_function(
                    prev_edge,
                    Some(callsite),
                    Some(return_site),
                    callee,
                );

                let sp = callsite;
                let d1 = *prev_edge.fact_at_source();
                for edge in out.clone().iter() {
                    out.extend(self.return_function_extendor(edge, sp, d1, callsite, return_site));
                }
                return out;
            }
        }

        return SmallVec::new();
    }

    fn call_to_return_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        return_site: Unit<'tcx>,
        callee: Option<FuncDef<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        if !self.on_active_path(return_site) {
            return SmallVec::new();
        }
        self.delegate
            .call_to_return_function(prev_edge, return_site, callee)
    }

    fn is_stubbed_call(&self, callee: FuncDef<'tcx>) -> bool {
        self.call_stubs.is_stubbed_call(callee)
    }

    fn stub_function_call(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        self.call_stubs
            .stub_function_call(prev_edge, callsite, return_site, callee)
    }

}
