use log::*;
use smallvec::{smallvec, SmallVec};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::ifds::function_call_handler::FunctionCallStubs;
use super::backward_call_handlers::backward_call_stubs;
use crate::infoflow;
use crate::infoflow::aliasing::query::QueryList;
use crate::infoflow::cfg::backward_infoflow_cfg::BackwardInfoflowCFG;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::ifds::default_path_edge_functions::DefaultPathEdgeFunctions;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::ifds::path_edge_functions::PathEdgeFunctions;
use crate::infoflow::{
    points_of_aliasing,
    PointerFlowOrigin, Unit,
};
use crate::mir::function::FuncDef;

use super::backward_flow_functions::BackwardFlowFunctions;

pub struct BackwardPathEdgeFunctions<'analysis, 'cfg, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
    bw_icfg: &'cfg BackwardInfoflowCFG<'tcx>,
    queries: QueryList<'tcx>,
    delegate: DefaultPathEdgeFunctions<
        'analysis,
        Unit<'tcx>,
        AccessPath<'tcx>,
        FuncDef<'tcx>,
        BackwardFlowFunctions<'analysis, 'tcx>,
    >,
    call_stubs: FunctionCallStubs<'analysis, 'tcx, Unit<'tcx>, AccessPath<'tcx>>,
}

impl<'analysis, 'cfg, 'tcx> BackwardPathEdgeFunctions<'analysis, 'cfg, 'tcx> {
    pub fn new(
        acx: &'analysis AnalysisContext<'tcx>,
        bw_icfg: &'cfg BackwardInfoflowCFG<'tcx>,
        queries: QueryList<'tcx>,
    ) -> BackwardPathEdgeFunctions<'analysis, 'cfg, 'tcx> {
        BackwardPathEdgeFunctions {
            acx,
            bw_icfg,
            queries: queries.clone(),
            delegate: DefaultPathEdgeFunctions::new(
                BackwardFlowFunctions::new(acx),
                move |d| infoflow::retain_access_path(acx, d),
            ),
            call_stubs: backward_call_stubs(acx),
        }
    }

    fn retain(&self, d: &AccessPath<'tcx>) -> bool {
        infoflow::retain_access_path(self.acx, d)
    }

    pub fn curr_query(&self) -> Query<'tcx> {
        self.queries.curr_query()
    }

    pub fn is_in_query_origin_function(
        &self,
        edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) -> bool {
        if self.curr_query().unit.func == edge.get_target().func
            && *edge.fact_at_source() == self.curr_query().access_path
        {
            true
        } else {
            false
        }
    }

    /// When the flow reaches the start point of the start function, the edge's target fact should
    /// be a projection of a parameter of this function. The pointer flow originates from this target.
    pub fn reaches_start_point_of_start_function(
        &self,
        edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) {
        let dtarget = edge.fact_at_target();
        if dtarget.is_heap_pointer() {
            let flow_origin = PointerFlowOrigin::new_allocation(*dtarget, dtarget.alloc_trace.unwrap());
            self.acx
                .query_cache
                .add_flow_origin(self.curr_query(), flow_origin);
            return;
        }

        if dtarget.is_from_param(self.acx.tcx) {
            trace!("reaches_start_point_of_start_function: {:?}", edge);
            let flow_origin = PointerFlowOrigin::new_parameter(*edge.fact_at_target());
            self.acx
                .query_cache
                .add_flow_origin(self.curr_query(), flow_origin);
            return;
        }

        if dtarget.has_ref_elem() {
            // The queried pointer may point to a local variable in another function
            if !self.is_in_query_origin_function(&edge) {
                error!(
                    "The queried pointer {:?}@{:?} may point to a local variable {:?} in another function {:?}", 
                    self.curr_query().access_path,
                    self.curr_query().unit,
                    dtarget,
                    edge.get_target().func
                );
            } else {
                // The queried pointer points to a local variable in the same function
                let flow_origin: PointerFlowOrigin<'_> = PointerFlowOrigin::new_reference(
                    *dtarget,
                    edge.get_target().location,
                );
                self.acx
                    .query_cache
                    .add_flow_origin(self.curr_query(), flow_origin);
                trace!("Add flow origin: {:?}", flow_origin);
            }
        }
    }

    fn normal_function_extendor(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        normal_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        let mut out = SmallVec::new();
        let target = normal_edge.fact_at_target();
        if target.has_ref_elem() {
            // Reaches a direct reference site
            if !target.is_indirect() {
                let end_point = self.bw_icfg.get_end_points_of(target.func_def)[0];
                out.push(PathEdge::new(
                    normal_edge.get_start(),
                    *normal_edge.fact_at_source(),
                    end_point,
                    *target,
                ));
            } else {
                let next_edges = points_of_aliasing::indirect_reference::process_indirect_reference_poa(
                    self.acx,
                    self.bw_icfg,
                    self.curr_query(),
                    *normal_edge,
                    target,
                    prev_edge.get_target(),
                );
                out.extend(next_edges);
            }
        } else {
            out.push(*normal_edge);
            // Apply POA for facts transformed by an assignment.
            // Skip inactive facts being activated (d3 != d2 but not an assignment).
            let source_fact = prev_edge.fact_at_target();
            if target != source_fact && !source_fact.is_inactive() {
                let curr_unit = prev_edge.get_target();
                let poa_aliases = if self
                    .delegate
                    .flow_functions
                    .is_load_poa_pending(target)
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
        }
        out
    }

    fn call_function_extendor(
        &self,
        call_edge: PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        let mut out = SmallVec::new();

        let dsource = call_edge.fact_at_source();
        let callee_sp = call_edge.get_target();
        let dtargets = points_of_aliasing::backward_call::process_backward_call_poa(
            self.acx, callee, callee_sp, &dsource,
        );
        for dtarget in dtargets {
            if self.retain(&dtarget) {
                let succ_edge = PathEdge::new(callee_sp, dtarget, callee_sp, dtarget);
                out.push(succ_edge);
            }
        }
        out
    }

    fn return_function_extendor(
        &self,
        return_edge: PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        return_site: Unit<'tcx>,
        incoming_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        let dtarget = return_edge.fact_at_target();
        if dtarget.is_heap_pointer() {
            return smallvec![return_edge];
        }

        if incoming_edge.fact_at_target() == return_edge.fact_at_target() {
            return smallvec![return_edge];
        }

        let edges = points_of_aliasing::backward_return::process_backward_return_poa(
            self.acx,
            self.bw_icfg,
            self.curr_query(),
            return_edge,
            incoming_edge.get_target(),
            return_site,
        );
        edges
            .into_iter()
            .filter(|e| self.retain(e.fact_at_target()))
            .collect()
    }
}

impl<'analysis, 'cfg, 'tcx> PathEdgeFunctions<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>
    for BackwardPathEdgeFunctions<'analysis, 'cfg, 'tcx>
{
    fn normal_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        succ: Unit<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        trace!("Backward Normal {:?}", prev_edge);
        self.delegate.flow_functions.clear_load_poa_pending();
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
        let mut out = SmallVec::new();
        for edge in self.delegate.call_function(prev_edge, callee, callee_sp) {
            out.extend(self.call_function_extendor(edge, callee));
        }
        out
    }

    fn balanced_return_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        return_site: Unit<'tcx>,
        callee: FuncDef<'tcx>,
        incoming_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        if self.is_in_query_origin_function(&prev_edge) {
            self.reaches_start_point_of_start_function(&prev_edge);
        }

        let mut out = SmallVec::new();
        for edge in
            self.delegate
                .balanced_return_function(prev_edge, return_site, callee, incoming_edge)
        {
            out.extend(self.return_function_extendor(edge, return_site, incoming_edge));
        }
        out
    }

    fn unbalanced_return_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        _call_site: Option<Unit<'tcx>>,
        _return_site: Option<Unit<'tcx>>,
        _callee: FuncDef<'tcx>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
        // The query should be started inside this function, do not propagate further.
        if self.is_in_query_origin_function(&prev_edge) {
            self.reaches_start_point_of_start_function(&prev_edge);
        }
        return smallvec![];
    }

    fn call_to_return_function(
        &self,
        prev_edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        return_site: Unit<'tcx>,
        callee: Option<FuncDef<'tcx>>,
    ) -> SmallVec<[PathEdge<Unit<'tcx>, AccessPath<'tcx>>; 1]> {
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
