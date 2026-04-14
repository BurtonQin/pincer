use smallvec::{smallvec, SmallVec};

use crate::infoflow::ifds::{
    flow_functions::FlowFunctions,
    path_edge::{PathEdge, PathEdgeData, PathEdgeNode},
    path_edge_functions::PathEdgeFunctions,
};

pub struct DefaultPathEdgeFunctions<'a, N, D, F, U>
where
    D: std::cmp::Eq,
    U: FlowFunctions<N, D, F>,
{
    pub(crate) flow_functions: U,
    retain: Box<dyn Fn(&D) -> bool + 'a>,
    marker: std::marker::PhantomData<(N, D, F)>,
}

impl<'a, N, D, F, U> DefaultPathEdgeFunctions<'a, N, D, F, U>
where
    D: std::cmp::Eq,
    U: FlowFunctions<N, D, F>,
{
    pub fn new(
        flow_functions: U,
        retain: impl Fn(&D) -> bool + 'a,
    ) -> DefaultPathEdgeFunctions<'a, N, D, F, U> {
        DefaultPathEdgeFunctions {
            flow_functions,
            retain: Box::new(retain),
            marker: std::marker::PhantomData,
        }
    }

    pub fn retain(&self, d: &D) -> bool {
        (self.retain)(d)
    }

    pub fn get_flow_functions(&self) -> &U {
        &self.flow_functions
    }
}

impl<'a, N, D, F, U> PathEdgeFunctions<N, D, F> for DefaultPathEdgeFunctions<'a, N, D, F, U>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    U: FlowFunctions<N, D, F>,
{
    fn normal_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        succ: N,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        let f = self.flow_functions.get_normal_flow_function(prev_edge, succ);
        let sp = prev_edge.get_start();
        let d1 = prev_edge.fact_at_source();
        let d2 = prev_edge.fact_at_target();
        let res = f(d2);
        let mut out = SmallVec::new();
        for d3 in res.into_iter() {
            if !self.retain(&d3) {
                continue;
            }
            let succ_edge = PathEdge::new(sp, d1.clone(), succ, d3);
            out.push(succ_edge);
        }
        out
    }

    fn call_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        callee: F,
        callee_sp: N,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        let d2 = prev_edge.fact_at_target();
        let f = self
            .flow_functions
            .get_call_flow_function(prev_edge, callee, callee_sp);
        let res = f(d2);
        let mut out = SmallVec::new();
        for d3 in res.into_iter() {
            if !self.retain(&d3) {
                continue;
            }
            let succ_edge = PathEdge::new(callee_sp, d3.clone(), callee_sp, d3);
            out.push(succ_edge);
        }
        out
    }

    fn balanced_return_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        return_site: N,
        callee: F,
        incoming_edge: &PathEdge<N, D>,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        let sp = incoming_edge.get_start();
        let n = incoming_edge.get_target();
        let d2 = prev_edge.fact_at_target();
        let new_d1 = incoming_edge.fact_at_source();
        let f = self.flow_functions.get_return_flow_function(
            prev_edge,
            Some(incoming_edge),
            n,
            callee,
            return_site,
        );
        let targets = f(d2);
        let mut out = SmallVec::new();
        for d3 in targets.into_iter() {
            if !self.retain(&d3) {
                continue;
            }
            let succ_edge = PathEdge::new(sp, new_d1.clone(), return_site, d3);
            out.push(succ_edge);
        }
        out
    }

    fn unbalanced_return_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        call_site: Option<N>,
        return_site: Option<N>,
        callee: F,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        let d1 = prev_edge.fact_at_source();
        let d2 = prev_edge.fact_at_target();
        if call_site.is_none() || return_site.is_none() {
            return smallvec![];
        }
        let (call_site, return_site) = (call_site.unwrap(), return_site.unwrap());
        let f = self.flow_functions.get_return_flow_function(
            prev_edge,
            None,
            call_site,
            callee,
            return_site,
        );
        let targets = f(d2);
        let mut out = SmallVec::new();
        for d3 in targets.into_iter() {
            if !self.retain(&d3) {
                continue;
            }
            let succ_edge = PathEdge::new(call_site, d1.clone(), return_site, d3);
            out.push(succ_edge);
        }
        out
    }

    fn call_to_return_function(
        &self,
        prev_edge: &PathEdge<N, D>,
        return_site: N,
        callee: Option<F>,
    ) -> SmallVec<[PathEdge<N, D>; 1]> {
        let d1 = prev_edge.fact_at_source();
        let sp = prev_edge.get_start();
        let d2 = prev_edge.fact_at_target();
        let f =
            self.flow_functions
                .get_call_to_return_flow_function(prev_edge, return_site, callee);
        let targets = f(d2);
        let mut out = SmallVec::new();
        for d3 in targets.into_iter() {
            if !self.retain(&d3) {
                continue;
            }
            let succ_edge = PathEdge::new(sp, d1.clone(), return_site, d3);
            out.push(succ_edge);
        }
        out
    }
}
