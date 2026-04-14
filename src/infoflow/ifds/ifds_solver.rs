use std::collections::LinkedList;

use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::ifds::{
    ifds_tabulation_problem::IFDSTabulationProblem,
    path_edge::{PathEdge, PathEdgeData, PathEdgeNode},
    path_edge_functions::PathEdgeFunctions,
    path_edges::PathEdges,
};

/// A solver for an IFDSTabulationProblem.
///
/// N: The type of nodes in the interprocedural control-flow graph. Typically Unit.
/// D: The type of data-flow facts to be computed by the tabulation problem.
/// F: The type of objects used to represent functions.
/// I: The type of inter-procedural control-flow graph being used.
pub struct IFDSSolver<N, D, F, I, T>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash + Copy,
    I: InterproceduralCFG<N, F>,
    T: IFDSTabulationProblem<N, D, F, I>,
{
    pub(crate) propagation_count: u64,
    pub(crate) worklist: LinkedList<PathEdge<N, D>>,
    pub(crate) tabulation_problem: T,
    marker: std::marker::PhantomData<(I, F)>,
}

impl<N, D, F, I, T> IFDSSolver<N, D, F, I, T>
where
    N: PathEdgeNode,
    D: PathEdgeData,
    F: std::cmp::Eq + std::hash::Hash + Copy,
    I: InterproceduralCFG<N, F>,
    T: IFDSTabulationProblem<N, D, F, I>,
{
    pub fn new(tabulation_problem: T) -> IFDSSolver<N, D, F, I, T> {
        IFDSSolver {
            propagation_count: 0,
            worklist: LinkedList::new(),
            tabulation_problem,
            marker: std::marker::PhantomData,
        }
    }

    pub fn icfg(&self) -> &I {
        self.tabulation_problem.interprocedural_cfg()
    }

    pub fn path_edge_functions(&self) -> &(impl PathEdgeFunctions<N, D, F> + '_) {
        self.tabulation_problem.path_edge_functions()
    }

    pub fn get_tabulation_problem(&self) -> &T {
        &self.tabulation_problem
    }

    /// Lines 13-20 of the algorithm; processing a call site in the caller's context.
    /// For each possible callee, registers incoming call edges. Also propagates call-to-return flows
    /// and summarized callee flows within the caller.
    /// inc_edge: an edge whose target node resembles a method call
    fn process_call(&mut self, inc_edge: &PathEdge<N, D>) {
        let n = inc_edge.get_target(); // a call node; line 14...
        let _d2 = inc_edge.fact_at_target();
        let return_sites = self.icfg().get_return_sites_of_call_at(n);
        // for each possible callee
        let callees = self.icfg().get_callees_of_call_at(n);

        // If we cannot resolve the callee.
        if callees.is_empty() {
            // line 17-19 of Naeem/Lhotak/Rodriguez
            // process intra-procedural flows along call-to-return flow functions
            for return_site in &return_sites {
                let next_edges = self.path_edge_functions().call_to_return_function(
                    inc_edge,
                    *return_site,
                    None,
                );
                for next_edge in next_edges {
                    self.propagate(next_edge, inc_edge, PropagationType::Call2Return, None);
                }
            }
        }

        for called_proc in callees {

            if self
                .path_edge_functions()
                .is_stubbed_call(called_proc)
            {
                for return_site in &return_sites {
                    let next_edges = self.path_edge_functions().stub_function_call(
                        inc_edge,
                        n,
                        *return_site,
                        called_proc,
                    );
                    for next_edge in next_edges {
                        self.propagate(next_edge, inc_edge, PropagationType::Call2Return, None);
                    }
                }
                continue;
            }

            // still line 14
            // for each result node of the call-flow function
            let start_points = self.icfg().get_start_points_of(called_proc);
            for sp in start_points {
                // In backward analysis: skip callee exits incompatible with this call's return edges.
                if !self.icfg().is_feasible_interprocedural_flow(n, n, sp) {
                    continue;
                }
                let next_call_edges =
                    self.path_edge_functions()
                        .call_function(inc_edge, called_proc, sp);
                for next_call_edge in next_call_edges {
                    // for each callee's start point(s)
                    // create initial self-loop
                    if !self.add_incoming(called_proc, next_call_edge.clone(), inc_edge.clone()) {
                        continue;
                    }
                    // line 15.2 of Naeem/Lhotak/Rodriguez
                    let end_summ = self.end_summary(called_proc, next_call_edge.get_start_node());
                    // for each already-queried exit value <eP,d4> reachable from <sP,d3>,
                    // create new caller-side jump functions to the return sites
                    // because we have observed a potentially new incoming edge into <sP,d3>
                    if let Some(summary_edges) = end_summ {
                        for summary_edge in summary_edges {
                            for return_site in &return_sites {
                                if !self.icfg().is_feasible_interprocedural_flow(
                                    n, summary_edge.get_target(), *return_site,
                                ) {
                                    continue;
                                }
                                // compute return-flow function
                                let next_edges =
                                    self.path_edge_functions().balanced_return_function(
                                        &summary_edge,
                                        *return_site,
                                        called_proc,
                                        inc_edge,
                                    );

                                // for each target value of the function
                                for next_edge in next_edges {
                                    // If we have not changed anything in the callee, we do not need the facts
                                    // from there. Even if we change something: If we don't need the concrete
                                    // path, we can skip the callee in the predecessor chain
                                    self.propagate(
                                        next_edge,
                                        &summary_edge,
                                        PropagationType::BalancedReturn,
                                        Some(inc_edge),
                                    );
                                }
                            }
                        }
                    } else {
                        self.propagate(next_call_edge, inc_edge, PropagationType::CallEnter, None);
                    }
                }
            }
            // line 17-19 of Naeem/Lhotak/Rodriguez
            // process intra-procedural flows along call-to-return flow functions
            for return_site in &return_sites {
                let next_edges = self.path_edge_functions().call_to_return_function(
                    inc_edge,
                    *return_site,
                    Some(called_proc),
                );
                for next_edge in next_edges {
                    self.propagate(next_edge, inc_edge, PropagationType::Call2Return, None);
                }
            }
        }
    }

    /// Lines 21-32 of the algorithm.
    /// Stores callee-side summaries. Also, at the side of the caller, propagates intra-procedural
    /// flows to return sites using those newly computed summaries.
    /// summary_edge an edge whose target node resembles a method exits
    fn process_exit(&mut self, summary_edge: &PathEdge<N, D>) {
        let n = summary_edge.get_target(); // an exit node; line 21...
        let func = self.icfg().get_function_of(n);

        self.add_end_summary(func, summary_edge.clone());

        let incomings = self.incoming(summary_edge.get_start_node(), func);

        if let Some(incoming_edges) = incomings {
            for inc in incoming_edges {
                let c = inc.get_target();
                for return_site in self.icfg().get_return_sites_of_call_at(c) {
                    if !self.icfg().is_feasible_interprocedural_flow(c, n, return_site) {
                        continue;
                    }
                    let next_edges = self.path_edge_functions().balanced_return_function(
                        summary_edge,
                        return_site,
                        func,
                        &inc,
                    );
                    for next_edge in next_edges {
                        self.propagate(
                            next_edge,
                            summary_edge,
                            PropagationType::BalancedReturn,
                            Some(&inc),
                        );
                    }
                }
            }
        } else {
            // handling for unbalanced problems where we return out of a method with a fact for which we
            // have no incoming flow
            let callers = self.icfg().get_callers_of(func);
            // in cases where there are no callers
            if callers.is_empty() {
                let next_edges = self.path_edge_functions().unbalanced_return_function(
                    summary_edge,
                    None,
                    None,
                    func,
                );
                for next_edge in next_edges {
                    self.propagate(
                        next_edge,
                        summary_edge,
                        PropagationType::UnbalancedReturn,
                        None,
                    );
                }
                return;
            }
            for c in callers {
                for return_site in self.icfg().get_return_sites_of_call_at(c) {
                    if !self.icfg().is_feasible_interprocedural_flow(c, n, return_site) {
                        continue;
                    }
                    let next_edges = self.path_edge_functions().unbalanced_return_function(
                        summary_edge,
                        Some(c),
                        Some(return_site),
                        func,
                    );
                    for next_edge in next_edges {
                        self.propagate(
                            next_edge,
                            summary_edge,
                            PropagationType::UnbalancedReturn,
                            None,
                        );
                    }
                }
            }
        }
    }

    fn process_normal_flow(&mut self, edge: &PathEdge<N, D>) {
        let n = edge.get_target();
        let succs = self.icfg().get_succs_of(n);
        for m in succs {
            let next_edges = self.path_edge_functions().normal_function(edge, m);
            for next_edge in next_edges {
                self.propagate(next_edge, edge, PropagationType::Normal, None);
            }
        }
    }

    pub fn propagate(
        &mut self,
        next_edge: PathEdge<N, D>,
        prev_edge: &PathEdge<N, D>,
        _t: PropagationType,
        _inc_edge: Option<&PathEdge<N, D>>,
    ) -> bool {
        let has_already_processed = self
            .tabulation_problem
            .path_edges()
            .has_already_processed(&next_edge);
        self.register_edge(next_edge.clone(), prev_edge);

        if !has_already_processed {
            self.propagation_count += 1;
            self.schedule_edge_processing(next_edge);
        }

        return has_already_processed;
    }

    #[inline]
    pub fn register_edge(&mut self, next_edge: PathEdge<N, D>, prev_edge: &PathEdge<N, D>) {
        self.on_register(&next_edge);
        self.tabulation_problem.add_flow_edge(
            prev_edge.get_target_node().clone(),
            next_edge.get_target_node().clone(),
        );
        self.tabulation_problem.register(next_edge);
    }

    #[inline]
    pub fn on_register(&mut self, _edge: &PathEdge<N, D>) {
        // We can do some check here
    }

    fn schedule_edge_processing(&mut self, edge: PathEdge<N, D>) {
        self.worklist.push_back(edge);
    }

    pub fn process_path_edge(&mut self, edge: &PathEdge<N, D>) {
        if self.icfg().is_call_node(edge.get_target()) {
            self.process_call(edge);
        } else {
            if self.icfg().is_exit_node(edge.get_target()) {
                self.process_exit(edge);
            }
            if !self.icfg().get_succs_of(edge.get_target()).is_empty() {
                self.process_normal_flow(edge);
            }
        }
    }

    pub fn end_summary(&self, func: F, start_node: &(N, D)) -> Option<Vec<PathEdge<N, D>>> {
        self.tabulation_problem
            .summaries()
            .end_summary(func, start_node)
            .cloned()
    }

    fn add_end_summary(&mut self, f: F, edge: PathEdge<N, D>) {
        let func = self.icfg().get_function_of(edge.get_target());
        let start_points = self.icfg().get_start_points_of(func);
        if !start_points.contains(&edge.get_start()) {
            return;
        }
        self.tabulation_problem.summaries_mut().add_end_summary(f, edge);
    }

    pub fn incoming(&self, pair: &(N, D), func: F) -> Option<Vec<PathEdge<N, D>>> {
        self.tabulation_problem
            .incomings()
            .incoming(pair, func)
            .cloned()
    }

    pub fn add_incoming(
        &mut self,
        callee: F,
        next_call_edge: PathEdge<N, D>,
        inc_edge: PathEdge<N, D>,
    ) -> bool {
        self.on_register(&inc_edge);
        self.tabulation_problem.on_solver_add_incoming(
            callee,
            next_call_edge.get_start_node(),
            &inc_edge,
        );
        self.tabulation_problem.add_flow_edge(
            inc_edge.get_target_node().clone(),
            next_call_edge.get_target_node().clone(),
        );
        self.tabulation_problem.incomings_mut().add_incoming(
            callee,
            next_call_edge.get_start_node().clone(),
            inc_edge,
        )
    }
}

pub enum PropagationType {
    Normal,
    Call2Return,
    CallEnter,
    BalancedReturn,
    UnbalancedReturn,
}
