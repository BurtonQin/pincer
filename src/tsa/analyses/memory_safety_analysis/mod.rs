use log::*;
use rustc_middle::mir::{BasicBlock, Operand, Place};
use rustc_middle::ty::TyCtxt;
use std::collections::{HashMap, HashSet};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::{self, query::Query};
use crate::infoflow::arg_param_pairs;
use crate::infoflow::backward::backward_solver::BackwardSolver;
use crate::infoflow::cfg::{
    interprocedural_cfg::InterproceduralCFG,
    CFGConfig, CFGQueries,
};
#[cfg(feature = "msa_with_bbcfg")]
use crate::infoflow::cfg::block_cfg::{BBCFGNode, BasicBlockCFG};
#[cfg(not(feature = "msa_with_bbcfg"))]
use crate::infoflow::cfg::infoflow_cfg::InfoflowCFG;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::forward::forward_solver::ForwardSolver;
use crate::infoflow::ifds::flow_graph::FlowGraph;
use crate::infoflow::FlowOriginKind;
use crate::mir::function::FuncDef;
use crate::mir::unit::Unit;
use crate::tsa::aliasing_xor_mutability::is_axm_compliant;
use crate::tsa::analyses::memory_safety_analysis::{
    null_state::NullState, null_state_transition::NullStateTransition,
    vulnerable_pointer::VulnerablePointer,
};
use crate::tsa::state::TypeState;
use crate::tsa::tsa_flow_functions::TypeStateAnalysisFlowFunctions;
use crate::tsa::tsa_solver::TypeStateAnalysisSolver;
use crate::tsa::{initial_seed, TSAPathEdge, TSAPathEdgeData, TSAPathEdgeNode};
use crate::infoflow::ifds::flow_functions::FlowFunctions;
use crate::util::type_util;

pub mod null_state;
pub mod null_state_transition;
pub mod vulnerable_pointer;

/// CFG configuration for memory safety analysis.
/// `dummy_resume` captures unwind paths via a synthetic resume node, ensuring
/// drop and panic unwind edges are visible to the analysis.
/// `model_drop_calls` treats `Drop` terminators as interprocedural call sites,
/// allowing the analysis to track pointer states through destructor bodies.
const MSA_CFG_CONFIG: CFGConfig = CFGConfig { dummy_resume: true, model_drop_calls: true };

pub struct MemorySafetyAnalysisInner<'analysis, 'cfg, 'tcx, N, I>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
{
    solver: TypeStateAnalysisSolver<
        'analysis,
        'cfg,
        'tcx,
        N,
        I,
        NullState,
        NullStateTransition<'analysis, 'tcx>,
    >,
    seeds: HashSet<(N, TSAPathEdgeData<'tcx, NullState>)>,
    error_seeds: HashSet<(N, TSAPathEdgeData<'tcx, NullState>)>,
    analyzed_functions: HashSet<FuncDef<'tcx>>,
}

impl<'analysis, 'cfg, 'tcx, N, I> MemorySafetyAnalysisInner<'analysis, 'cfg, 'tcx, N, I>
where
    'analysis: 'cfg,
    N: TSAPathEdgeNode<'tcx> + 'analysis,
    I: CFGQueries<'tcx, N> + InterproceduralCFG<N, FuncDef<'tcx>>,
{
    /// Generic constructor — caller supplies the CFG reference directly.
    pub fn new_inner(acx: &'analysis AnalysisContext<'tcx>, icfg: &'cfg I) -> Self {
        let trans = NullStateTransition::new(acx);
        let solver = TypeStateAnalysisSolver::new(acx, icfg, trans);
        Self {
            solver,
            seeds: HashSet::new(),
            error_seeds: HashSet::new(),
            analyzed_functions: HashSet::new(),
        }
    }

    fn icfg(&self) -> &I {
        self.solver.tabulation_problem().icfg
    }

    pub fn acx(&self) -> &'analysis AnalysisContext<'tcx> {
        self.solver.acx
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.solver.acx.tcx
    }

    pub fn get_flow_graph(
        &self,
    ) -> &FlowGraph<'cfg, N, TSAPathEdgeData<'tcx, NullState>, FuncDef<'tcx>, I> {
        self.solver.tabulation_problem().flow_graph()
    }

    pub fn error_seeds(&self) -> &HashSet<(N, TSAPathEdgeData<'tcx, NullState>)> {
        &self.error_seeds
    }

    pub fn analyzed_functions(&self) -> &HashSet<FuncDef<'tcx>> {
        &self.analyzed_functions
    }

    pub fn report(&self) {
        if self.error_seeds.is_empty() {
            println!("No bug detected.");
        } else {
            println!("{:?} Bug(s) detected.", self.error_seeds.len());
        }
        for (i, error_seed) in self.error_seeds.iter().enumerate() {
            println!("Error seed #{}: {:?} in {:?}", i + 1, error_seed, error_seed.0.containing_function().def_id);
            // self.print_flow_paths_with_error_states(error_seed.clone());
        }
    }

    pub fn analyze_vulnerable_pointer(&mut self, vulnerable_pointer: VulnerablePointer<'tcx>) {
        self.analyzed_functions.insert(vulnerable_pointer.unit.func);
        info!(
            "Analyzing vulnerable pointer: {:?} in {:?}",
            vulnerable_pointer, vulnerable_pointer.unit.func
        );
        let mut bw_solver = BackwardSolver::new(self.solver.acx);
        let flow_origins = aliasing::find_flow_origins(
            self.solver.acx,
            &mut bw_solver,
            Query::new(vulnerable_pointer.ptr_path, vulnerable_pointer.unit),
        );
        info!("Flow origins: {:?}", flow_origins);
        let curr_func = vulnerable_pointer.unit.func;
        for flow_origin in flow_origins {
            match flow_origin.kind {
                FlowOriginKind::Parameter(origin_path) => {
                    let start_unit =
                        Unit::new(curr_func, BasicBlock::from_usize(0).start_location());
                    self.start_analysis(origin_path, start_unit, false);
                }
                FlowOriginKind::Allocation { path, .. } => {
                    let alloc_site = path.get_alloc_site().unwrap();
                    if alloc_site.func == curr_func {
                        self.start_analysis(path.discard_alloc_trace(), alloc_site, true);
                    } else {
                        let seeds = self.initial_seeds_for_interprocedural_alloc(
                            path,
                            vulnerable_pointer.unit,
                            &mut bw_solver,
                        );
                        info!("Initial seeds: {:?}", seeds);
                        for seed in seeds {
                            self.start_analysis_from_seed(seed, false);
                        }
                    }
                }
                _ => {}
            }
        }
    }

    pub fn start_analysis(
        &mut self,
        path: AccessPath<'tcx>,
        start_unit: Unit<'tcx>,
        skip_start: bool,
    ) {
        let init_state = NullState::NonNull;
        let seed = initial_seed(
            self.solver.tcx(),
            HashSet::from([path]),
            init_state,
            start_unit,
        );
        self.start_analysis_from_seed(seed, skip_start);
    }

    pub fn start_analysis_from_seed(
        &mut self,
        seed: (N, TSAPathEdgeData<'tcx, NullState>),
        skip_start: bool,
    ) {
        self.seeds.insert(seed.clone());
        self.solver.start_propagation(seed.clone(), skip_start);

        if !self.end_with_error_states(&seed).is_empty() {
            self.error_seeds.insert(seed.clone());
        } else {
            self.continue_analysis(&seed);
        }
    }

    fn continue_analysis(
        &mut self,
        seed: &(N, TSAPathEdgeData<'tcx, NullState>),
    ) {
        if self.continue_analysis_in_callers(seed) {
            let start_node = seed.0;
            let param_origin = is_entry_node(start_node);
            let curr_func = start_node.containing_function();
            for caller in self.icfg().get_callers_of(curr_func) {
                let callsite_unit = caller.as_callsite();
                let caller_func = caller.containing_function();
                if self.tcx().is_mir_available(caller_func.def_id) {
                    let arg_param_pairs = arg_param_pairs(self.acx(), callsite_unit, curr_func);

                    if param_origin {
                        info!(
                            "Continue analysis in caller {:?} from {:?}",
                            caller_func, curr_func
                        );
                        assert!(seed.1.aliases().len() == 1);
                        let origin_ptr = seed.1.aliases().iter().next().unwrap();
                        for (arg, param) in arg_param_pairs.iter() {
                            if origin_ptr.is_projection_of(self.acx(), param) {
                                if let Operand::Copy(arg_place) | Operand::Move(arg_place) = arg {
                                    let source = origin_ptr.derive_with_new_base_in_func(
                                        self.acx(),
                                        param,
                                        arg_place,
                                        caller_func,
                                    );
                                    let vulnerable_pointer = VulnerablePointer {
                                        ptr_path: source,
                                        unit: callsite_unit,
                                    };
                                    self.analyze_vulnerable_pointer(vulnerable_pointer);
                                    break;
                                }
                            }
                        }
                    } else {
                        let end_edges = self.end_edges(seed);
                        let callsite_node = N::from_unit(self.tcx(), callsite_unit);
                        let return_sites =
                            self.icfg().get_return_sites_of_call_at(callsite_node);
                        // Collect seeds before dropping tsa_flow_functions so we can mutably borrow self.
                        let new_seeds: Vec<_> = {
                            let tsa_flow_functions = TypeStateAnalysisFlowFunctions::new(
                                self.acx(),
                                self.icfg(),
                                NullStateTransition::new(self.acx()),
                            );
                            end_edges
                                .iter()
                                .flat_map(|(end_point, edges)| {
                                    edges
                                        .iter()
                                        .filter(|edge| {
                                            edge.fact_at_target().get_type_state().is_null()
                                        })
                                        .flat_map(|edge| {
                                            return_sites.iter().flat_map(|return_site| {
                                                let f = tsa_flow_functions
                                                    .get_return_flow_function(
                                                        edge,
                                                        None,
                                                        callsite_node,
                                                        end_point.containing_function(),
                                                        *return_site,
                                                    );
                                                let out_states = f(&edge.fact_at_target());
                                                out_states
                                                    .into_iter()
                                                    .filter(|s| !s.aliases().is_empty())
                                                    .map(|out_state| (*return_site, out_state))
                                                    .collect::<Vec<_>>()
                                            })
                                            .collect::<Vec<_>>()
                                        })
                                        .collect::<Vec<_>>()
                                })
                                .collect()
                        };
                        for seed in new_seeds {
                            info!(
                                "Continue analysis in caller {:?} from {:?}, initial seed: {:?}",
                                caller_func, curr_func, seed
                            );
                            self.start_analysis_from_seed(seed, false);
                        }
                    }
                }
            }
        }
    }

    fn continue_analysis_in_callers(
        &self,
        seed: &(N, TSAPathEdgeData<'tcx, NullState>),
    ) -> bool {
        let result_aliases = |arg_count: usize, aliases: &HashSet<AccessPath<'tcx>>| {
            let mut ret = HashSet::new();
            for alias in aliases {
                if alias.has_ref_elem() && !alias.is_indirect() {
                    continue;
                }
                if alias.local.index() <= arg_count {
                    ret.insert(alias.clone());
                }
            }
            ret
        };

        let func = seed.0.containing_function();
        if !self.tcx().is_mir_available(func.def_id) {
            return false;
        }
        let arg_count = self.tcx().optimized_mir(func.def_id).arg_count;
        for (_end_point, edges) in self.end_edges(seed) {
            for edge in edges {
                let result_aliases = result_aliases(arg_count, edge.fact_at_target().aliases());
                trace!("End edge: {:?}, seed: {:?}", edge, seed);
                let start_node = edge.get_start();
                let param_origin = is_entry_node(start_node);

                if edge.fact_at_target().get_type_state().is_null() {
                    if param_origin || !result_aliases.is_empty() {
                        return true;
                    }
                    if let Some(alias) = result_aliases.iter().next() {
                        let local_ty = type_util::place_ty(
                            self.tcx(),
                            &Place::from(alias.local),
                            func,
                        );
                        if !local_ty.is_trivially_pure_clone_copy() {
                            return true;
                        }
                    }
                }

                if edge.fact_at_target().get_type_state().is_non_null() {
                    let origin_ptr =
                        edge.fact_at_source().aliases().iter().next().unwrap();
                    if !param_origin {
                        if result_aliases.len() > 1 {
                            return true;
                        }
                    } else {
                        assert!(origin_ptr.local.index() <= arg_count);
                        if result_aliases.iter().all(|alias| alias.local == origin_ptr.local) {
                            continue;
                        }
                        if !self.acx().analysis_options.msa_axm_check {
                            return true;
                        }
                        if !is_axm_compliant(self.acx(), origin_ptr.clone(), &result_aliases) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    pub fn find_intraprocedural_flow_paths_from(
        &self,
        node: (N, TSAPathEdgeData<'tcx, NullState>),
    ) -> HashSet<Vec<(N, TSAPathEdgeData<'tcx, NullState>)>> {
        self.get_flow_graph()
            .find_intraprocedural_flow_paths_from(node)
    }

    pub fn print_flow_paths_with_error_states(
        &self,
        node: (N, TSAPathEdgeData<'tcx, NullState>),
    ) {
        let all_paths = self.find_intraprocedural_flow_paths_from(node);
        let mut paths_with_error = HashSet::new();
        for path in all_paths {
            let first_error_index = path
                .iter()
                .position(|node| node.1.get_type_state().is_error_state());
            if let Some(index) = first_error_index {
                paths_with_error.insert((path[..index].to_vec(), path[index].1.clone()));
            }
        }
        println!("Paths with error states:");
        for (path, state) in paths_with_error {
            let mut path_string = String::new();
            for (i, node) in path.iter().enumerate() {
                if i > 0 {
                    path_string.push_str(" -> ");
                }
                path_string.push_str(&format!("{:?}", node));
            }
            path_string.push_str(&format!(" -> {:?}", state));

            println!("\t{}", path_string);
        }
    }

    /// For a vulnerable pointer that originates from an allocation site outside of the
    /// current function, we start a forward analysis from the allocation site to find
    /// the start unit in current function that the vulnerable pointer flows from,
    /// i.e. the call site that leads to the allocation site. We create the initial
    /// seed by finding out all the pointers that originate from the same source at the
    /// start unit.
    ///
    /// For example, in the following code:
    /// ```text
    /// fn main() {
    ///     let mut v = Vec::new();
    ///     let r = &mut v;
    ///     r.push(1);
    ///     let ptr = v.as_mut_ptr();
    /// }
    /// ```
    ///
    /// Given the vulnerable pointer `ptr`, our backward analysis finds that it points to
    /// a heap object allocated in `grow` transitively called from `push`. We start a forward
    /// analysis from the allocation site, determining that the pointer flow starts from
    /// `push` in `main`, and after the call to `push`, there are two pointers `v.ptr` and
    /// `(*r).ptr` that originate from the same source as `ptr`.
    fn initial_seeds_for_interprocedural_alloc(
        &self,
        ptr_path: AccessPath<'tcx>,
        query_unit: Unit<'tcx>,
        bw_solver: &mut BackwardSolver<'analysis, 'cfg, 'tcx>,
    ) -> HashSet<(N, TSAPathEdgeData<'tcx, NullState>)> {
        assert_ne!(ptr_path.get_alloc_site().unwrap().func, query_unit.func);
        let mut seeds = HashSet::new();
        let alloc_from = *ptr_path.alloc_trace.unwrap().last().unwrap();
        let seed_unit = alloc_from.call_succ_unit(self.solver.tcx()).unwrap();
        let mut pts_solver = ForwardSolver::new(self.solver.acx);
        let start_units = pts_solver
            .solver
            .icfg()
            .get_start_points_of(query_unit.func);
        let start_unit = *start_units.first().unwrap();
        pts_solver.start_propagation_along_path(
            ptr_path,
            start_unit,
            seed_unit,
            bw_solver.incomings(),
            true,
        );
        let mut init_aliases = HashSet::new();
        if let Some(path_edges) = pts_solver.path_edges_at_stmt(seed_unit) {
            for path_edge in path_edges {
                let ptr = path_edge.fact_at_target().clone();
                if !ptr.is_inactive() {
                    init_aliases.insert(ptr);
                }
            }
        }
        if !init_aliases.is_empty() {
            let seed = initial_seed(
                self.solver.tcx(),
                init_aliases,
                NullState::NonNull,
                Unit::new(query_unit.func, seed_unit.location),
            );
            seeds.insert(seed);
        }

        seeds
    }

    /// Determine if the initial seed will lead to an error state at
    /// an end point of the current function.
    fn end_with_error_states(
        &self,
        seed: &(N, TSAPathEdgeData<'tcx, NullState>),
    ) -> HashSet<(N, TSAPathEdgeData<'tcx, NullState>)> {
        let mut error_states = HashSet::new();
        let end_edges = self.end_edges(seed);
        for (_end_point, edges) in end_edges.iter() {
            for edge in edges {
                if edge.fact_at_target().get_type_state().is_error_state()
                    && *edge.get_start_node() == *seed
                {
                    error_states.insert(edge.get_target_node().clone());
                }
            }
        }
        error_states
    }

    fn end_edges(
        &self,
        seed: &(N, TSAPathEdgeData<'tcx, NullState>),
    ) -> HashMap<N, HashSet<TSAPathEdge<'tcx, NullState, N>>> {
        let mut end_edges: HashMap<N, HashSet<TSAPathEdge<'tcx, NullState, N>>> = HashMap::new();
        let func = seed.0.containing_function();
        let end_points = self.icfg().get_end_points_of(func);
        for end_point in end_points {
            if let Some(edges) = self
                .solver
                .tabulation_problem()
                .path_edges
                .path_edges_at_stmt(end_point, func)
            {
                for edge in edges {
                    if edge.get_start_node() == seed {
                        end_edges
                            .entry(end_point)
                            .or_default()
                            .insert(edge.clone());
                    }
                }
            }
        }
        end_edges
    }
}

/// Returns true when `n` represents the function entry point (BB 0, statement 0).
/// Uses `TSAPathEdgeNode::as_unit()` so no new trait method is needed.
fn is_entry_node<'tcx, N: TSAPathEdgeNode<'tcx>>(n: N) -> bool {
    let loc = n.as_unit().location;
    loc.block == BasicBlock::ZERO && loc.statement_index == 0
}


#[cfg(feature = "msa_with_bbcfg")]
pub type MemorySafetyAnalysis<'analysis, 'cfg, 'tcx> =
    MemorySafetyAnalysisInner<'analysis, 'cfg, 'tcx, BBCFGNode<'tcx>, BasicBlockCFG<'tcx>>;

#[cfg(feature = "msa_with_bbcfg")]
impl<'analysis: 'cfg, 'cfg, 'tcx>
    MemorySafetyAnalysisInner<'analysis, 'cfg, 'tcx, BBCFGNode<'tcx>, BasicBlockCFG<'tcx>>
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> Self {
        Self::new_inner(acx, acx.get_bb_cfg(MSA_CFG_CONFIG))
    }
}

#[cfg(not(feature = "msa_with_bbcfg"))]
pub type MemorySafetyAnalysis<'analysis, 'cfg, 'tcx> =
    MemorySafetyAnalysisInner<'analysis, 'cfg, 'tcx, Unit<'tcx>, InfoflowCFG<'tcx>>;

#[cfg(not(feature = "msa_with_bbcfg"))]
impl<'analysis: 'cfg, 'cfg, 'tcx>
    MemorySafetyAnalysisInner<'analysis, 'cfg, 'tcx, Unit<'tcx>, InfoflowCFG<'tcx>>
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> Self {
        Self::new_inner(acx, acx.get_fw_icfg(MSA_CFG_CONFIG))
    }
}
