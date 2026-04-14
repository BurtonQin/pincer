use rustc_middle::mir;
use smallvec::{smallvec, SmallVec};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::forward::forward_flow_functions::{kill_source, ForwardFlowFunctions};
use crate::infoflow::ifds::function_call_handler::{FunctionCallHandler, FunctionCallStubs};
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::{self, points_of_aliasing, Unit};
use crate::mir::builtins::{self, is_realloc, realloc_arg_and_dst, FunctionEffect};
use crate::mir::function::FuncDef;

type Edge<'tcx> = PathEdge<Unit<'tcx>, AccessPath<'tcx>>;
type Edges<'tcx> = SmallVec<[Edge<'tcx>; 1]>;

/// Creates an identity edge: the fact passes through unchanged.
fn identity_edge<'tcx>(prev_edge: &Edge<'tcx>, return_site: Unit<'tcx>) -> Edge<'tcx> {
    PathEdge::new(
        prev_edge.get_start(),
        *prev_edge.fact_at_source(),
        return_site,
        *prev_edge.fact_at_target(),
    )
}

/// Creates a FunctionCallStubs with all forward-analysis handlers registered.
pub fn forward_call_stubs<'analysis, 'tcx>(
    acx: &'analysis AnalysisContext<'tcx>,
) -> FunctionCallStubs<'analysis, 'tcx, Unit<'tcx>, AccessPath<'tcx>> {
    FunctionCallStubs::new(vec![
        Box::new(ForwardReallocHandler::new(acx)),
        Box::new(ForwardEffectsHandler::new(acx)),
    ])
}

// --- ForwardReallocHandler ---

struct ForwardReallocHandler<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
}

impl<'analysis, 'tcx> ForwardReallocHandler<'analysis, 'tcx> {
    fn new(acx: &'analysis AnalysisContext<'tcx>) -> Self {
        ForwardReallocHandler { acx }
    }
}

impl<'analysis, 'tcx> FunctionCallHandler<'tcx, Unit<'tcx>, AccessPath<'tcx>>
    for ForwardReallocHandler<'analysis, 'tcx>
{
    fn can_handle(&self, callee: FuncDef<'tcx>) -> bool {
        is_realloc(self.acx, callee)
    }

    fn handle(
        &self,
        prev_edge: &Edge<'tcx>,
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> Edges<'tcx> {
        let d2 = prev_edge.fact_at_target();
        let (ptr_dest, ptr_arg) =
            realloc_arg_and_dst(self.acx, callsite, callee).unwrap();

        match &ptr_arg {
            mir::Operand::Copy(arg) | mir::Operand::Move(arg) => {
                if d2.is_projection_of(self.acx, arg) {
                    let dtarget = d2.derive_with_new_base(self.acx, arg, &ptr_dest);
                    return smallvec![PathEdge::new(
                        prev_edge.get_start(),
                        *prev_edge.fact_at_source(),
                        return_site,
                        dtarget,
                    )];
                }
            }
            _ => {}
        }

        smallvec![identity_edge(prev_edge, return_site)]
    }
}

// --- ForwardEffectsHandler ---

struct ForwardEffectsHandler<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
    flow_fns: ForwardFlowFunctions<'analysis, 'tcx>,
}

impl<'analysis, 'tcx> ForwardEffectsHandler<'analysis, 'tcx> {
    fn new(acx: &'analysis AnalysisContext<'tcx>) -> Self {
        ForwardEffectsHandler {
            acx,
            flow_fns: ForwardFlowFunctions::new(acx),
        }
    }

    /// Converts effect results into path edges, expanding POA aliases for each
    /// new active fact produced by the effect.
    fn expand_poa(
        &self,
        prev_edge: &Edge<'tcx>,
        d2: &AccessPath<'tcx>,
        results: &SmallVec<[AccessPath<'tcx>; 1]>,
        return_site: Unit<'tcx>,
        callsite: Unit<'tcx>,
    ) -> Edges<'tcx> {
        let mut out: Edges<'tcx> = results
            .iter()
            .map(|fact| PathEdge::new(
                prev_edge.get_start(),
                *prev_edge.fact_at_source(),
                return_site,
                *fact,
            ))
            .collect();
        for target in results {
            if target != d2 && !target.is_inactive() {
                let poa_aliases = if self.flow_fns.is_store_poa_pending(target) {
                    points_of_aliasing::load_or_store::process_load_or_store_poa(
                        self.acx, target, callsite,
                    )
                } else {
                    points_of_aliasing::address_taken::process_address_taken_poa(
                        self.acx, target, callsite,
                    )
                };
                for alias in poa_aliases {
                    if infoflow::retain_access_path(self.acx, &alias) {
                        out.push(PathEdge::new(
                            prev_edge.get_start(),
                            *prev_edge.fact_at_source(),
                            return_site,
                            alias,
                        ));
                    }
                }
            }
        }
        out
    }

    /// Apply configured function effects for a MIR-unavailable callee.
    /// Returns `Some(results)` if an effect matched, `None` otherwise.
    fn apply_function_effects(
        &self,
        source: &AccessPath<'tcx>,
        effects: &[FunctionEffect],
        args: &[mir::Operand<'tcx>],
        destination: &mir::Place<'tcx>,
        callsite: Unit<'tcx>,
    ) -> Option<SmallVec<[AccessPath<'tcx>; 1]>> {
        let tcx = self.acx.tcx;
        for effect in effects {
            match effect {
                FunctionEffect::Copy { from_arg } | FunctionEffect::Move { from_arg } => {
                    let Some(mir::Operand::Copy(p) | mir::Operand::Move(p)) = args.get(*from_arg) else { continue };
                    if source.is_projection_of(self.acx, p) {
                        return Some(self.flow_fns.compute_move_or_copy_targets(source, destination, &args[*from_arg], callsite));
                    }
                }
                FunctionEffect::Load { from_arg } => {
                    let Some(mir::Operand::Copy(p) | mir::Operand::Move(p)) = args.get(*from_arg) else { continue };
                    let deref_p = tcx.mk_place_deref(*p);
                    if source.is_projection_of(self.acx, &deref_p) {
                        let synthetic_op = mir::Operand::Copy(deref_p);
                        return Some(self.flow_fns.compute_move_or_copy_targets(source, destination, &synthetic_op, callsite));
                    }
                }
                FunctionEffect::Store { to_arg, from_arg } => {
                    let Some(mir::Operand::Copy(to_p) | mir::Operand::Move(to_p)) = args.get(*to_arg) else { continue };
                    let deref_to = tcx.mk_place_deref(*to_p);
                    if let Some(from_idx) = from_arg {
                        let Some(mir::Operand::Copy(from_p) | mir::Operand::Move(from_p)) = args.get(*from_idx) else { continue };
                        if source.is_projection_of(self.acx, from_p) {
                            return Some(self.flow_fns.compute_move_or_copy_targets(source, &deref_to, &args[*from_idx], callsite));
                        }
                    }
                }
                _ => continue,
            }
        }
        None
    }
}

impl<'analysis, 'tcx> FunctionCallHandler<'tcx, Unit<'tcx>, AccessPath<'tcx>>
    for ForwardEffectsHandler<'analysis, 'tcx>
{
    fn can_handle(&self, callee: FuncDef<'tcx>) -> bool {
        !self.acx.tcx.is_mir_available(callee.def_id)
            && builtins::function_effects(self.acx.tcx, callee.def_id).is_some()
    }

    fn handle(
        &self,
        prev_edge: &Edge<'tcx>,
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> Edges<'tcx> {
        self.flow_fns.clear_store_poa_pending();
        let d2 = prev_edge.fact_at_target();
        let tcx = self.acx.tcx;
        let (args, destination) = callsite.args_and_destination(tcx);

        // 1. Inactive facts pass through unchanged.
        if d2.is_inactive() {
            return smallvec![identity_edge(prev_edge, return_site)];
        }

        // 2. Heap pointer: handle alloc trace.
        if d2.is_heap_pointer() {
            if *d2.alloc_trace.unwrap().last().unwrap() == callsite {
                if d2.alloc_trace.unwrap().len() == 1 {
                    return smallvec![PathEdge::new(
                        prev_edge.get_start(),
                        *prev_edge.fact_at_source(),
                        return_site,
                        d2.pop_alloc_trace(),
                    )];
                } else {
                    return SmallVec::new();
                }
            }
            return smallvec![identity_edge(prev_edge, return_site)];
        }

        // 3. Destination kill: deactivate facts rooted at the call destination.
        if d2.is_projection_of(self.acx, &destination) {
            return if kill_source(self.acx, d2, &destination) {
                let deactivated = d2.deactivate_at(callsite.location);
                smallvec![PathEdge::new(
                    prev_edge.get_start(),
                    *prev_edge.fact_at_source(),
                    return_site,
                    deactivated,
                )]
            } else {
                smallvec![identity_edge(prev_edge, return_site)]
            };
        }

        // 4. Apply configured effects with POA expansion.
        let effects = builtins::function_effects(tcx, callee.def_id).unwrap();
        if let Some(results) = self.apply_function_effects(d2, effects, &args, &destination, callsite) {
            return self.expand_poa(prev_edge, d2, &results, return_site, callsite);
        }

        // 5. No effect matched — pass through.
        smallvec![identity_edge(prev_edge, return_site)]
    }
}
