use rustc_middle::mir;
use smallvec::{smallvec, SmallVec};

use crate::analysis_context::AnalysisContext;
use crate::infoflow;
use crate::infoflow::backward::backward_flow_functions::BackwardFlowFunctions;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::function_call_handler::{FunctionCallHandler, FunctionCallStubs};
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::{is_alloc, is_realloc, points_of_aliasing, realloc_arg_and_dst, Unit};
use crate::mir::builtins::{self, FunctionEffect};
use crate::mir::function::FuncDef;

type Edge<'tcx> = PathEdge<Unit<'tcx>, AccessPath<'tcx>>;
type Edges<'tcx> = SmallVec<[Edge<'tcx>; 1]>;

pub fn backward_call_stubs<'analysis, 'tcx>(
    acx: &'analysis AnalysisContext<'tcx>,
) -> FunctionCallStubs<'analysis, 'tcx, Unit<'tcx>, AccessPath<'tcx>> {
    FunctionCallStubs::new(vec![
        Box::new(BackwardAllocHandler { acx }),
        Box::new(BackwardReallocHandler { acx }),
        Box::new(BackwardEffectsHandler::new(acx)),
    ])
}

/// Creates an identity edge: the fact passes through unchanged.
fn identity_edge<'tcx>(prev_edge: &Edge<'tcx>, return_site: Unit<'tcx>) -> Edge<'tcx> {
    PathEdge::new(
        prev_edge.get_start(),
        *prev_edge.fact_at_source(),
        return_site,
        *prev_edge.fact_at_target(),
    )
}

/// If the tracked fact is inactive, propagate it (activating at its deactivation
/// point if reached). Returns `None` when the fact is active and needs handling.
fn propagate_inactive<'tcx>(
    prev_edge: &Edge<'tcx>,
    callsite: Unit<'tcx>,
    return_site: Unit<'tcx>,
) -> Option<Edges<'tcx>> {
    let d2 = prev_edge.fact_at_target();
    if !d2.is_inactive() {
        return None;
    }
    if d2.deactivation_point == Some(callsite.location) {
        Some(smallvec![PathEdge::new(
            prev_edge.get_start(),
            *prev_edge.fact_at_source(),
            return_site,
            d2.activate(),
        )])
    } else {
        Some(smallvec![identity_edge(prev_edge, return_site)])
    }
}

// --- BackwardAllocHandler ---

struct BackwardAllocHandler<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
}

impl<'analysis, 'tcx> FunctionCallHandler<'tcx, Unit<'tcx>, AccessPath<'tcx>>
    for BackwardAllocHandler<'analysis, 'tcx>
{
    fn can_handle(&self, callee: FuncDef<'tcx>) -> bool {
        is_alloc(self.acx, callee)
    }

    /// For an alloc call, if the tracked access path is rooted at the call
    /// destination, tag it with this allocation site. Otherwise pass through.
    fn handle(
        &self,
        prev_edge: &Edge<'tcx>,
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        _callee: FuncDef<'tcx>,
    ) -> Edges<'tcx> {
        if let Some(edges) = propagate_inactive(prev_edge, callsite, return_site) {
            return edges;
        }

        let d2 = prev_edge.fact_at_target();
        let call_dest = callsite.call_destination(self.acx.tcx);

        if d2.is_projection_of(self.acx, &call_dest) {
            if !d2.is_indirect() {
                // Direct projection of the alloc result — tag with allocation site.
                let heap_ptr = d2.with_alloc_site(self.acx, callsite);
                return smallvec![PathEdge::new(
                    prev_edge.get_start(),
                    *prev_edge.fact_at_source(),
                    return_site,
                    heap_ptr,
                )];
            } else {
                assert!(!d2.has_ref_elem());
                return SmallVec::new();
            }
        }

        smallvec![identity_edge(prev_edge, return_site)]
    }
}

// --- BackwardReallocHandler ---

struct BackwardReallocHandler<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
}

impl<'analysis, 'tcx> FunctionCallHandler<'tcx, Unit<'tcx>, AccessPath<'tcx>>
    for BackwardReallocHandler<'analysis, 'tcx>
{
    fn can_handle(&self, callee: FuncDef<'tcx>) -> bool {
        is_realloc(self.acx, callee)
    }

    /// For a realloc call, if the tracked access path is rooted at the result
    /// destination, rebase it onto the source pointer argument.
    fn handle(
        &self,
        prev_edge: &Edge<'tcx>,
        callsite: Unit<'tcx>,
        return_site: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> Edges<'tcx> {
        if let Some(edges) = propagate_inactive(prev_edge, callsite, return_site) {
            return edges;
        }

        let d2 = prev_edge.fact_at_target();

        if let Some((dest, arg)) = realloc_arg_and_dst(self.acx, callsite, callee) {
            if d2.is_projection_of(self.acx, &dest) {
                if let mir::Operand::Copy(place) | mir::Operand::Move(place) = &arg {
                    let rebased = d2.derive_with_new_base(self.acx, &dest, place);
                    return smallvec![PathEdge::new(
                        prev_edge.get_start(),
                        *prev_edge.fact_at_source(),
                        return_site,
                        rebased,
                    )];
                }
            }
        }

        smallvec![identity_edge(prev_edge, return_site)]
    }
}

// --- BackwardEffectsHandler ---

struct BackwardEffectsHandler<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
    flow_fns: BackwardFlowFunctions<'analysis, 'tcx>,
}

impl<'analysis, 'tcx> BackwardEffectsHandler<'analysis, 'tcx> {
    fn new(acx: &'analysis AnalysisContext<'tcx>) -> Self {
        BackwardEffectsHandler {
            acx,
            flow_fns: BackwardFlowFunctions::new(acx),
        }
    }

    /// Converts effect results into path edges, expanding POA aliases for each
    /// new fact when the original fact is active.
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
            if target != d2 && !d2.is_inactive() {
                let poa_aliases = if self.flow_fns.is_load_poa_pending(target) {
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
                    if source.is_projection_of(self.acx, destination) {
                        let Some(op) = args.get(*from_arg) else { continue };
                        return Some(self.flow_fns.compute_move_or_copy_targets(source, destination, op, callsite));
                    }
                }
                FunctionEffect::Load { from_arg } => {
                    if source.is_projection_of(self.acx, destination) {
                        let Some(mir::Operand::Copy(p) | mir::Operand::Move(p)) = args.get(*from_arg) else { continue };
                        let synthetic_op = mir::Operand::Copy(tcx.mk_place_deref(*p));
                        return Some(self.flow_fns.compute_move_or_copy_targets(source, destination, &synthetic_op, callsite));
                    }
                }
                FunctionEffect::Store { to_arg, from_arg } => {
                    let Some(mir::Operand::Copy(to_p) | mir::Operand::Move(to_p)) = args.get(*to_arg) else { continue };
                    let deref_to = tcx.mk_place_deref(*to_p);
                    if source.is_projection_of(self.acx, &deref_to) {
                        if let Some(from_idx) = from_arg {
                            let Some(op) = args.get(*from_idx) else { continue };
                            return Some(self.flow_fns.compute_move_or_copy_targets(source, &deref_to, op, callsite));
                        }
                        // Kill: overwritten with no known source
                        return Some(smallvec![]);
                    }
                }
                _ => continue,
            }
        }
        None
    }
}

impl<'analysis, 'tcx> FunctionCallHandler<'tcx, Unit<'tcx>, AccessPath<'tcx>>
    for BackwardEffectsHandler<'analysis, 'tcx>
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
        self.flow_fns.clear_load_poa_pending();
        let d2 = prev_edge.fact_at_target();
        let tcx = self.acx.tcx;
        let (args, destination) = callsite.args_and_destination(tcx);

        // 1. Inactive facts: activate at deactivation point or pass through.
        if let Some(edges) = propagate_inactive(prev_edge, callsite, return_site) {
            return edges;
        }

        // 2. Heap pointers pass through.
        if d2.is_heap_pointer() {
            return smallvec![identity_edge(prev_edge, return_site)];
        }

        // 3. Apply configured effects with POA expansion (checked before destination
        //    kill so that Copy/Move/Load effects matching the destination are handled first).
        let effects = builtins::function_effects(tcx, callee.def_id).unwrap();
        if let Some(results) = self.apply_function_effects(d2, effects, &args, &destination, callsite) {
            return self.expand_poa(prev_edge, d2, &results, return_site, callsite);
        }

        // 4. Destination kill: facts rooted at the call destination are killed.
        if d2.is_projection_of(self.acx, &destination) {
            return SmallVec::new();
        }

        // 5. Pass through.
        smallvec![identity_edge(prev_edge, return_site)]
    }
}
