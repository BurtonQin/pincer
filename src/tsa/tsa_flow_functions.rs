use smallvec::{smallvec, SmallVec};
use std::collections::{HashMap, HashSet};

use rustc_middle::mir::{self, Local, Place};
use rustc_middle::ty::TyCtxt;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::CFGQueries;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::flow_functions::FlowFunctions;
use crate::infoflow::{self, arg_param_pairs, points_of_aliasing};
use crate::mir::drop_shim;
use crate::mir::function::FuncDef;
use crate::mir::unit::{statement_or_terminator_at, StatementOrTerminator, Unit};
use crate::tsa::abstract_value::ConstantValue;
use crate::tsa::state::{self, ExecutionState, SymbState, SymbStateSupport, TypeState};
use crate::tsa::state_transition::TypeStateTransition;
use crate::tsa::{TSAPathEdgeNode, TSAPathEdge};
use crate::util;

pub struct TypeStateAnalysisFlowFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
    I: CFGQueries<'tcx, N>,
{
    acx: &'analysis AnalysisContext<'tcx>,
    icfg: &'cfg I,
    trans: T,
    marker: std::marker::PhantomData<(S, N)>,
}

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    TypeStateAnalysisFlowFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
    I: CFGQueries<'tcx, N>,
{
    pub fn new(acx: &'analysis AnalysisContext<'tcx>, icfg: &'cfg I, trans: T) -> Self {
        TypeStateAnalysisFlowFunctions {
            acx,
            icfg,
            trans,
            marker: std::marker::PhantomData,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    /// Reimplement some functions as we need to handle the case where the caller/callee is a drop function.
    fn arg_param_pairs(
        &self,
        callsite: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> Vec<(mir::Operand<'tcx>, Place<'tcx>)> {
        let caller = callsite.func;
        // In rustc's drop shim, _1 is *mut T. The dropped value is at *_1.
        let drop_shim_value = self.tcx().mk_place_deref(Place::from(Local::from_usize(1)));
        let param = Place::from(Local::from_usize(1));

        if drop_shim::is_drop_shim(self.tcx(), caller) {
            let body = self.acx.drop_shim_body(caller);
            let block_data = &body.basic_blocks[callsite.location.block];
            let terminator = block_data.terminator();
            return match &terminator.kind {
                mir::TerminatorKind::Call { args, .. } => {
                    vec![(args[0].node.clone(), param)]
                }
                mir::TerminatorKind::Drop { place, .. } => {
                    // Field drop: the dropped place is a projection of *_1 (e.g., (*_1).field).
                    // The callee's *_1 should receive this field.
                    vec![(mir::Operand::Move(*place), drop_shim_value)]
                }
                _ => unreachable!("Expect a Drop or a Call terminator in drop shim"),
            };
        }

        if self.tcx().is_mir_available(caller.def_id) {
            if let StatementOrTerminator::Terminator(terminator) =
                statement_or_terminator_at(self.tcx(), callsite)
            {
                match &terminator {
                    mir::TerminatorKind::Call { .. } => arg_param_pairs(self.acx, callsite, callee),
                    mir::TerminatorKind::Drop { place, .. } => {
                        // Drop terminator in regular code: maps dropped place to
                        // *_1 in the drop shim (the dereferenced parameter).
                        vec![(mir::Operand::Move(*place), drop_shim_value)]
                    }
                    _ => unreachable!("Expect a Call or a Drop terminator"),
                }
            } else {
                unreachable!("Expect a terminator");
            }
        } else {
            unreachable!("No MIR available for non-drop caller {:?}", caller.def_id);
        }
    }

    fn call_args(&self, callsite: Unit<'tcx>) -> Vec<mir::Operand<'tcx>> {
        let caller = callsite.func;

        if drop_shim::is_drop_shim(self.tcx(), caller) {
            let body = self.acx.drop_shim_body(caller);
            let block_data = &body.basic_blocks[callsite.location.block];
            let terminator = block_data.terminator();
            return match &terminator.kind {
                mir::TerminatorKind::Call { args, .. } => {
                    vec![args[0].node.clone()]
                }
                mir::TerminatorKind::Drop { place, .. } => {
                    vec![mir::Operand::Move(place.clone())]
                }
                _ => unreachable!("Expect a Drop or a Call terminator in drop shim"),
            };
        }

        if self.tcx().is_mir_available(caller.def_id) {
            if let StatementOrTerminator::Terminator(terminator) =
                statement_or_terminator_at(self.tcx(), callsite)
            {
                match &terminator {
                    mir::TerminatorKind::Call { .. } => callsite.call_args(self.tcx()),
                    mir::TerminatorKind::Drop { place, .. } => {
                        vec![mir::Operand::Move(place.clone())]
                    }
                    _ => unreachable!("Expect a Call or a Drop terminator"),
                }
            } else {
                unreachable!("Expect a terminator");
            }
        } else {
            unreachable!("No MIR available for non-drop caller {:?}", caller.def_id);
        }
    }

    /// We don't have a call destination for a drop site.
    fn call_destination(&self, callsite: Unit<'tcx>) -> Option<Place<'tcx>> {
        let caller = callsite.func;

        if drop_shim::is_drop_shim(self.tcx(), caller) {
            let body = self.acx.drop_shim_body(caller);
            let block_data = &body.basic_blocks[callsite.location.block];
            let terminator = block_data.terminator();
            return match &terminator.kind {
                mir::TerminatorKind::Call { destination, .. } => Some(*destination),
                mir::TerminatorKind::Drop { .. } => None,
                _ => unreachable!("Expect a Drop or a Call terminator in drop shim"),
            };
        }

        if !self.tcx().is_mir_available(caller.def_id) {
            return None;
        }
        if let StatementOrTerminator::Terminator(terminator) =
            statement_or_terminator_at(self.tcx(), callsite)
        {
            match &terminator {
                mir::TerminatorKind::Call { destination, .. } => {
                    return Some(destination.clone());
                }
                mir::TerminatorKind::Drop { .. } => {
                    return None;
                }
                _ => unreachable!("Expect a Drop or a Call terminator"),
            }
        } else {
            unreachable!("Expect a terminator");
        }
    }

    /// Process normal flow for a terminator node (branch pruning, discriminant tracking).
    fn terminator_normal_flow(
        &self,
        curr: N,
        succ: N,
        state: &SymbState<'tcx, S, AccessPath<'tcx>>,
    ) -> SmallVec<[SymbState<'tcx, S, AccessPath<'tcx>>; 1]> {
        if self.icfg.is_conditional_branch_from(curr) {
            if let Some(switch_int) = self.icfg.get_switch_int(curr) {
                if let Some(discr_place) = switch_int.discr.place() {
                    if let Some(const_value) = state.get_constant_value(&discr_place) {
                        if let ConstantValue::Constant(const_value) = const_value {
                            let target =
                                switch_int.targets.target_for_value(*const_value as u128);
                            let target_unit = succ.as_unit();
                            if target != target_unit.location.block {
                                return smallvec![];
                            }
                        }
                    } else {
                        let value_for_target =
                            switch_int.targets.iter().find_map(|(value, target)| {
                                if target == succ.as_unit().location.block {
                                    Some(value)
                                } else {
                                    None
                                }
                            });
                        if let Some(value_for_target) = value_for_target {
                            let curr_unit = curr.as_unit();
                            let curr_bb = curr_unit.location.block;
                            let func = curr_unit.func;
                            let block = if drop_shim::is_drop_shim(self.acx.tcx, func) {
                                let body = self.acx.drop_shim_body(func);
                                &body.basic_blocks[curr_bb]
                            } else {
                                self.acx
                                    .tcx
                                    .optimized_mir(func.def_id)
                                    .basic_blocks
                                    .get(curr_bb)
                                    .unwrap()
                            };
                            if let Some(discriminant) =
                                util::enum_discriminant_of(&discr_place, block)
                            {
                                let mut new_state = state.clone_owned();
                                new_state.borrow_mut().set_discriminant(
                                    discriminant,
                                    ConstantValue::Constant(value_for_target as u32),
                                );
                                return smallvec![new_state];
                            }
                        }
                    }
                }
            }
        }
        smallvec![state.clone_owned()]
    }

    fn retain_aliases(&self, state: &mut SymbState<'tcx, S, AccessPath<'tcx>>) {
        state
            .borrow_mut()
            .aliases_mut()
            .retain(|alias| infoflow::retain_access_path(self.acx, alias));
    }

    /// Normalize the error state by wiping out the execution state.
    fn normalize_error_state(
        &self,
        state: &SymbState<'tcx, S, AccessPath<'tcx>>,
    ) -> SymbState<'tcx, S, AccessPath<'tcx>> {
        assert!(state.type_state.is_error_state());
        SymbState::new_symb_state(
            state.type_state,
            ExecutionState::init_exec_state(HashSet::new()),
        )
    }

}

// ── Blanket FlowFunctions impl for all N: TSAPathEdgeNode ────────────────────────────

impl<'analysis, 'cfg, 'tcx, N, I, S, T>
    FlowFunctions<N, SymbState<'tcx, S, AccessPath<'tcx>>, FuncDef<'tcx>>
    for TypeStateAnalysisFlowFunctions<'analysis, 'cfg, 'tcx, N, I, S, T>
where
    N: TSAPathEdgeNode<'tcx>,
    I: CFGQueries<'tcx, N>,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    fn get_normal_flow_function(
        &self,
        edge: &TSAPathEdge<'tcx, S, N>,
        succ: N,
    ) -> impl Fn(
        &SymbState<'tcx, S, AccessPath<'tcx>>,
    ) -> SmallVec<[SymbState<'tcx, S, AccessPath<'tcx>>; 1]> {
        let curr = edge.get_target();
        move |state| match curr.apply_normal_flow(self.acx, state, self.trans) {
            Some(out_state) => {
                let mut out = if out_state.type_state.is_error_state() {
                    self.normalize_error_state(&out_state)
                } else {
                    out_state
                };
                self.retain_aliases(&mut out);
                smallvec![out]
            }
            None => self.terminator_normal_flow(curr, succ, state),
        }
    }

    fn get_call_flow_function(
        &self,
        edge: &TSAPathEdge<'tcx, S, N>,
        callee: FuncDef<'tcx>,
        _first_stmt_in_callee: N,
    ) -> impl Fn(
        &SymbState<'tcx, S, AccessPath<'tcx>>,
    ) -> SmallVec<[SymbState<'tcx, S, AccessPath<'tcx>>; 1]> {
        let callsite = edge.get_target().as_callsite();
        let arg_param_pairs = self.arg_param_pairs(callsite, callee);

        move |state| {
            if state.type_state.is_error_state() {
                return smallvec![];
            }

            if self.acx.analysis_options.ignore_rc_drop
                && drop_shim::is_rc_drop_shim(self.tcx(), callee)
            {
                return smallvec![];
            }

            let mut new_aliases = HashSet::new();
            let mut new_constants = HashMap::new();
            for (arg, param) in arg_param_pairs.iter() {
                match arg {
                    mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
                        for alias in state.aliases() {
                            if alias.has_ref_elem() && !alias.is_indirect() {
                                continue;
                            }
                            if alias.is_projection_of(self.acx, arg_place) {
                                let new_alias = alias.derive_with_new_base_in_func(
                                    self.acx, arg_place, param, callee,
                                );
                                new_aliases.insert(new_alias);
                            }
                        }
                        for (const_kind, constant_value) in state.constants() {
                            match const_kind {
                                state::ConstantKind::EnumDiscriminant(place) => {
                                    if place == arg_place {
                                        new_constants.insert(
                                            state::ConstantKind::EnumDiscriminant(param.clone()),
                                            *constant_value,
                                        );
                                    }
                                }
                                _ => {}
                            }
                        }
                    }
                    _ => {}
                }
            }
            if new_aliases.is_empty() {
                smallvec![]
            } else {
                let mut new_state = SymbState::new_symb_state(
                    state.type_state,
                    ExecutionState::new_exec_state(new_aliases, new_constants),
                );
                self.retain_aliases(&mut new_state);
                smallvec![new_state]
            }
        }
    }

    fn get_return_flow_function(
        &self,
        prev_edge: &TSAPathEdge<'tcx, S, N>,
        incoming_edge: Option<&TSAPathEdge<'tcx, S, N>>,
        callsite_node: N,
        callee: FuncDef<'tcx>,
        return_site: N,
    ) -> impl Fn(
        &SymbState<'tcx, S, AccessPath<'tcx>>,
    ) -> SmallVec<[SymbState<'tcx, S, AccessPath<'tcx>>; 1]> {
        let callsite = callsite_node.as_callsite();
        let caller = callsite.func;
        let arg_param_pairs = self.arg_param_pairs(callsite, callee);
        let destination = self.call_destination(callsite);
        let ret_place = Place::from(Local::from_usize(0));
        let return_site_unit = return_site.as_unit();
        let start_aliases = prev_edge.fact_at_source().aliases().clone();
        let prev_edge_incoming = incoming_edge.map(|e| {
            (
                e.fact_at_target().aliases().clone(),
                e.fact_at_target().constants().clone(),
            )
        });

        move |state| {
            if state.type_state.is_error_state() {
                return smallvec![self.normalize_error_state(state)];
            }

            let mut gen_set = HashSet::new();
            let mut kill_set = HashSet::new();

            // Compute the kill set for balanced return flow only
            if prev_edge_incoming.is_some() {
                for alias in &start_aliases {
                    // TODO: This may lead to unsoundness.
                    // For example, if we are computing the data flow of `(*x).f`,
                    // and `x` is passed as an argument to a function call. Let `p`
                    // be the corresponding parameter of `x` in the callee.
                    // `(*p).x` can be killed if `p` is reassigned in the callee.
                    // However, we should not kill `(*x).f` in the caller.
                    if !state.aliases().contains(alias) && alias.is_indirect() {
                        for (arg, param) in arg_param_pairs.iter() {
                            if alias.is_projection_of(self.acx, param) {
                                if let mir::Operand::Copy(arg_place)
                                | mir::Operand::Move(arg_place) = arg
                                {
                                    let killed_alias = alias.derive_with_new_base_in_func(
                                        self.acx, param, arg_place, caller,
                                    );
                                    kill_set.insert(killed_alias);

                                    // kill a place `(*p).f` can also kill `(*q).f` (`x.f`),
                                    // if `p` and `q` must aliases (`p` must point to `x`) at this point.
                                    // TODO: to reduce the complexity, we simply compute the aliases of `(*p).f`
                                    // by invoking `process_forward_return_poa`. This may lead to unsoundness,
                                    // as we should consider strong updates here. However, it is very useful
                                    // to reduce the false positives.
                                    if self.acx.analysis_options.msa_strong_updates {
                                        if self.tcx().is_mir_available(caller.def_id) {
                                            let poa_aliases = points_of_aliasing::forward_return::process_forward_return_poa(
                                                self.acx,
                                                killed_alias,
                                                callsite,
                                                return_site_unit,
                                            );
                                            kill_set.extend(poa_aliases);
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }

            // Compute the gen set
            for alias in state.aliases() {
                // destination <- return value
                if let Some(destination) = destination {
                    if alias.is_projection_of(self.acx, &ret_place) {
                        let new_alias = alias.derive_with_new_base_in_func(
                            self.acx,
                            &ret_place,
                            &destination,
                            caller,
                        );
                        gen_set.insert(new_alias);
                        continue;
                    }
                }

                for (arg, param) in arg_param_pairs.iter() {
                    if alias.is_projection_of(self.acx, param) && alias.is_indirect() {
                        if let mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) = arg
                        {
                            let new_alias = alias.derive_with_new_base_in_func(
                                self.acx, param, arg_place, caller,
                            );
                            gen_set.insert(new_alias);
                        }
                    }
                }
            }

            let empty_aliases = HashSet::new();
            let empty_constants = HashMap::new();
            let (prev_aliases, prev_constants) = match &prev_edge_incoming {
                Some((aliases, constants)) => (aliases, constants),
                None => (&empty_aliases, &empty_constants),
            };

            // Call Return POA
            if !drop_shim::is_drop_shim(self.tcx(), return_site_unit.func)
                && !drop_shim::is_drop_shim(self.tcx(), callee)
            {
                let poa_aliases = gen_set
                    .iter()
                    .flat_map(|alias| {
                        // Apply Forward Return POA for new aliases only.
                        if prev_aliases.contains(alias) {
                            HashSet::from([alias.clone()])
                        } else {
                            points_of_aliasing::forward_return::process_forward_return_poa(
                                self.acx,
                                *alias,
                                callsite,
                                return_site_unit,
                            )
                        }
                    })
                    .collect();
                gen_set = poa_aliases;
                gen_set.retain(|alias| !alias.is_inactive());
            }

            let mut new_aliases = gen_set;
            if !prev_aliases.is_empty() {
                for alias in prev_aliases {
                    // Kill the alias if it is a projection of the call destination
                    if let Some(destination) = destination {
                        if !alias.has_ref_elem() || alias.is_indirect() {
                            if alias.is_projection_of(self.acx, &destination) {
                                continue;
                            }
                        }
                    }

                    // If the callee is a drop function, kill the aliases derived from the dropped place.
                    if drop_shim::is_drop_shim(self.tcx(), callee) {
                        for (arg, _) in arg_param_pairs.iter() {
                            if let mir::Operand::Move(arg_place) = arg {
                                if alias.is_projection_of(self.acx, arg_place) {
                                    continue;
                                }
                            }
                        }
                    }

                    if !kill_set.contains(alias) {
                        new_aliases.insert(alias.clone());
                    }
                }
            }

            // update the constants
            let mut new_constants = prev_constants.clone();
            if let Some(dest_place) = destination {
                new_constants.remove(&state::ConstantKind::EnumDiscriminant(dest_place));
                new_constants.remove(&state::ConstantKind::ConstantVariable(ret_place));

                for (const_kind, constant_value) in state.constants() {
                    match const_kind {
                        state::ConstantKind::EnumDiscriminant(place) => {
                            if *place == ret_place {
                                new_constants.insert(
                                    state::ConstantKind::EnumDiscriminant(dest_place),
                                    *constant_value,
                                );
                            }
                        }
                        _ => {}
                    }
                }
            }

            // Compute the new state
            let mut new_state = SymbState::new_symb_state(
                state.type_state,
                ExecutionState::new_exec_state(new_aliases, new_constants),
            );
            self.retain_aliases(&mut new_state);
            smallvec![new_state]
        }
    }

    fn get_call_to_return_flow_function(
        &self,
        edge: &TSAPathEdge<'tcx, S, N>,
        return_site: N,
        callee: Option<FuncDef<'tcx>>,
    ) -> impl Fn(
        &SymbState<'tcx, S, AccessPath<'tcx>>,
    ) -> SmallVec<[SymbState<'tcx, S, AccessPath<'tcx>>; 1]> {
        let curr = edge.get_target();
        let callsite = curr.as_callsite();
        let call_args = self.call_args(callsite);

        move |state| {
            if state.type_state.is_error_state() {
                return smallvec![self.normalize_error_state(state)];
            }

            let mut arg_aliases = HashSet::new();
            let mut kill_set = HashSet::new();
            for call_arg in call_args.iter() {
                match call_arg {
                    mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
                        for alias in state.aliases() {
                            if alias.has_ref_elem() && !alias.is_indirect() {
                                continue;
                            }
                            if alias.is_projection_of(self.acx, arg_place) {
                                arg_aliases.insert(alias);

                                if matches!(call_arg, mir::Operand::Move(_)) {
                                    // If the argument is a move, we need to kill the original alias
                                    // in the state.
                                    kill_set.insert(alias);
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
            if let Some(dst_place) = self.call_destination(callsite) {
                for alias in state.aliases() {
                    if alias.has_ref_elem() && !alias.is_indirect() {
                        continue;
                    }
                    if alias.is_projection_of(self.acx, &dst_place) {
                        kill_set.insert(alias);
                    }
                }
            }

            let callee_available = if let Some(callee) = callee {
                self.tcx().is_mir_available(callee.def_id)
                    || drop_shim::is_drop_shim(self.tcx(), callee)
            } else {
                false
            };

            if !callee_available {
                if let Some(state) =
                    self.trans
                        .on_mir_unavailable_callee(state, callee, &arg_aliases)
                {
                    return smallvec![state];
                }
            }

            if self.acx.analysis_options.ignore_rc_drop
                && callee_available
                && drop_shim::is_rc_drop_shim(self.tcx(), callee.unwrap())
            {
                // While we ignore the Rc drops, we still kill a rc pointer if it is moved and will not be used again.
                let mut new_state = state.clone_owned();
                for alias in kill_set {
                    new_state.borrow_mut().aliases_mut().remove(alias);
                }
                return smallvec![new_state];
            }

            // The callee has no impact on the state, we do not enter the callee and continue the analysis.
            if arg_aliases.is_empty() || !callee_available {
                // If the return site corresponds to an unwind branch and the callee will not unwind resume
                // in any case, we stop propagating.
                let is_unwind_branch = self.icfg.is_unwind_branch(curr, return_site);
                if is_unwind_branch && !self.acx.call_may_unwind(&callsite) {
                    return smallvec![];
                }

                let mut new_state = state.clone_owned();
                for alias in kill_set {
                    new_state.borrow_mut().aliases_mut().remove(alias);
                }
                return smallvec![new_state];
            } else {
                // Otherwise, we stop propagating and wait for the return flow from the callee.
                return smallvec![];
            }
        }
    }
}

