use std::cell::RefCell;
use std::collections::HashSet;

use smallvec::{smallvec, SmallVec};

use rustc_middle::mir::{self, Local, Place};
use rustc_middle::ty::TyCtxt;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::flow_functions::FlowFunctions;
use crate::infoflow::ifds::path_edge::PathEdge;
use crate::infoflow::{
    apply_assignment_flow, arg_param_pairs,
    statement_or_terminator_at, StatementOrTerminator, Unit,
};
use crate::mir::function::FuncDef;
use crate::mir::place_ext::PlaceExt;
use crate::util::type_util;

pub struct ForwardFlowFunctions<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
    /// Facts that need store POA expansion in the path edge extendor.
    /// Only populated when lplace.is_indirect() (a store through a pointer).
    store_poa_pending: RefCell<SmallVec<[AccessPath<'tcx>; 2]>>,
}

impl<'analysis, 'tcx> ForwardFlowFunctions<'analysis, 'tcx> {
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> ForwardFlowFunctions<'analysis, 'tcx> {
        ForwardFlowFunctions {
            acx,
            store_poa_pending: RefCell::new(SmallVec::new()),
        }
    }

    pub fn clear_store_poa_pending(&self) {
        self.store_poa_pending.borrow_mut().clear();
    }

    pub fn is_store_poa_pending(&self, fact: &AccessPath<'tcx>) -> bool {
        self.store_poa_pending.borrow().contains(fact)
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    /// Forward aggregate field matching: check operand place, return first match.
    fn compute_aggregate_field_targets(
        &self,
        source: &AccessPath<'tcx>,
        _base_place: mir::Place<'tcx>,
        field_pairs: &[(mir::Place<'tcx>, mir::Operand<'tcx>)],
        curr: Unit<'tcx>,
    ) -> SmallVec<[AccessPath<'tcx>; 1]> {
        for (field_place, operand) in field_pairs {
            if let mir::Operand::Copy(place)
            | mir::Operand::Move(place) = operand
            {
                if source.is_projection_of(self.acx, place) {
                    return self.compute_move_or_copy_targets(
                        source, field_place, operand, curr,
                    );
                }
            }
        }
        smallvec![*source]
    }

    // Compute the targets of a move or copy operation from rplace to lplace.
    // Box dereference must have been expanded for lplace before calling this function.
    pub fn compute_move_or_copy_targets(
        &self,
        source: &AccessPath<'tcx>,
        lplace: &mir::Place<'tcx>,
        operand: &mir::Operand<'tcx>,
        unit: Unit<'tcx>,
    ) -> SmallVec<[AccessPath<'tcx>; 1]> {
        // Ignore the move/copy assignment if lplace is of zero-sized type
        let lty = type_util::place_ty(self.tcx(), lplace, source.func_def);
        if type_util::is_zst(self.tcx(), lty) {
            return smallvec![*source];
        }

        let kill_source = kill_source(self.acx, source, lplace);

        let mut res = if kill_source {
            // smallvec![]
            let deactivated_path = source.deactivate_at(unit.location);
            smallvec![deactivated_path]
        } else {
            smallvec![*source]
        };

        let rplace = match operand {
            mir::Operand::Copy(rplace) | mir::Operand::Move(rplace) => rplace,
            mir::Operand::Constant(_constant) => return res,
            mir::Operand::RuntimeChecks(_) => return res,
        };

        let rplace =
            rplace.expand_box_deref(self.tcx(), unit.func.def_id);
        if !source.is_projection_of(self.acx, &rplace) {
            return res;
        }

        // 1. If the source is not a reference path, a copy or move from the prefix of the
        //    source generates a new dtarget.
        // 2. If the source is a reference path, like `&x.f` or `&(*x).f`:
        //    a. If the source is not indirect, like `&x.f`, a copy or move from any prefix
        //       does not generate a new dtarget.
        //    b. If the source is indirect, like `&(*x).f`, a copy or move from the prefix
        //       of the base pointer, i.e. `x`, generates a new dtarget. For example,
        //       after `y = x`, we will have a new dtarget &(*x).f
        //       The source can be more complex in this case, like `&(*(*x).f).g`, and
        //       a copy or move from `(*x).f` also generates a new dtarget.
        if source.has_ref_elem() {
            if !source.is_indirect() {
                return res;
            } else {
                let base_path = source.truncate_from_last_deref().unwrap();
                if !base_path.is_projection_of(self.acx, &rplace) {
                    return res;
                }
            }
        }

        let dtarget = source.derive_with_new_base(self.acx, &rplace, lplace);
        res.push(dtarget);
        if lplace.is_indirect() {
            self.store_poa_pending.borrow_mut().push(dtarget);
        }
        res
    }

    // Compute the targets of a ref or rawptr operation.
    // Box dereference must have been expanded for lplace before calling this function.
    pub fn compute_ref_or_rawptr_targets(
        &self,
        source: &AccessPath<'tcx>,
        lplace: &mir::Place<'tcx>,
        rplace: &mir::Place<'tcx>,
        unit: Unit<'tcx>,
        _is_rawptr: bool,
    ) -> SmallVec<[AccessPath<'tcx>; 1]> {
        let rplace =
            rplace.expand_box_deref(self.tcx(), unit.func.def_id);
        let rpath = AccessPath::from_rustc_place(self.acx, unit.func, &rplace);
        // A special case is "y = &(*x)", where we treat it as "y = x".
        if rpath.is_indirect() && rpath.access_elems.len() == 1 {
            return self.compute_move_or_copy_targets(
                source,
                lplace,
                &mir::Operand::Copy(Place::from(rplace.local)),
                unit,
            );
        }

        let kill_source = kill_source(self.acx, source, lplace);

        let mut res = if kill_source {
            let deactivated_path = source.deactivate_at(unit.location);
            smallvec![deactivated_path]
        } else {
            smallvec![*source]
        };

        // Given a reference statement "y = &(*x).f" and a source "(*x).f.g", we produce a dtarget "(*y).g"
        // by making a dereference place for the lplace and replacing it with the rplace in the source.
        // This also works for the cases where the source is a reference path like "&x.f" or "&(*x).f".
        if source.is_projection_of(self.acx, &rplace) {
            let lplace_deref = self.tcx().mk_place_deref(*lplace);
            let dtarget = source.derive_with_new_base(self.acx, &rplace, &lplace_deref);
            res.push(dtarget);
        }

        res
    }

}

impl<'analysis, 'tcx> FlowFunctions<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>
    for ForwardFlowFunctions<'analysis, 'tcx>
{
    fn get_normal_flow_function(
        &self,
        edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        _succ: Unit<'tcx>,
    ) -> impl Fn(&AccessPath<'tcx>) -> SmallVec<[AccessPath<'tcx>; 1]> {
        let curr = edge.get_target();
        let func = curr.func;
        let stmt = statement_or_terminator_at(self.tcx(), curr);

        move |source| {
            if source.is_inactive() {
                return smallvec![*source];
            }

            if source.is_heap_pointer() {
                return smallvec![*source];
            }

            if let StatementOrTerminator::Statement(stmt_kind) = stmt {
                match stmt_kind {
                    mir::StatementKind::Assign(box (lplace, rvalue)) => {
                        let lplace = lplace.expand_box_deref(self.tcx(), func.def_id);
                        if let Some(result) = apply_assignment_flow(
                            self.tcx(),
                            func,
                            &lplace,
                            rvalue,
                            source,
                            curr,
                            &|s, l, o, c| self.compute_move_or_copy_targets(s, l, o, c),
                            &|s, l, r, c, raw| self.compute_ref_or_rawptr_targets(s, l, r, c, raw),
                            &|s, bp, fp, c| self.compute_aggregate_field_targets(s, bp, fp, c),
                        ) {
                            return result;
                        }
                        // Otherwise 
                        if kill_source(self.acx, source, &lplace) {
                            return smallvec![];
                        } else {
                            return smallvec![*source];
                        }
                    }
                    mir::StatementKind::StorageLive(_) => {}
                    mir::StatementKind::StorageDead(local) => {
                        if source.is_projection_of(self.acx, &Place::from(*local)) {
                            let deactivated_path = source.deactivate_at(curr.location);
                            return smallvec![deactivated_path];
                        }
                    }
                    _ => {}
                }
            }

            smallvec![*source]
        }
    }

    fn get_call_flow_function(
        &self,
        edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        callee: FuncDef<'tcx>,
        _first_stmt_in_callee: Unit<'tcx>,
    ) -> impl Fn(&AccessPath<'tcx>) -> SmallVec<[AccessPath<'tcx>; 1]> {
        let callsite = edge.get_target();
        let arg_param_pairs = arg_param_pairs(self.acx, callsite, callee);

        move |source| {
            if source.is_inactive() {
                return smallvec![];
            }

            if source.is_heap_pointer() {
                // the callsite is the last unit of the allocation trace
                if *source.alloc_trace.unwrap().last().unwrap() == callsite {
                    if source.alloc_trace.unwrap().len() > 1 {
                        return smallvec![source.pop_alloc_trace()];
                    }
                }

                // if the callsite is not part of the allocation trace, or if the callsite
                // corresponds to the ultimate allocation site, we do not propagate the flow.
                return smallvec![];
            }

            let mut out = HashSet::new();
            // params <- args
            for (arg, param) in arg_param_pairs.iter() {
                match arg {
                    mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
                        // If the source path has a reference element, like &x.f or &(*x).f,
                        // we only propagate it if it is indirect.
                        if source.has_ref_elem() && !source.is_indirect() {
                            continue;
                        }
                        if source.is_projection_of(self.acx, arg_place) {
                            let dtarget = source
                                .derive_with_new_base_in_func(self.acx, arg_place, param, callee);
                            out.insert(dtarget);
                        }
                    }
                    _ => {}
                }
            }

            out.into_iter().collect()
        }
    }

    fn get_return_flow_function(
        &self,
        _edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        _incoming_edge: Option<&PathEdge<Unit<'tcx>, AccessPath<'tcx>>>,
        callsite: Unit<'tcx>,
        callee: FuncDef<'tcx>,
        _return_site: Unit<'tcx>,
    ) -> impl Fn(&AccessPath<'tcx>) -> SmallVec<[AccessPath<'tcx>; 1]> {
        let caller = callsite.func;
        let arg_param_pairs = arg_param_pairs(self.acx, callsite, callee);
        let destination = callsite.call_destination(self.tcx());
        let ret_place = Place::from(Local::from_usize(0));

        move |source| {
            if source.is_inactive() {
                return smallvec![];
            }

            if source.is_heap_pointer() {
                // A heap pointer's forward flow should ended without allocation information.
                return smallvec![];
            }

            // destination <- return value
            if source.is_projection_of(self.acx, &ret_place) {
                let dtarget =
                    source.derive_with_new_base_in_func(self.acx, &ret_place, &destination, caller);
                return smallvec![dtarget];
            }

            if !source.is_indirect() {
                return smallvec![];
            }

            let mut out = HashSet::new();
            // params <- args
            for (arg, param) in arg_param_pairs.iter() {
                if source.is_projection_of(self.acx, param) {
                    if let mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) = arg {
                        let dtarget = source
                            .derive_with_new_base_in_func(self.acx, param, &arg_place, caller);
                        out.insert(dtarget);
                    }
                }
            }

            out.into_iter().collect()
        }
    }

    fn get_call_to_return_flow_function(
        &self,
        edge: &PathEdge<Unit<'tcx>, AccessPath<'tcx>>,
        _return_site: Unit<'tcx>,
        callee: Option<FuncDef<'tcx>>,
    ) -> impl Fn(&AccessPath<'tcx>) -> SmallVec<[AccessPath<'tcx>; 1]> {
        let callsite = edge.get_target();
        let (args, destination) = callsite.args_and_destination(self.tcx());

        move |source| {
            if source.is_inactive() {
                return smallvec![*source];
            }

            if source.is_heap_pointer() {
                if *source.alloc_trace.unwrap().last().unwrap() == callsite {
                    // reaches the allocation site
                    if source.alloc_trace.unwrap().len() == 1 {
                        return smallvec![source.pop_alloc_trace()];
                    } else {
                        return smallvec![];
                    }
                }

                return smallvec![*source];
            }

            // destination <- return value
            if source.is_projection_of(self.acx, &destination) {
                return if kill_source(self.acx, source, &destination) {
                    // smallvec![]
                    let deactivated_path = source.deactivate_at(callsite.location);
                    smallvec![deactivated_path]
                } else {
                    smallvec![*source]
                };
            }
            
            if callee.is_none() || !self.tcx().is_mir_available(callee.unwrap().def_id) {
                return smallvec![*source];
            }

            if !source.is_indirect() {
                return smallvec![*source];
            }

            // params <- args
            for arg in &args {
                match arg {
                    mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
                        if source.is_projection_of(self.acx, arg_place) {
                            return smallvec![];
                        }
                    }
                    _ => {}
                }
            }

            smallvec![*source]
        }
    }

}

/// 1. If the source is not a reference path, a writing to the prefix of the source
///    directly kills the source.
/// 2. If the source is a reference path, like `&x.f` or `&(*x).f`:
///    a. If the source is not indirect, like `&x.f`, a writing to any prefix does
///       not kill the source since the address of `x.f` does not change.
///    b. If the source is indirect, like `&(*x).f`, a writing to the prefix of the
///       base pointer, i.e. `x`, kills the source.
///       The source can be more complex in this case, like `&(*(*x).f).g`, and
///       writing to `(*x).f` also kills the source.
pub fn kill_source<'tcx>(
    acx: &AnalysisContext<'tcx>,
    source: &AccessPath<'tcx>,
    lplace: &mir::Place<'tcx>,
) -> bool {
    if !source.has_ref_elem() {
        source.is_projection_of(acx, &lplace) && !lplace.is_projection_of_array()
    } else {
        if !source.is_indirect() {
            false
        } else {
            let base_path = source.truncate_from_last_deref().unwrap();
            base_path.is_projection_of(acx, &lplace) && !lplace.is_projection_of_array()
        }
    }
}
