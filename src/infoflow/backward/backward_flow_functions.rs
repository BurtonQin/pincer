use std::cell::RefCell;
use std::collections::HashSet;

use log::*;
use smallvec::{smallvec, SmallVec};

use rustc_middle::mir::{self, Local, Place};
use rustc_middle::ty::TyCtxt;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::{access_elem::AccessElem, access_path::AccessPath};
use crate::infoflow::ifds::{flow_functions::FlowFunctions, path_edge::PathEdge};
use crate::infoflow::{
    apply_assignment_flow, arg_param_pairs,
    statement_or_terminator_at, StatementOrTerminator, Unit,
};
use crate::mir::function::FuncDef;
use crate::mir::place_ext::PlaceExt;
use crate::util::type_util;

pub struct BackwardFlowFunctions<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
    /// Facts that need load_or_store POA expansion in the path edge extendor.
    /// Only populated when rplace.is_indirect() in a flow function.
    load_poa_pending: RefCell<SmallVec<[AccessPath<'tcx>; 2]>>,
}

impl<'analysis, 'tcx> BackwardFlowFunctions<'analysis, 'tcx> {
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> BackwardFlowFunctions<'analysis, 'tcx> {
        BackwardFlowFunctions {
            acx,
            load_poa_pending: RefCell::new(SmallVec::new()),
        }
    }

    pub fn clear_load_poa_pending(&self) {
        self.load_poa_pending.borrow_mut().clear();
    }

    pub fn is_load_poa_pending(&self, fact: &AccessPath<'tcx>) -> bool {
        self.load_poa_pending.borrow().contains(fact)
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    /// Backward aggregate field matching: guard with projection_after_base, then first-match.
    fn compute_aggregate_field_targets(
        &self,
        source: &AccessPath<'tcx>,
        base_place: mir::Place<'tcx>,
        field_pairs: &[(mir::Place<'tcx>, mir::Operand<'tcx>)],
        curr: Unit<'tcx>,
    ) -> SmallVec<[AccessPath<'tcx>; 1]> {
        if source.projection_after_base(self.acx, &base_place).is_some() {
            for (field_place, operand) in field_pairs {
                if source.is_projection_of(self.acx, field_place) {
                    return self.compute_move_or_copy_targets(
                        source, field_place, operand, curr,
                    );
                }
            }
            return smallvec![];
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
        if !source.is_projection_of(self.acx, &lplace) {
            return smallvec![*source];
        }

        // Ignore the move/copy assignment if lplace is of zero-sized type
        let lty = type_util::place_ty(self.tcx(), lplace, unit.func);
        if type_util::is_zst(self.tcx(), lty) {
            return smallvec![*source];
        }

        let rplace = match operand {
            mir::Operand::Copy(rplace) | mir::Operand::Move(rplace) => rplace,
            mir::Operand::Constant(constant) => {
                return self.compute_constant_assignment_targets(source, lplace, constant);
            }
            mir::Operand::RuntimeChecks(_) => return smallvec![*source],
        };

        let rplace =
            rplace.expand_box_deref(self.tcx(), unit.func.def_id);
        let dtarget = source.derive_with_new_base(self.acx, lplace, &rplace);

        let out = if lplace.is_projection_of_array() {
            smallvec![*source, dtarget]
        } else {
            smallvec![dtarget]
        };
        if rplace.is_indirect() {
            self.load_poa_pending.borrow_mut().push(dtarget);
        }
        out
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
        if !source.is_projection_of(self.acx, &lplace) {
            return smallvec![*source];
        }

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

        let proj_after_base = source.projection_after_base(self.acx, lplace).unwrap();
        if let Some(next_access_elem) = proj_after_base.first() {
            if matches!(next_access_elem, AccessElem::Deref) {
                // The next access element is a deref. We can remove the deref and replace the base
                // with the right place.
                let dtarget = AccessPath::from_rustc_place_with_elems(
                    self.acx,
                    source.func_def,
                    &rplace,
                    &proj_after_base[1..],
                );
                let out = if lplace.is_projection_of_array() {
                    smallvec![*source, dtarget]
                } else {
                    smallvec![dtarget]
                };
                if rplace.is_indirect() {
                    self.load_poa_pending.borrow_mut().push(dtarget);
                }
                return out;
            } else {
                // It should be an error if the next access element is not a deref.
                // The left place is a reference or raw pointer since we are
                // visiting a ref or rawptr operation. It has no field or index.
                warn!(
                    "Unexpected access element ({:?}) after place {:?}",
                    next_access_elem, lplace
                );
                return smallvec![];
            }
        } else {
            let ref_path = AccessPath::from_rustc_place_with_elems(
                self.acx,
                unit.func,
                &rplace,
                self.acx.mk_access_elems(&[AccessElem::Ref]),
            );
            return smallvec![ref_path];
        }
    }

    pub fn compute_constant_assignment_targets(
        &self,
        _source: &AccessPath<'tcx>,
        _lplace: &mir::Place<'tcx>,
        constant: &mir::ConstOperand<'tcx>,
    ) -> SmallVec<[AccessPath<'tcx>; 1]> {
        let mir::ConstOperand { const_, .. } = constant;
        match const_ {
            mir::Const::Val(val, _ty) => {
                if let mir::ConstValue::Scalar(mir::interpret::Scalar::Ptr(ptr, _size)) = val {
                    match self.tcx().try_get_global_alloc(ptr.provenance.alloc_id()) {
                        Some(mir::interpret::GlobalAlloc::Static(def_id)) => {
                            info!("Global allocation found: {:?}", def_id);
                            let def_kind = self.tcx().def_kind(def_id);
                            info!("Is static: {}", matches!(def_kind, rustc_hir::def::DefKind::Static { .. }));
                        }
                        _ => {}
                    }
                }
            }
            _ => {}
        }
        return smallvec![];
    }

}

impl<'analysis, 'tcx> FlowFunctions<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>
    for BackwardFlowFunctions<'analysis, 'tcx>
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
                if source.deactivation_point == Some(curr.location) {
                    return smallvec![source.activate()];
                } else {
                    return smallvec![*source];
                }
            }

            if source.is_heap_pointer() {
                return smallvec![*source];
            }

            if let StatementOrTerminator::Statement(stmt_kind) = stmt {
                match stmt_kind {
                    mir::StatementKind::Assign(box (lplace, rvalue)) => {
                        let lplace = lplace.expand_box_deref(self.tcx(), func.def_id);
                        if !source.is_projection_of(self.acx, &lplace) {
                            return smallvec![*source];
                        }
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
                        if lplace.is_projection_of_array() {
                            return smallvec![*source];
                        } else {
                            return smallvec![];
                        }
                    }
                    mir::StatementKind::StorageLive(local) => {
                        if source.is_projection_of(self.acx, &mir::Place::from(*local)) {
                            return smallvec![];
                        } 
                    }
                    mir::StatementKind::StorageDead(_) => {}
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
        let destination = callsite.call_destination(self.tcx());

        move |source| {
            if source.is_inactive() {
                return smallvec![];
            }

            if source.is_heap_pointer() {
                return smallvec![];
            }

            // destination <- return value
            if source.is_projection_of(self.acx, &destination) {
                let ret_place = Place::from(Local::from_usize(0));
                let dtarget =
                    source.derive_with_new_base_in_func(self.acx, &destination, &ret_place, callee);
                return smallvec![dtarget];
            }

            if !source.is_indirect() {
                return smallvec![];
            }

            let mut out = HashSet::new();
            // params <- args
            for (arg, param) in arg_param_pairs.iter() {
                match arg {
                    mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
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

        move |source| {
            if source.is_inactive() {
                return smallvec![];
            }

            if source.is_heap_pointer() {
                return smallvec![source.extend_alloc_trace(self.acx, callsite)];
            }

            let mut out = HashSet::new();
            // params <- args
            for (arg, param) in arg_param_pairs.iter() {
                if source.is_projection_of(self.acx, param) {
                    match arg {
                        mir::Operand::Copy(arg_place) | mir::Operand::Move(arg_place) => {
                            let dtarget = source
                                .derive_with_new_base_in_func(self.acx, param, arg_place, caller);
                            out.insert(dtarget);
                        }
                        _ => {}
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
                if source.deactivation_point == Some(callsite.location) {
                    return smallvec![source.activate()];
                } else {
                    return smallvec![*source];
                }
            }

            if source.is_heap_pointer() {
                return smallvec![*source];
            }

            if callee.is_some() && !self.tcx().is_mir_available(callee.unwrap().def_id) {
                return smallvec![*source];
            }

            // destination <- return value
            if source.is_projection_of(self.acx, &destination) {
                return smallvec![];
            }

            // The points-to information of source would not be changed in the callee
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
