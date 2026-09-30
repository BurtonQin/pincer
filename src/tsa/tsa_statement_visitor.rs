use std::collections::HashSet;

use rustc_middle::mir::{
    self, Local, Operand, Place, Rvalue, Statement, StatementKind,
};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_abi::FieldIdx;
use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::forward::forward_flow_functions::kill_source;
use crate::infoflow::points_of_aliasing;
use crate::mir::drop_shim;
use crate::mir::function::FuncDef;
use crate::mir::place_ext::PlaceExt;
use crate::mir::unit::Unit;
use crate::tsa::abstract_value::ConstantValue;
use crate::tsa::aliases_project_from;
use crate::tsa::state::{SymbState, SymbStateSupport, TypeState};
use crate::tsa::state_transition::TypeStateTransition;
use crate::util::{self, type_util, generics_specializer::GenericsSpecializer};

/// Canonical per-statement analysis visitor.
/// Processes one MIR statement at a time. Used by both block-level and statement-level flow functions.
pub struct TSAStatementVisitor<'tcx, 'analysis, S, T>
where
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    acx: &'analysis AnalysisContext<'tcx>,
    func: FuncDef<'tcx>,
    pub out_state: SymbState<'tcx, S, AccessPath<'tcx>>,
    pub trans: T,
}

impl<'tcx, 'analysis, S, T> TSAStatementVisitor<'tcx, 'analysis, S, T>
where
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    pub fn new(
        acx: &'analysis AnalysisContext<'tcx>,
        func: FuncDef<'tcx>,
        in_state: &SymbState<'tcx, S, AccessPath<'tcx>>,
        trans: T,
    ) -> Self {
        TSAStatementVisitor {
            acx,
            func,
            out_state: in_state.clone_owned(),
            trans,
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    pub fn is_drop_shim_func(&self) -> bool {
        drop_shim::is_drop_shim(self.tcx(), self.func)
    }

    pub fn place_ty(&self, place: &Place<'tcx>) -> Ty<'tcx> {
        type_util::place_ty(self.tcx(), place, self.func)
    }

    /// Visit a single MIR statement at the given location.
    pub fn visit_statement(&mut self, loc: mir::Location, statement: &Statement<'tcx>) {
        let curr_unit = Unit::new(self.func, loc);
        let Statement {
            kind,
            source_info: _,
            ..
        } = statement;
        match kind {
            StatementKind::Assign(box (place, rvalue)) => {
                self.visit_assign(place, rvalue, curr_unit)
            }
            StatementKind::FakeRead(..) => (),
            StatementKind::SetDiscriminant {
                place,
                variant_index,
            } => self.visit_set_discriminant(place, *variant_index),
            StatementKind::StorageLive(local) => self.visit_storage_live(*local),
            StatementKind::StorageDead(local) => self.visit_storage_dead(*local),
            StatementKind::Retag(..) => (),
            StatementKind::PlaceMention(..) => (),
            StatementKind::AscribeUserType(..) => (),
            StatementKind::Coverage(..) => (),
            StatementKind::Intrinsic(box non_diverging_intrinsic) => {
                self.visit_non_diverging_intrinsic(non_diverging_intrinsic, curr_unit);
            }
            StatementKind::ConstEvalCounter => (),
            StatementKind::Nop => (),
            StatementKind::BackwardIncompatibleDropHint { .. } => (),
        }
    }

    fn visit_assign(&mut self, lplace: &Place<'tcx>, rvalue: &Rvalue<'tcx>, unit: Unit<'tcx>) {
        let lplace = self.expand_box_deref(lplace);
        let lty = self.place_ty(&lplace);
        if type_util::is_zst(self.tcx(), lty) {
            return;
        }

        if lplace.is_indirect() {
            // Get the base place that's being dereferenced
            let base_place = lplace.base_place_of_deref(self.tcx()).unwrap();
            // Visit pointer dereference
            self.visit_deref(&base_place);
        }

        let mut gen_set = HashSet::new();
        let mut kill_set = HashSet::new();

        // Iterate over the aliases in the out state to find the set of killed aliases.
        // We simiply kill an alias if the assignment is a writing to a prefix of the alias.
        // TODO: An assignment to the place `(*p).f` not only kills `(*p).f` but also `(*q).f`
        // (`x.f`), if `p` and `q` must aliases (`p` must point to `x`) at this point.
        for alias in self.out_state.aliases() {
            // The same as in `kill_source` in forward_flow_functions in infoflow analysis.
            if kill_source(self.acx, alias, &lplace) {
                kill_set.insert(*alias);
            }
        }

        match rvalue {
            Rvalue::Use(operand) => {
                self.visit_use(&lplace, operand, unit, &mut gen_set, &mut kill_set);
            }
            mir::Rvalue::Repeat(operand, _count) => {
                let index_place = self.tcx().mk_place_elem(
                    lplace,
                    mir::PlaceElem::ConstantIndex {
                        offset: 0,
                        min_length: 0,
                        from_end: false,
                    },
                );
                self.visit_use(&index_place, operand, unit, &mut gen_set, &mut kill_set);
            }
            mir::Rvalue::Ref(_, _, rplace) => {
                self.visit_ref_or_rawptr(&lplace, rplace, unit, &mut gen_set, &mut kill_set, false);
            }
            mir::Rvalue::RawPtr(_, rplace) => {
                self.visit_ref_or_rawptr(&lplace, rplace, unit, &mut gen_set, &mut kill_set, true);
            }
            mir::Rvalue::Aggregate(box aggregate_kind, operands) => {
                match aggregate_kind {
                    mir::AggregateKind::Array(_ty) => {
                        for (i, operand) in operands.iter().enumerate() {
                            let index_place = self.tcx().mk_place_elem(
                                lplace,
                                mir::PlaceElem::ConstantIndex {
                                    offset: i as u64,
                                    min_length: 1,
                                    from_end: false,
                                },
                            );
                            self.visit_use(
                                &index_place,
                                operand,
                                unit,
                                &mut gen_set,
                                &mut kill_set,
                            );
                        }
                    }
                    mir::AggregateKind::Adt(def, variant_idx, args, _user_annot, case_index) => {
                        let args = GenericsSpecializer::new(self.tcx(), self.func.generic_args)
                            .specialize_generic_args(args);
                        let adt_def = self.tcx().adt_def(*def);
                        let variant_def = &adt_def.variants()[*variant_idx];
                        if adt_def.is_union() {
                            let case_index = case_index.unwrap_or(FieldIdx::from_usize(0));
                            let field = &variant_def.fields[case_index];
                            let field_ty = type_util::field_ty(self.tcx(), field, args);
                            let union_field = self.tcx().mk_place_field(
                                lplace,
                                case_index,
                                field_ty,
                            );
                            self.visit_use(
                                &union_field,
                                &operands[FieldIdx::from_usize(0)],
                                unit,
                                &mut gen_set,
                                &mut kill_set,
                            );
                        } else {
                            let adt_place = if adt_def.is_enum() {
                                self.visit_set_discriminant(&lplace, *variant_idx);
                                self.tcx().mk_place_downcast(lplace, adt_def, *variant_idx)
                            } else {
                                lplace
                            };

                            for field in 0..operands.len() {
                                let field_idx = FieldIdx::from_usize(field);
                                let field_ty = type_util::field_ty(
                                    self.tcx(),
                                    &variant_def.fields[field_idx],
                                    args,
                                );
                                if type_util::is_zst(self.tcx(), field_ty) {
                                    continue;
                                }
                                let operand = operands.get(field_idx).unwrap();
                                let field_place = self.tcx().mk_place_field(
                                    adt_place,
                                    field_idx,
                                    field_ty,
                                );
                                self.visit_use(
                                    &field_place,
                                    operand,
                                    unit,
                                    &mut gen_set,
                                    &mut kill_set,
                                );
                            }
                        }
                    }
                    mir::AggregateKind::Tuple
                    | mir::AggregateKind::Closure(..)
                    | mir::AggregateKind::Coroutine(..) => {
                        for field in 0..operands.len() {
                            let field_idx = FieldIdx::from_usize(field);
                            let field_ty = type_util::get_field_type(self.tcx(), lty, field);
                            if type_util::is_zst(self.tcx(), field_ty) {
                                continue;
                            }
                            let operand = operands.get(field_idx).unwrap();
                            let field_place = self.tcx().mk_place_field(
                                lplace,
                                field_idx,
                                field_ty,
                            );
                            self.visit_use(
                                &field_place,
                                operand,
                                unit,
                                &mut gen_set,
                                &mut kill_set,
                            );
                        }
                    }
                    mir::AggregateKind::RawPtr(_ty, _mutbl) => {
                        if let Some(operand) = operands.get(FieldIdx::from_usize(0)) {
                            self.visit_use(&lplace, operand, unit, &mut gen_set, &mut kill_set);
                        }
                    }
                    mir::AggregateKind::CoroutineClosure(_def_id, _args) => {
                        // TODO: Handle coroutine closure
                    }
                }
            }
            mir::Rvalue::ShallowInitBox(operand, ty) => {
                let box_ty = Ty::new_box(self.tcx(), *ty);
                let box_ptr = lplace.box_ptr_field(self.tcx(), box_ty);
                self.visit_use(&box_ptr, operand, unit, &mut gen_set, &mut kill_set);
            }
            mir::Rvalue::Cast(cast_kind, operand, _ty) => {
                match cast_kind {
                    mir::CastKind::PointerCoercion(PointerCoercion::MutToConstPointer, _)
                    | mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _)
                    | mir::CastKind::PointerCoercion(PointerCoercion::ArrayToPointer, _)
                    | mir::CastKind::PtrToPtr
                    | mir::CastKind::Transmute => {
                        self.visit_use(&lplace, operand, unit, &mut gen_set, &mut kill_set);
                    }
                    _ => {}
                }
            }
            mir::Rvalue::CopyForDeref(rplace) => {
                self.visit_use(
                    &lplace,
                    &mir::Operand::Copy(*rplace),
                    unit,
                    &mut gen_set,
                    &mut kill_set,
                );
            }
            mir::Rvalue::BinaryOp(bin_op, box (first_operand, _second_operand)) => {
                if let mir::BinOp::Offset = bin_op {
                    self.visit_use(&lplace, first_operand, unit, &mut gen_set, &mut kill_set);
                }
            }
            mir::Rvalue::Discriminant(rplace) => {
                self.visit_discriminant(&lplace, rplace);
            }
            mir::Rvalue::UnaryOp(..) => {}
            _ => {}
        }

        self.update_out_state(&gen_set, &kill_set);
    }

    fn visit_set_discriminant(
        &mut self,
        place: &Place<'tcx>,
        variant_index: rustc_abi::VariantIdx,
    ) {
        self.out_state
            .borrow_mut()
            .set_discriminant(*place, ConstantValue::Constant(variant_index.as_u32()));
    }

    fn visit_storage_live(&mut self, _local: Local) {}

    fn visit_storage_dead(&mut self, local: Local) {
        let dead_place = Place::from(local);
        let kill_set: HashSet<AccessPath<'tcx>> = self
            .aliases_project_from(&dead_place)
            .into_iter()
            .cloned()
            .collect();
        self.update_out_state(&HashSet::new(), &kill_set);
        self.out_state.borrow_mut().constants_mut().retain(|constant, _| constant.place().local != local);
    }

    fn visit_non_diverging_intrinsic(
        &mut self,
        non_diverging_intrinsic: &mir::NonDivergingIntrinsic<'tcx>,
        unit: Unit<'tcx>,
    ) {
        match non_diverging_intrinsic {
            mir::NonDivergingIntrinsic::CopyNonOverlapping(copy_info) => {
                self.visit_copy_non_overlapping(copy_info, unit);
            }
            mir::NonDivergingIntrinsic::Assume(_operand) => {}
        }
    }

    fn visit_use(
        &mut self,
        lplace: &Place<'tcx>,
        operand: &Operand<'tcx>,
        unit: Unit<'tcx>,
        gen_set: &mut HashSet<AccessPath<'tcx>>,
        kill_set: &mut HashSet<AccessPath<'tcx>>,
    ) {
        match operand {
            mir::Operand::Copy(rplace) => {
                self.visit_copy_or_move(lplace, rplace, unit, gen_set, kill_set, false);
            }
            mir::Operand::Move(rplace) => {
                self.visit_copy_or_move(lplace, rplace, unit, gen_set, kill_set, true);
            }
            mir::Operand::Constant(const_op) => {
                self.visit_constant_assign(lplace, const_op);
            }
            mir::Operand::RuntimeChecks(_) => {}
        }
    }

    fn visit_ref_or_rawptr(
        &mut self,
        lplace: &Place<'tcx>,
        rplace: &Place<'tcx>,
        unit: Unit<'tcx>,
        gen_set: &mut HashSet<AccessPath<'tcx>>,
        kill_set: &mut HashSet<AccessPath<'tcx>>,
        _is_rawptr: bool,
    ) {
        let rplace = self.expand_box_deref(rplace);
        let rpath = AccessPath::from_rustc_place(self.acx, unit.func, &rplace);
        // A special case is "y = &(*x)", where we treat it as "y = x".
        if rpath.is_indirect() && rpath.access_elems.len() == 1 {
            self.visit_copy_or_move(
                lplace,
                &Place::from(rplace.local),
                unit,
                gen_set,
                kill_set,
                false,
            );
            return;
        }

        if rplace.is_indirect() {
            // Get the base place that's being dereferenced
            let base_place = rplace.base_place_of_deref(self.tcx()).unwrap();
            // Visit pointer dereference
            self.visit_deref(&base_place);
        }

        // Given a reference statement "y = &(*x).f" and a source "(*x).f.g", we produce a dtarget "(*y).g"
        // by making a dereference place for the lplace and replacing it with the rplace in the source.
        // This also works for the cases where the source is a reference path like "&x.f" or "&(*x).f".
        let src_aliases = self.aliases_project_from(&rplace);
        // Generate new aliases.
        for alias in src_aliases {
            let lplace_deref = self.tcx().mk_place_deref(*lplace);
            let new_alias = alias.derive_with_new_base(self.acx, &rplace, &lplace_deref);
            gen_set.insert(new_alias);
        }
    }

    fn visit_discriminant(&mut self, lplace: &Place<'tcx>, rplace: &Place<'tcx>) {
        if let Some(discriminant) = self.out_state.discriminant(rplace).cloned() {
            self.out_state.borrow_mut().add_constant_value(*lplace, discriminant);
        }
    }

    fn visit_copy_or_move(
        &mut self,
        lplace: &Place<'tcx>,
        rplace: &Place<'tcx>,
        unit: Unit<'tcx>,
        gen_set: &mut HashSet<AccessPath<'tcx>>,
        kill_set: &mut HashSet<AccessPath<'tcx>>,
        is_move: bool,
    ) {
        let rplace = self.expand_box_deref(rplace);

        if rplace.is_indirect() {
            let base_place = rplace.base_place_of_deref(self.tcx()).unwrap();
            self.visit_deref(&base_place);
        }

        let src_aliases = self.aliases_project_from(&rplace);

        // If the rplace is moved, it cannot be used again. We add all the src_aliases to the kill set.
        // Note: we do not kill the aliases projected from parameters to avoid the aliases to be killed in the caller after return flow.
        let is_rplace_param = rplace.is_from_param(self.tcx(), self.func.def_id);
        if is_move & !is_rplace_param {
            kill_set.extend(src_aliases.iter().cloned());
        }

        // Generate new aliases.
        for alias in src_aliases {
            let new_alias = alias.derive_with_new_base(self.acx, &rplace, &lplace);
            gen_set.insert(new_alias);

            // Handle the Store POA
            if lplace.is_indirect() {
                gen_set.extend(
                    points_of_aliasing::load_or_store::process_load_or_store_poa(
                        self.acx, &new_alias, unit,
                    ),
                );
            }

            // Handle the AddressTaken POA
            gen_set.extend(
                points_of_aliasing::address_taken::process_address_taken_poa(
                    self.acx, &new_alias, unit,
                ),
            );

            gen_set.retain(|alias| !alias.is_inactive());
        }

        self.update_constants_after_copy_or_move(lplace, &rplace);
    }

    fn visit_constant_assign(&mut self, lplace: &Place<'tcx>, const_op: &mir::ConstOperand<'tcx>) {
        let mir::ConstOperand { const_, .. } = const_op;
        if let Some(variant_idx) = util::try_to_evaluate_const_std_result_discriminant(const_op) {
            self.out_state
                .borrow_mut()
                .set_discriminant(*lplace, ConstantValue::Constant(variant_idx));
            return;
        }

        let typing_env = rustc_middle::ty::TypingEnv::non_body_analysis(self.tcx(), self.func.def_id);
        if let Some(scalar) = const_.try_eval_scalar_int(self.tcx(), typing_env) {
            let val = scalar.to_uint(scalar.size());
            self.out_state
                .borrow_mut()
                .add_constant_value(*lplace, ConstantValue::Constant(val as u32));
        } else {
            self.out_state.borrow_mut().remove_constant_value(lplace);
        }
    }

    /// Denotes a call to the intrinsic function copy_nonoverlapping, where `src` and `dst` denotes the
    /// memory being read from and written to and size indicates how many bytes are being copied over.
    /// `src` and `dst` must each be a reference, pointer, or `Box` pointing to the same type T.
    /// A copy_nonoverlapping statement can be regarded as a statement like `*dst = *src`.
    fn visit_copy_non_overlapping(
        &mut self,
        copy_info: &mir::CopyNonOverlapping<'tcx>,
        unit: Unit<'tcx>,
    ) {
        let src_ptr = match &copy_info.src {
            mir::Operand::Copy(src_ptr) | mir::Operand::Move(src_ptr) => src_ptr,
            mir::Operand::Constant(_const_op) => return,
            mir::Operand::RuntimeChecks(_) => return,
        };
        let dst_ptr = match &copy_info.dst {
            mir::Operand::Copy(dst_ptr) | mir::Operand::Move(dst_ptr) => dst_ptr,
            mir::Operand::Constant(_const_op) => return,
            mir::Operand::RuntimeChecks(_) => return,
        };
        self.visit_deref(src_ptr);
        let src_deref = self.tcx().mk_place_deref(*src_ptr);
        let dst_deref = self.tcx().mk_place_deref(*dst_ptr);
        let mut gen_set = HashSet::new();
        let mut kill_set = HashSet::new();
        self.visit_copy_or_move(
            &dst_deref,
            &src_deref,
            unit,
            &mut gen_set,
            &mut kill_set,
            false,
        );
        self.update_out_state(&gen_set, &kill_set);
    }

    fn visit_deref(&mut self, deref_place: &Place<'tcx>) {
        self.trans
            .on_pointer_dereference(&mut self.out_state, deref_place);
    }

    fn update_constants_after_copy_or_move(&mut self, lplace: &Place<'tcx>, rplace: &Place<'tcx>) {
        self.out_state.borrow_mut().constants_mut().retain(|constant, _| constant.place() != lplace);

        if let Some(constant) = self.out_state.get_constant_value(rplace).cloned() {
            self.out_state.borrow_mut().add_constant_value(*lplace, constant);
        } else if let Some(discriminant) = self.out_state.discriminant(rplace).cloned() {
            self.out_state.borrow_mut().set_discriminant(*lplace, discriminant);
        }
    }

    fn update_out_state(
        &mut self,
        gen_set: &HashSet<AccessPath<'tcx>>,
        kill_set: &HashSet<AccessPath<'tcx>>,
    ) {
        for alias in kill_set {
            self.out_state.borrow_mut().aliases_mut().remove(alias);
        }
        for alias in gen_set {
            self.out_state.borrow_mut().aliases_mut().insert(*alias);
        }
    }

    fn expand_box_deref(&self, place: &Place<'tcx>) -> Place<'tcx> {
        if self.is_drop_shim_func() {
            place.clone()
        } else if self.tcx().is_mir_available(self.func.def_id) {
            place.expand_box_deref(self.tcx(), self.func.def_id)
        } else {
            place.clone()
        }
    }

    fn aliases_project_from(&self, place: &Place<'tcx>) -> Vec<&AccessPath<'tcx>> {
        aliases_project_from(self.acx, &self.out_state.aliases(), place)
    }
}
