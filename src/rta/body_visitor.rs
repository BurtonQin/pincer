// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use rustc_hir::def_id::DefId;
use rustc_hir::lang_items::LangItem;
use rustc_middle::mir;
use rustc_middle::mir::interpret::{GlobalAlloc, Scalar};
use rustc_middle::ty::{Ty, TyCtxt, TyKind, GenericArgsRef};
use rustc_middle::ty::adjustment::PointerCoercion;
use rustc_span::source_map::Spanned;

use log::*;

use crate::analysis_context::AnalysisContext;
use crate::graph::call_graph::CallSite;
use crate::mir::known_names::KnownNames;
use crate::mir::function::FuncDef;
use crate::util::{self, type_util, generics_specializer::GenericsSpecializer};

use super::RapidTypeAnalysis;

pub struct BodyVisitor<'a, 'rta, 'tcx> {
    pub(crate) rta: &'rta mut RapidTypeAnalysis<'a, 'tcx>,
    pub(crate) func_def: FuncDef<'tcx>,
    pub mir: &'tcx mir::Body<'tcx>,

    /// For specializing the generic type in the method.
    generics_specializer: GenericsSpecializer<'tcx>,
}

impl<'a, 'rta, 'tcx> BodyVisitor<'a, 'rta, 'tcx> {
    pub fn new(
        rta: &'rta mut RapidTypeAnalysis<'a, 'tcx>,
        func_def: FuncDef<'tcx>,
        mir: &'tcx mir::Body<'tcx>,
    ) -> BodyVisitor<'a, 'rta, 'tcx> {
        trace!("Processing function {}", func_def.to_string());
        let generics_specializer = GenericsSpecializer::new(
            rta.acx.tcx,
            func_def.generic_args
        );

        BodyVisitor {
            rta,
            func_def,
            mir,
            generics_specializer,
        }
    }

    #[inline]
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.rta.acx.tcx
    }

    #[inline]
    fn acx(&mut self) -> &mut AnalysisContext<'tcx> {
        self.rta.acx
    }

    pub fn visit_body(&mut self) {
        for bb in self.mir.basic_blocks.indices() {
            self.visit_basic_block(bb);
        }
    }

    fn visit_basic_block(&mut self, bb: mir::BasicBlock) {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &self.mir[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(location, &statements[location.statement_index]);
            location.statement_index += 1;
        }

        if let Some(terminator) = terminator {
            self.visit_terminator(location, &terminator.kind);
        }

        self.rta.num_stmts += statements.len() + 1;
    }

    fn visit_statement(&mut self, _location: mir::Location, statement: &mir::Statement<'tcx>) {
        if let mir::StatementKind::Assign(box (place, rvalue)) = &statement.kind {
            self.visit_assign(place, rvalue);
        }
    }

    fn visit_assign(&mut self, _place: &mir::Place<'tcx>, rvalue: &mir::Rvalue<'tcx>) {
        let mir::Rvalue::Cast(cast_kind, operand, ty) = rvalue else {
            return;
        };
        let specialized_ty = self.generics_specializer.specialize_generic_argument_type(*ty);
        self.visit_operand(operand);
        let source_ty = self.get_rustc_type_for_operand(operand);
        match specialized_ty.kind() {
            TyKind::RawPtr(ty, _)
            | TyKind::Ref(_, ty, _) => {
                if matches!(ty.kind(), TyKind::Dynamic(..)) {
                    let src_deref_type = type_util::get_dereferenced_type(source_ty);
                    if matches!(src_deref_type.kind(), TyKind::Dynamic(..)) {
                        self.rta.add_trait_upcasting_relation(src_deref_type, *ty);
                    } else {
                        trace!("Casting type {:?} to {:?}", src_deref_type, ty);
                        self.rta.add_possible_concrete_type(*ty, src_deref_type);
                    }
                }
            }
            TyKind::FnPtr(..) => {
                if matches!(source_ty.kind(), TyKind::FnDef(..) | TyKind::Closure(..) | TyKind::Coroutine(..)) {
                    trace!("Casting type {:?} to {:?}", source_ty, specialized_ty);
                    self.rta.add_possible_fnptr_target(specialized_ty, source_ty);
                }
            }
            _ => {
                // An unsize pointer cast can also convert structs containing thin pointers to structs
                // containing fat pointers, e.g., Box<MyStruct> -> Box<dyn MyTrait>, and
                // NonNull<MyStruct> -> NonNull<dyn MyTrait>
                if matches!(cast_kind, mir::CastKind::PointerCoercion(PointerCoercion::Unsize, _)) {
                    if let TyKind::Adt(_def, tgt_generic_args) = specialized_ty.kind() {
                        if let TyKind::Adt(_def, src_generic_args) = source_ty.kind() {
                            for (tgt_generic_arg, src_generic_arg) in
                                tgt_generic_args.iter().zip(src_generic_args.iter())
                            {
                                if let Some(tgt_generic_ty) = tgt_generic_arg.as_type() {
                                    if matches!(tgt_generic_ty.kind(), TyKind::Dynamic(..)) {
                                        if let Some(src_generic_ty) = src_generic_arg.as_type() {
                                            if matches!(src_generic_ty.kind(), TyKind::Dynamic(..)) {
                                                trace!("trait_upcasting coercion from {:?} to {:?}", src_generic_ty, tgt_generic_ty);
                                                self.rta.add_trait_upcasting_relation(src_generic_ty, tgt_generic_ty);
                                            } else {
                                                trace!("Casting type {:?} to {:?}", src_generic_ty, tgt_generic_ty);
                                                self.rta.add_possible_concrete_type(tgt_generic_ty, src_generic_ty);
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    fn visit_terminator(
        &mut self,
        location: mir::Location,
        kind: &mir::TerminatorKind<'tcx>,
    ) {
        match kind {
            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                ..
            } => self.visit_call(func, args, destination, location),
            mir::TerminatorKind::Drop { place, .. } => {
                self.visit_drop(place, location);
            }
            _ => {}
        }
    }

    /// Block ends with the call of a function.
    ///
    /// #Arguments
    /// * `func` - The function that's being called
    /// * `args` - Arguments the function is called with. These are owned by the callee, which is
    /// free to modify them. This allows the memory occupied by "by-value" arguments to be reused
    /// across function calls without duplicating the contents.
    /// * `destination` - Destination for the return value. If some, the call returns a value.
    fn visit_call(
        &mut self,
        func: &mir::Operand<'tcx>,
        args: &[Spanned<mir::Operand<'tcx>>],
        _destination: &mir::Place<'tcx>,
        location: mir::Location
    ) {
        match func {
            mir::Operand::Constant(box constant) => {
                match constant.ty().kind() {
                    TyKind::Closure(callee_def_id, gen_args)
                    | TyKind::FnDef(callee_def_id, gen_args)
                    | TyKind::Coroutine(callee_def_id, gen_args) => {
                        self.resolve_call(callee_def_id, gen_args, location, args)
                    }
                    _ => {
                        warn!("Unexpected call: {:?}", constant);
                    }
                }
            }
            mir::Operand::Copy(place)
            | mir::Operand::Move(place) => {
                let fn_item_ty = self.get_rustc_type_for_place(place);
                assert!(fn_item_ty.is_fn());
                match fn_item_ty.kind() {
                    TyKind::FnDef(callee_def_id, callee_gen_args) => {
                        self.resolve_call(callee_def_id, callee_gen_args, location, args)
                    }
                    TyKind::FnPtr(..) => {
                        let callsite = CallSite::new(self.func_def, location);
                        self.rta.add_fnptr_callsite(callsite, fn_item_ty);
                    }
                    _ => {
                        unreachable!();
                    }
                }
            }
            mir::Operand::RuntimeChecks(_) => {
                warn!("Unexpected RuntimeChecks operand as call target");
            }
        }
    }

    /// Process the drop shim for the dropped type: resolve and cache its body,
    /// register call edges, and recursively process nested field drops.
    fn visit_drop(&mut self, place: &mir::Place<'tcx>, _location: mir::Location) {
        let place_ty = self.get_rustc_type_for_place(place);
        self.rta.process_drop_shim(place_ty);
    }

    fn resolve_call(
        &mut self,
        callee_def_id: &DefId,
        gen_args: &GenericArgsRef<'tcx>,
        location: mir::Location,
        _args: &[Spanned<mir::Operand<'tcx>>],
    ) {
        // Specialize callee's generic args from known generic types
        let gen_args = self.generics_specializer.specialize_generic_args(gen_args);
        trace!("Call func {:?}, generic_args: {:?}", callee_def_id, gen_args);

        // Special handlings for thread spawn functions
        if matches!(self.acx().get_known_name_for(*callee_def_id), KnownNames::StdThreadBuilderSpawnUnchecked) {
            let mut new_location = location;
            new_location.statement_index += 1;
            let fn_once_defid = self.tcx().require_lang_item(LangItem::FnOnce, rustc_span::DUMMY_SP);
            self.inline_indirectly_called_function(&fn_once_defid, &gen_args, new_location);

            return;
        }


        if util::is_drop_in_place(self.tcx(), *callee_def_id) {
            // Explicit drop_in_place call: process the drop shim for the
            // pointed-to type and register the call edge.
            let drop_ty = gen_args.types().next().expect("drop_in_place has a type arg");
            self.rta.process_drop_shim(drop_ty);
        }

        if self.acx().is_std_ops_fntrait_call(*callee_def_id) {
            // Fn*::call*
            self.resolve_fntrait_call(callee_def_id, &gen_args, location);
            return;
        }

        if !util::is_trait_method(self.tcx(), *callee_def_id) {
            // Static functions or methods or associated functions not declared on a trait.
            let callee = FuncDef::new_func_def(*callee_def_id, gen_args);
            let callsite = CallSite::new(self.func_def, location);
            self.rta.add_static_callsite(callsite);
            self.rta.add_call_edge(callsite, callee);
        } else if let Some((callee_def_id, callee_gen_args)) =
            util::try_to_devirtualize(self.tcx(), *callee_def_id, gen_args)
        {
            // Methods or associated functions declared on a trait.
            // The called instance can be resolved at compile time.
            let callee = FuncDef::new_func_def(callee_def_id, callee_gen_args);
            let callsite = CallSite::new(self.func_def, location);
            self.rta.add_static_callsite(callsite);
            self.rta.add_call_edge(callsite, callee);
        } else if util::is_dynamic_call(self.tcx(), *callee_def_id, gen_args) {
            // trait method calls where the first argument is of dynamic type
            let dyn_callsite = CallSite::new(self.func_def, location);
            self.rta.add_dyn_callsite(dyn_callsite, *callee_def_id, gen_args);
        } else {
            debug!("Could not resolve function: {:?}, {:?}", callee_def_id, gen_args);
        }
    }

    fn resolve_fntrait_call(
        &mut self,
        callee_def_id: &DefId,
        gen_args: &GenericArgsRef<'tcx>,
        location: mir::Location,
    ) {
        // The fn_traits feature allows for implementation of the Fn* traits for
        // creating custom closure-like types. We first try to devirtualize the callee function
        // https://doc.rust-lang.org/beta/unstable-book/library-features/fn-traits.html
        let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
        // Instance::resolve panics if try_normalize_erasing_regions returns an error.
        // It is hard to figure out exactly when this will be the case.
        if self.tcx().try_normalize_erasing_regions(typing_env, *gen_args).is_err() {
            debug!("Could not resolve fntrait call: {:?}, {:?}", callee_def_id, gen_args);
            return;
        }
        let resolved_instance = rustc_middle::ty::Instance::try_resolve(
            self.tcx(),
            typing_env,
            *callee_def_id,
            gen_args,
        );
        if let Ok(Some(instance)) = resolved_instance {
            let resolved_def_id = instance.def.def_id();

            // If it is a call to a closure, inline the closure call.
            if self.tcx().is_closure_like(resolved_def_id) {
                self.inline_indirectly_called_function(callee_def_id, gen_args, location);
                return;
            }

            // Visit the implementation if its mir is available
            if !self.tcx().is_mir_available(resolved_def_id) {
                // ops::function::Fn*::call* for FnDef, FnPtr, Dynamic... types are unavailable
                // Try to inline the indirect call for these types
                if self.acx().def_in_ops_func_namespace(resolved_def_id) {
                    self.inline_indirectly_called_function(callee_def_id, gen_args, location);
                } else {
                    debug!("Unavailable mir for def_id: {:?}", resolved_def_id);
                }
                return;
            }
            let callsite = CallSite::new(self.func_def, location);
            let callee = FuncDef::new_func_def(resolved_def_id, instance.args);
            self.rta.add_static_callsite(callsite);
            self.rta.add_call_edge(callsite, callee);
        } else {
            debug!("Could not resolve function: {:?}, {:?}", callee_def_id, gen_args);
        }
    }

    /// Fn::call, FnMut::call_mut, FnOnce::call_once all receive two arguments:
    /// 1. Operand of any type that implements Fn|FnMut|FnOnce, a function pointer or closure instance for most cases.
    /// 2. A tuple of argument values for the call.
    /// The tuple is unpacked and the callee is then invoked with its normal function signature.
    /// In the case of calling a closure, the closure signature includes the closure as the first argument.
    ///
    /// All of this happens in code that is not encoded as MIR, so we need built in support for it.
    fn inline_indirectly_called_function(
        &mut self,
        callee_def_id: &DefId,
        gen_args: &GenericArgsRef<'tcx>,
        location: mir::Location,
    ) {
        // If the first substitution is a closure or FnDef, we can inline the closure call directly.
        // The generic args should have been specialized when added to the type cache.
        let first_arg_ty = gen_args.types().next().expect("Expect type substitution in Fn* invocation");
        match first_arg_ty.kind() {
            TyKind::FnDef(def_id, fn_gen_args) => {
                // Fn*::call* itself cannot be the first argument as it is a trait method without
                // a implementation, therefore we do not need to worry about the recursive std_ops_func_call.
                let (def_id, fn_gen_args) = util::resolve_fn_def(self.tcx(), *def_id, fn_gen_args);
                let callsite = CallSite::new(self.func_def, location);
                let callee = FuncDef::new_func_def(def_id, fn_gen_args);
                self.rta.add_static_callsite(callsite);
                self.rta.add_call_edge(callsite, callee);
            }
            TyKind::Closure(def_id, fn_gen_args)
            | TyKind::Coroutine(def_id, fn_gen_args) => {
                let callsite = CallSite::new(self.func_def, location);
                let callee = FuncDef::new_func_def(*def_id, fn_gen_args);
                self.rta.add_static_callsite(callsite);
                self.rta.add_call_edge(callsite, callee);
            }
            TyKind::FnPtr(..) => {
                let callsite = CallSite::new(self.func_def, location);
                self.rta.add_fnptr_callsite(callsite, first_arg_ty);
            }
            // e.g. &dyn FnMut(..)
            TyKind::Dynamic(..) => {
                let callsite = CallSite::new(self.func_def, location);
                self.rta.add_dyn_fntrait_callsite(callsite, *callee_def_id, gen_args);
            }
            _ => {
                warn!("Unexpected first argument type in std::ops::call!");
            }
        }
    }

    fn get_rustc_type_for_operand(&mut self, operand: &mir::Operand<'tcx>) -> Ty<'tcx> {
        let ty = self.generics_specializer.specialize_generic_argument_type(
            operand.ty(&self.mir.local_decls, self.tcx())
        );
        match ty.kind() {
            TyKind::FnDef(def_id, gen_args) => {
                let (def_id, gen_args) = util::resolve_fn_def(self.tcx(), *def_id, gen_args);
                Ty::new_fn_def(self.tcx(), def_id, gen_args)
            }
            _ => ty,
        }
    }

    fn get_rustc_type_for_place(&self, place: &mir::Place<'tcx>) -> Ty<'tcx> {
        self.generics_specializer.specialize_generic_argument_type(
            place.ty(&self.mir.local_decls, self.tcx()).ty
        )
    }

    fn visit_operand(&mut self, operand: &mir::Operand<'tcx>) {
        if let mir::Operand::Constant(const_op) = operand {
            let mir::ConstOperand { const_, .. } = &**const_op;
            match const_ {
                mir::Const::Ty(_ty, _c) => {},
                mir::Const::Unevaluated(c, ty) => {
                    self.visit_unevaluated_const(c, *ty);
                }
                mir::Const::Val(v, _ty) => {
                    self.visit_const_value(*v);
                }
            }
        }
    }

    fn visit_unevaluated_const(
        &mut self,
        unevaluated: &mir::UnevaluatedConst<'tcx>,
        ty: Ty<'tcx>,
    ) {
        trace!("Visiting unevaluated constant: {unevaluated:?} {ty:?}");
        if unevaluated.promoted.is_some() {
            return;
        }

        let mut def_id = unevaluated.def;
        let args = self.generics_specializer.specialize_generic_args(unevaluated.args);
        if !args.is_empty() {
            let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
            if let Ok(Some(instance)) = rustc_middle::ty::Instance::try_resolve(
                self.tcx(),
                typing_env,
                def_id,
                args,
            ) {
                def_id = instance.def.def_id();
            }
            if self.tcx().is_mir_available(def_id) {
                self.rta.referenced_statics.insert(def_id);
            }
        }
    }

    fn visit_const_value(&mut self, val: mir::ConstValue) {
        if let mir::ConstValue::Scalar(Scalar::Ptr(ptr, _size)) = val {
            if let Some(GlobalAlloc::Static(def_id)) = self.tcx().try_get_global_alloc(ptr.provenance.alloc_id()) {
                self.rta.referenced_statics.insert(def_id);
            }
        }
    }
}
