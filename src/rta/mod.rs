// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

pub mod body_visitor;

use std::collections::{HashSet, HashMap};
use std::time::{Instant, Duration};
use log::*;

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::ty::{FnSigTys, GenericArgsRef, Ty, TyCtxt};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::CallGraph;
use crate::graph::call_graph::CallSite;
use crate::mir::drop_shim;
use crate::mir::function::FuncDef;
use crate::util::{self, type_util, chunked_queue};
use crate::rta::body_visitor::BodyVisitor;

pub struct RapidTypeAnalysis<'a, 'tcx> {
    /// The analysis context
    pub(crate) acx: &'a mut AnalysisContext<'tcx>,
    /// The call graph
    pub call_graph: CallGraph<'tcx>,
    /// Iterator for reachable functions
    pub(crate) reachable_func_iter: chunked_queue::IterCopied<FuncDef<'tcx>>,

    /// Records the functions that have been visited
    pub(crate) visited_functions: HashSet<FuncDef<'tcx>>,

    pub static_callsites: HashSet<CallSite<'tcx>>,
    pub dyn_callsites: HashMap<Ty<'tcx>, HashSet<(CallSite<'tcx>, DefId, GenericArgsRef<'tcx>)>>,
    pub dyn_fntrait_callsites: HashMap<Ty<'tcx>, HashSet<(CallSite<'tcx>, DefId, GenericArgsRef<'tcx>)>>,
    pub fnptr_callsites: HashMap<Ty<'tcx>, HashSet<CallSite<'tcx>>>,

    pub dynamic_to_possible_concrete_types: HashMap<Ty<'tcx>, HashSet<Ty<'tcx>>>,
    pub fnptr_sig_to_possible_targets: HashMap<FnSigTys<TyCtxt<'tcx>>, HashSet<Ty<'tcx>>>,
    pub trait_upcasting_relations: HashMap<Ty<'tcx>, HashSet<Ty<'tcx>>>,
    /// Whether new trait upcasting relations were added since the last solve.
    has_new_trait_upcasting: bool,

    /// Static items (global variables and resolved const items) referenced in reachable functions.
    pub referenced_statics: HashSet<DefId>,

    pub num_stmts: usize,
    pub analysis_time: Duration,
}

impl<'a, 'tcx> RapidTypeAnalysis<'a, 'tcx> {
    pub fn new(acx: &'a mut AnalysisContext<'tcx>) -> Self {
        let call_graph = CallGraph::new();
        let reachable_func_iter = call_graph.reachable_funcs_iter();
        RapidTypeAnalysis {
            acx,
            call_graph,
            reachable_func_iter,
            visited_functions: HashSet::new(),
            static_callsites: HashSet::new(),
            dyn_callsites: HashMap::new(),
            dyn_fntrait_callsites: HashMap::new(),
            fnptr_callsites: HashMap::new(),
            dynamic_to_possible_concrete_types: HashMap::new(),
            fnptr_sig_to_possible_targets: HashMap::new(),
            trait_upcasting_relations: HashMap::new(),
            has_new_trait_upcasting: false,
            referenced_statics: HashSet::new(),
            num_stmts: 0,
            analysis_time: Duration::ZERO,
        }
    }

    #[inline]
    fn tcx(&self) -> TyCtxt<'tcx> {
        self.acx.tcx
    }

    pub fn analyze(&mut self) {
        let now = Instant::now();

        // add the entry points to the call graph
        for &func_id in &self.acx.entry_funcs {
            let entry_func_def = FuncDef::new_func_def(func_id, self.tcx().mk_args(&vec![]));
            self.call_graph.add_func(entry_func_def);
        }

        self.iteratively_process_reachable_functions();

        self.analysis_time = now.elapsed();
        info!(
            "Rapid Type Analysis completed in {}.",
            humantime::format_duration(self.analysis_time)
        );
    }

    fn iteratively_process_reachable_functions(&mut self) {
        while self.process_reachable_functions() {
            self.solve_trait_upcasting();
            self.solve_dyn_callsites();
            self.solve_dyn_fntrait_callsites();
            self.solve_fnptr_callsites();
        }
    }

    /// Process statements of reachable functions.
    fn process_reachable_functions(&mut self) -> bool {
        let mut has_new_functions = false;
        while let Some(func_def) = self.reachable_func_iter.next() {
            has_new_functions = true;
            if !self.visited_functions.contains(&func_def) {
                self.visited_functions.insert(func_def);

                let def_id = func_def.def_id;
                let generic_args = &func_def.generic_args;

                if !self.tcx().is_mir_available(def_id) {
                    trace!("Unavailable mir for def_id: {:?}", def_id);
                    continue;
                }

                self.promote_constants(def_id, generic_args);
                let mir = self.tcx().optimized_mir(def_id);
                let mut bv = BodyVisitor::new(self, func_def, mir);
                bv.visit_body();
            }
        }
        has_new_functions
    }


    fn solve_trait_upcasting(&mut self) {
        if !self.has_new_trait_upcasting {
            return;
        }
        self.has_new_trait_upcasting = false;

        // To further optimize, we can incrementally update concrete types only for
        // dynamic types involved in newly added trait upcasting relations, rather than
        // iterating over all relations each time.
        let mut changed = true;
        let mut propagations = Vec::new();
        while changed {
            changed = false;
            for (src_dyn_ty, tgt_dyn_ty_set) in &self.trait_upcasting_relations {
                if let Some(src_concrete_types) = self.dynamic_to_possible_concrete_types.get(src_dyn_ty) {
                    for tgt_dyn_ty in tgt_dyn_ty_set {
                        for src_concrete_ty in src_concrete_types {
                            propagations.push((*tgt_dyn_ty, *src_concrete_ty));
                        }
                    }
                }
            }
            for (tgt_dyn_ty, concrete_ty) in propagations.drain(..) {
                changed |= self.dynamic_to_possible_concrete_types
                    .entry(tgt_dyn_ty)
                    .or_default()
                    .insert(concrete_ty);
            }
        }
    }

    fn solve_dyn_callsites(&mut self) {
        let tcx = self.acx.tcx;
        for (dyn_ty, concrete_types) in &self.dynamic_to_possible_concrete_types {
            if let Some(dyn_callsites_tuple) = self.dyn_callsites.get(dyn_ty) {
                for (callsite, callee_def_id, gen_args) in dyn_callsites_tuple {
                    for concrete_type in concrete_types {
                        let mut replaced_args = gen_args.to_vec();
                        replaced_args[0] = (*concrete_type).into();
                        let replaced_args = tcx.mk_args(&replaced_args);
                        // Devirtualize the callee function
                        if let Some((callee_def_id, gen_args)) = util::try_to_devirtualize(
                            tcx,
                            *callee_def_id,
                            replaced_args,
                        ) {
                            let func_def = FuncDef::new_func_def(callee_def_id, gen_args);
                            self.call_graph.add_edge(*callsite, callsite.func, func_def);
                        } else {
                            debug!("Could not resolve function: {:?}, {:?}", callee_def_id, replaced_args);
                        }
                    }
                }
            }
        }
    }

    fn solve_dyn_fntrait_callsites(&mut self) {
        let tcx = self.acx.tcx;
        for (dyn_fntrait_ty, callsites_tuple) in &self.dyn_fntrait_callsites {
            if let Some(concrete_types) = self.dynamic_to_possible_concrete_types.get(dyn_fntrait_ty) {
                for concrete_type in concrete_types {
                    match concrete_type.kind() {
                        rustc_middle::ty::TyKind::FnDef(def_id, gen_args)
                        | rustc_middle::ty::TyKind::Closure(def_id, gen_args)
                        | rustc_middle::ty::TyKind::Coroutine(def_id, gen_args) => {
                            for (callsite, _, _) in callsites_tuple {
                                let (def_id, gen_args) = util::resolve_fn_def(tcx, *def_id, gen_args);
                                let func_def = FuncDef::new_func_def(def_id, gen_args);
                                self.call_graph.add_edge(*callsite, callsite.func, func_def);
                            }
                        }
                        rustc_middle::ty::TyKind::FnPtr(..) => {
                            let fnptr_type = tcx.erase_and_anonymize_regions(*concrete_type);
                            for (callsite, _, _) in callsites_tuple {
                                self.fnptr_callsites.entry(fnptr_type).or_default().insert(*callsite);
                            }
                        }
                        _ => {
                            for (callsite, callee_def_id, gen_args) in callsites_tuple {
                                let mut replaced_args = gen_args.to_vec();
                                replaced_args[0] = (*concrete_type).into();
                                let replaced_args = tcx.mk_args(&replaced_args);

                                let resolved_instance = rustc_middle::ty::Instance::try_resolve(
                                    tcx,
                                    rustc_middle::ty::TypingEnv::fully_monomorphized(),
                                    *callee_def_id,
                                    replaced_args,
                                );
                                if let Ok(Some(instance)) = resolved_instance {
                                    let resolved_def_id = instance.def.def_id();
                                    let instance_args = instance.args;
                                    if tcx.is_mir_available(resolved_def_id) {
                                        let func_def = FuncDef::new_func_def(resolved_def_id, instance_args);
                                        self.call_graph.add_edge(*callsite, callsite.func, func_def);
                                    } else {
                                        debug!("Unavailable mir for def_id: {:?}", resolved_def_id);
                                    }
                                } else {
                                    debug!("Could not resolve function: {:?}, {:?}", callee_def_id, replaced_args);
                                }
                            }
                        }
                    }
                }
            } else {
                warn!("Fail to find concrete types for dyn fn* type: {:?}", dyn_fntrait_ty);
            }
        }
    }

    fn solve_fnptr_callsites(&mut self) {
        let tcx = self.acx.tcx;
        for (fnptr_type, callsites) in &self.fnptr_callsites {
            if let rustc_middle::ty::TyKind::FnPtr(fn_sig, _) = fnptr_type.kind() {
                for (fn_sig2, possible_targets) in &self.fnptr_sig_to_possible_targets {
                    if type_util::matched_fn_sig(tcx, fn_sig.skip_binder(), *fn_sig2) {
                        for callsite in callsites {
                            for fn_item_ty in possible_targets {
                                match fn_item_ty.kind() {
                                    rustc_middle::ty::TyKind::FnDef(def_id, gen_args)
                                    | rustc_middle::ty::TyKind::Closure(def_id, gen_args)
                                    | rustc_middle::ty::TyKind::Coroutine(def_id, gen_args) => {
                                        let func_def = FuncDef::new_func_def(*def_id, gen_args);
                                        self.call_graph.add_edge(*callsite, callsite.func, func_def);
                                    }
                                    _ => {
                                        unreachable!();
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }


    pub fn promote_constants(&mut self, def_id: DefId, _gen_args: GenericArgsRef<'tcx>) {
        for (_ordinal, _constant_mir) in self.tcx().promoted_mir(def_id).iter().enumerate() {
            // TODO
        }
    }

    pub fn visit_static(&mut self, def_id: DefId) {
        if !self.tcx().is_mir_available(def_id) {
            return;
        }

        let func_def = FuncDef::new_func_def(def_id, self.tcx().mk_args(&[]));
        if !self.visited_functions.contains(&func_def) {
            let def = rustc_middle::ty::InstanceKind::Item(def_id);
            let mir = self.tcx().instance_mir(def);
            let mut bv = BodyVisitor::new(self, func_def, mir);
            bv.visit_body();
            self.visited_functions.insert(func_def);
        }
    }

    pub fn add_static_callsite(&mut self, callsite: CallSite<'tcx>) {
        self.static_callsites.insert(callsite);
    }

    pub fn add_dyn_callsite(
        &mut self, 
        callsite: CallSite<'tcx>, 
        callee_def_id: DefId, 
        callee_gen_args: GenericArgsRef<'tcx>
    ) {
        let dyn_type = type_util::strip_auto_traits(
            self.tcx(), 
            self.tcx().erase_and_anonymize_regions(callee_gen_args[0].expect_ty())
        );
        trace!("Add dyn callsite: {:?}->{:?}", dyn_type, callsite);
        assert!(matches!(dyn_type.kind(), rustc_middle::ty::TyKind::Dynamic(..)));
        self.dyn_callsites.entry(dyn_type).or_default().insert((callsite, callee_def_id, callee_gen_args));
    }

    pub fn add_dyn_fntrait_callsite(
        &mut self, 
        callsite: CallSite<'tcx>, 
        callee_def_id: DefId, 
        callee_gen_args: GenericArgsRef<'tcx>
    ) {
        let dyn_fntrait_type = type_util::strip_auto_traits(
            self.tcx(), 
            self.tcx().erase_and_anonymize_regions(callee_gen_args[0].expect_ty())
        );
        trace!("Add dyn_fn_trait callsite: {:?}->{:?}", dyn_fntrait_type, callsite);
        self.dyn_fntrait_callsites.entry(dyn_fntrait_type).or_default().insert((callsite, callee_def_id, callee_gen_args));
    }

    pub fn add_fnptr_callsite(&mut self, callsite: CallSite<'tcx>, fnptr_type: Ty<'tcx>) {
        let fnptr_type =  self.tcx().erase_and_anonymize_regions(fnptr_type);
        trace!("Add fnptr callsite: {:?} -> {:?}", fnptr_type, callsite);
        self.fnptr_callsites.entry(fnptr_type).or_default().insert(callsite);
    }


    pub fn add_possible_concrete_type(&mut self, dyn_ty: Ty<'tcx>, concrete_ty: Ty<'tcx>) {
        let dyn_ty = type_util::strip_auto_traits(
            self.tcx(), 
            self.tcx().erase_and_anonymize_regions(dyn_ty)
        );
        let concrete_ty = self.tcx().erase_and_anonymize_regions(concrete_ty);
        self.dynamic_to_possible_concrete_types.entry(dyn_ty).or_default().insert(concrete_ty);
    }

    pub fn add_possible_fnptr_target(&mut self, fnptr_type: Ty<'tcx>, fn_item_type: Ty<'tcx>) {
        let fnptr_type = self.tcx().erase_and_anonymize_regions(fnptr_type);
        let fn_item_type = self.tcx().erase_and_anonymize_regions(fn_item_type);
        trace!("Possible target fn item for fnptr type {:?}, {:?}", fnptr_type, fn_item_type);
        if let rustc_middle::ty::TyKind::FnPtr(fnsig, _) = fnptr_type.kind() {
            self.fnptr_sig_to_possible_targets.entry(fnsig.skip_binder()).or_default().insert(fn_item_type);
        } else {
            unreachable!();
        }
    }

    pub fn add_trait_upcasting_relation(&mut self, src_dyn_ty: Ty<'tcx>, tgt_dyn_ty: Ty<'tcx>) {
        let src_dyn_ty = type_util::strip_auto_traits(
            self.tcx(), 
            self.tcx().erase_and_anonymize_regions(src_dyn_ty)
        );
        let tgt_dyn_ty = type_util::strip_auto_traits(
            self.tcx(), 
            self.tcx().erase_and_anonymize_regions(tgt_dyn_ty)
        );
        if src_dyn_ty != tgt_dyn_ty {
            info!("trait_upcasting coercion from {:?} to {:?}", src_dyn_ty, tgt_dyn_ty);
            if self.trait_upcasting_relations.entry(src_dyn_ty).or_default().insert(tgt_dyn_ty) {
                self.has_new_trait_upcasting = true;
            }
        }
    }

    pub fn add_call_edge(&mut self, callsite: CallSite<'tcx>, callee: FuncDef<'tcx>) {
        self.call_graph.add_edge(callsite, callsite.func, callee);
    }

    pub fn add_reachable_func(&mut self, func: FuncDef<'tcx>) {
        self.call_graph.add_func(func);
    }

    /// Process a drop shim: add as reachable, resolve and cache the body,
    /// register the Drop::drop call edge, and recursively process nested
    /// field drop shims.
    pub fn process_drop_shim(&mut self, ty: Ty<'tcx>) {
        let func_def = drop_shim::drop_func_def(self.tcx(), ty);
        if self.visited_functions.contains(&func_def) {
            return;
        }
        self.visited_functions.insert(func_def);
        self.call_graph.add_func(func_def);

        let body = self.acx.drop_shim_body(func_def);

        // Register the Drop::drop impl call edge if T: Drop
        if let Some((drop_impl_id, drop_gen_args)) = type_util::find_drop_impl(self.tcx(), ty) {
            let drop_impl = FuncDef::new_func_def(drop_impl_id, drop_gen_args);
            self.call_graph.add_func(drop_impl);
            // Find the Call terminator in the body and register the edge
            for (bb, bb_data) in body.basic_blocks.iter_enumerated() {
                if bb_data.is_cleanup { continue; }
                if matches!(bb_data.terminator().kind, mir::TerminatorKind::Call { .. }) {
                    let callsite = CallSite::new(func_def, mir::Location {
                        block: bb,
                        statement_index: bb_data.statements.len(),
                    });
                    self.call_graph.add_edge(callsite, func_def, drop_impl);
                }
            }
        }

        // Recursively process nested field drop shims.
        // We cannot use BodyVisitor here because its GenericsSpecializer
        // incorrectly remaps type params in drop shim bodies.
        if !type_util::is_manually_drop(ty) {
            let typing_env = rustc_middle::ty::TypingEnv::fully_monomorphized();
            for (_fld_proj, field_ty) in drop_shim::get_field_and_types(self.tcx(), ty) {
                if !type_util::contains_alias_projection(self.tcx(), field_ty)
                    && !field_ty.needs_drop(self.tcx(), typing_env)
                {
                    continue;
                }
                self.process_drop_shim(field_ty);
            }
        }
    }
}

