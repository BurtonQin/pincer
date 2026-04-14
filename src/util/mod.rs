// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

pub mod cache;
pub mod cached_hash;
pub mod chunked_queue;
pub mod dot;
pub mod generics_specializer;
pub mod interners;
pub mod mem_watcher;
pub mod results_dumper;
pub mod options;
pub mod test_util;
pub mod type_util;

use std::io::Write;
use log::*;

use rustc_hir::{Node, LangItem};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::ty::{self, Ty, TyCtxt, TyKind, GenericArgsRef, TypeVisitableExt};
use rustc_middle::mir;
use rustc_middle::mir::TerminatorKind;
use std::collections::VecDeque;
use crate::analysis_context::AnalysisContext;
use crate::mir::function::FuncDef;
use crate::mir::unit::Unit;
use std::collections::HashSet;

/// Returns the location of the rust system binaries that are associated with this build of pincer.
/// The location is obtained by looking at the contents of the environmental variables that were
/// set at the time pincer was compiled. If the rust compiler was installed by rustup, the variables
/// `RUSTUP_HOME` and `RUSTUP_TOOLCHAIN` are used and these are set by the compiler itself.
/// If the rust compiler was compiled and installed in some other way, for example from a source
/// enlistment, then the `RUST_SYSROOT` variable must be set in the environment from which pincer
/// is compiled.
pub fn find_sysroot() -> String {
    let home = option_env!("RUSTUP_HOME");
    let toolchain = option_env!("RUSTUP_TOOLCHAIN");
    match (home, toolchain) {
        (Some(home), Some(toolchain)) => format!("{home}/toolchains/{toolchain}"),
        _ => match option_env!("RUST_SYSROOT") {
            Some(sys_root) => sys_root.to_owned(),
            None => {
                panic!(
                    "Could not find sysroot. Specify the RUST_SYSROOT environment variable, \
                    or use rustup to set the compiler to use for Mirai",
                )
            }
        },
    }
}

/// Dumps a human readable MIR redendering of the function with the given DefId to standard output.
pub fn pretty_print_mir(tcx: TyCtxt<'_>, def_id: DefId) {
    if !matches!(
        tcx.def_kind(def_id),
        rustc_hir::def::DefKind::Struct | rustc_hir::def::DefKind::Variant
    ) {
        let mut stdout = std::io::stdout();
        stdout.write_fmt(format_args!("{:?}", def_id)).unwrap();
        rustc_middle::mir::write_mir_pretty(tcx, Some(def_id), &mut stdout).unwrap();
        let _ = stdout.flush();
    }
}

pub fn parse_func_name_from_def_id(def_id: DefId) -> String {
    let def_id_str = format!("{:?}", def_id);
    if let Some(last) = def_id_str.rsplit("::").next() {
        last.trim_end_matches(')').to_string()
    } else {
        def_id_str
    }
}

pub fn is_drop_in_place(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    tcx.is_lang_item(def_id, LangItem::DropInPlace)
}

/// Returns true if the function identified by `def_id` is defined as part of a trait.
#[inline]
pub fn is_trait_method(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    if tcx.trait_of_item(def_id).is_some() {
        true
    } else {
        false
    }
}

/// Returns true if the function identified by `def_id` is defined in the Rust Standard Library.
pub fn is_std_lib_func(tcx: TyCtxt<'_>, def_id: DefId) -> bool {
    let crate_name = tcx.crate_name(def_id.krate);
    match crate_name.as_str() {
        "alloc" | "core" | "std" => true,
        _ => false,
    }
}

pub fn is_higher_order_function(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    let fn_ty = tcx.type_of(def_id).skip_binder();
    if fn_ty.is_fn() {
        let fn_sig = fn_ty.fn_sig(tcx).skip_binder();
        for param_ty in fn_sig.inputs() {
            if contains_function(*param_ty, tcx) {
                return true;
            }
        }
    }
    false
}

/// Returns true if the given type is a function, a closure, a generator, or a struct with
/// a field that is (or contains) a function in this sense.
/// This does not traverse references, so the answer is approximate.
pub fn contains_function<'tcx>(ty: Ty<'tcx>, tcx: TyCtxt<'tcx>) -> bool {
    if ty.is_fn() || ty.is_closure() || ty.is_coroutine() {
        return true;
    }
    if let TyKind::Adt(def, args) = ty.kind() {
        for variant in def.variants().iter() {
            for field in variant.fields.iter() {
                let field_ty = field.ty(tcx, args);
                if contains_function(field_ty, tcx) {
                    return true;
                }
            }
        }
    }
    false
}

/// Returns true if the function identified by def_id is a public function.
pub fn is_public(def_id: DefId, tcx: TyCtxt<'_>) -> bool {
    if tcx.hir().get_if_local(def_id).is_some() {
        let def_id = def_id.expect_local();
        match tcx
            .resolutions(())
            .visibilities_for_hashing
            .iter()
            .find(|(id, _)| *id == def_id)
        {
            Some((_, vis)) => vis.is_public(),
            None => {
                let hir_id = tcx.local_def_id_to_hir_id(def_id);
                match tcx.hir_node(hir_id) {
                    Node::Expr(rustc_hir::Expr {
                        kind: rustc_hir::ExprKind::Closure { .. },
                        ..
                    })
                    | Node::Item(rustc_hir::Item {
                        kind:
                            rustc_hir::ItemKind::Use(_, rustc_hir::UseKind::ListStem)
                            | rustc_hir::ItemKind::TyAlias(..),
                        ..
                    }) => ty::Visibility::Restricted(tcx.parent_module(hir_id).to_def_id())
                        .is_public(),
                    Node::ImplItem(..) => {
                        let parent_def_id: LocalDefId = tcx.hir().get_parent_item(hir_id).def_id;
                        match tcx.hir_node_by_def_id(parent_def_id) {
                            Node::Item(rustc_hir::Item {
                                kind:
                                    rustc_hir::ItemKind::Impl(rustc_hir::Impl {
                                        of_trait: Some(tr),
                                        ..
                                    }),
                                ..
                            }) => tr
                                .path
                                .res
                                .opt_def_id()
                                .map_or_else(
                                    || {
                                        tcx.sess.dcx().span_delayed_bug(
                                            tr.path.span,
                                            "trait without a def-id",
                                        );
                                        ty::Visibility::Public
                                    },
                                    |def_id| tcx.visibility(def_id),
                                )
                                .is_public(),
                            _ => false,
                        }
                    }
                    _ => false,
                }
            }
        }
    } else {
        false
    }
}

/// Returns true if the call to (`callee_def_id`, `callee_substs`) is a dynamic call.
#[inline]
pub fn is_dynamic_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    callee_def_id: DefId,
    callee_substs: GenericArgsRef<'tcx>,
) -> bool {
    if !is_trait_method(tcx, callee_def_id) {
        return false;
    }
    let arg0_ty = callee_substs
        .types()
        .next()
        .expect("Expect `Self` substition in trait method invocation");
    if matches!(arg0_ty.kind(), TyKind::Dynamic(..)) {
        true
    } else {
        false
    }
}


/// Try to resolve the function with `def_id` and `gen_args`. 
/// 
/// If the function is not a trait method, (`def_id`, `gen_args`) is returned
/// directly. Otherwise, the function is devirtualized to a specific implementation.
pub fn resolve_fn_def<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    gen_args: GenericArgsRef<'tcx>,
) -> (DefId, GenericArgsRef<'tcx>) {
    if tcx.is_mir_available(def_id) && !is_trait_method(tcx, def_id) {
        (def_id, gen_args)
    } else if let Some((resolved_def_id, resolved_substs)) =
        try_to_devirtualize(tcx, def_id, gen_args)
    {
        (resolved_def_id, resolved_substs)
    } else {
        // if the function cannot be resolved, 
        // return the original (def_id, gen_args) pair directly.
        (def_id, gen_args)
    }
}

/// Try to devirtualize a trait method with `def_id` and `gen_args`. 
/// 
/// Returns `None` if the given `def_id` does not correspond to a trait method or 
/// we cannot resolve the trait method to a specific instance. For example, the 
/// first gen_arg is a dynamic type.
pub fn try_to_devirtualize<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
    gen_args: GenericArgsRef<'tcx>,
) -> Option<(DefId, GenericArgsRef<'tcx>)> {
    if !is_trait_method(tcx, def_id) {
        return None;
    }

    // A trait method cannot be devirtualized when the first gen_arg corresponds
    // to a dynamic type.
    let arg0_ty = gen_args
        .types()
        .next()
        .expect("Expect `Self` substition in trait method invocation");
    if matches!(arg0_ty.kind(), TyKind::Dynamic(..)) {
        return None;
    }

    let param_env = rustc_middle::ty::ParamEnv::reveal_all();
    let abi = tcx
        .type_of(def_id)
        .skip_binder()
        .fn_sig(tcx)
        .abi();    
    let resolved_instance = if abi == rustc_target::spec::abi::Abi::Rust {
        // Instance::resolve panics if try_normalize_erasing_regions returns an error.
        // It is difficult to determine exactly when this error will occur.
        if tcx.try_normalize_erasing_regions(param_env, gen_args).is_err() {
            None
        } else if gen_args.has_param() {
            // Types with unresolved params can cause panics inside rustc's query system
            // that leave queries in an active state, breaking incremental cache serialization.
            None
        } else {
            // Even after the normalization check passes, Instance::try_resolve can still panic
            // due to internal compiler issues. We catch any panic and return None to handle
            // cases gracefully where the call cannot be resolved.
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                rustc_middle::ty::Instance::try_resolve(
                    tcx,
                    param_env,
                    def_id,
                    gen_args,
                )
            })).ok()
        }
    } else {
        None
    };
    if let Some(Ok(Some(instance))) = resolved_instance {
        let resolved_def_id = instance.def.def_id();
        return Some((resolved_def_id, instance.args));
    }
    None
}

/// Evaluate the variant idx for an enum constant, like `const std::result::Result::<(), std::collections::TryReserveError>::Ok(())`.
pub fn try_to_evaluate_const_std_result_discriminant(const_op: &mir::ConstOperand<'_>) -> Option<u32> {
    let mir::ConstOperand { const_, .. } = const_op;
    if let mir::Const::Val(_const_val, const_ty) = const_ {
        if let rustc_middle::ty::TyKind::Adt(adt_def, _) = const_ty.kind() {
            if adt_def.is_enum() {
                // Parse the debug representation to identify the variant
                let const_debug = format!("{:?}", const_op);
                trace!("Enum constant: {}", const_debug);
                
                // For std::result::Result, check if it's Ok or Err
                if const_debug.contains("const std::result::Result::") {
                    if const_debug.contains("::Ok(") {
                        trace!("Found Result::Ok variant, returning index 0");
                        return Some(0);
                    } else if const_debug.contains("::Err(") {
                        trace!("Found Result::Err variant, returning index 1");
                        return Some(1);
                    }
                }
                
                // For other enums, we can add more specific parsing logic here if needed
                // For now, just log that we found an enum but couldn't parse it
                trace!("Found enum constant but couldn't parse variant: {}", const_debug);
            }
        }
    }
    None
}

pub fn enum_discriminant_of<'tcx>(place: &mir::Place<'tcx>, block_data: &mir::BasicBlockData<'tcx>) -> Option<mir::Place<'tcx>> {
    let mir::BasicBlockData {
        ref statements,
        ..
    } = block_data;
    for statement in statements {
        if let mir::StatementKind::Assign(box (lplace, rvalue)) = &statement.kind {
            if lplace == place {
                if let mir::Rvalue::Discriminant(rplace) = rvalue {
                    return Some(rplace.clone());
                }
            }
        }
    }
    return None;
}

pub fn call_may_unwind<'tcx>(acx: &AnalysisContext<'tcx>, callsite: &Unit<'tcx>) -> bool {
    if let Some(call_graph) = &acx.call_graph {
        let callees: Vec<crate::mir::function::FuncDef<'tcx>> = call_graph.get_callees(&callsite);           
        if callees.is_empty() {
            // If we can't determine callees, conservatively assume it may unwind
            return true;
        }
        
        // Check if any callee may unwind resume
        for callee in callees {
            if may_unwind_resume(acx, callee) {
                return true;
            }
        }
        return false;
    } else {
        return true;
    }
}

pub fn may_unwind_resume<'tcx>(acx: &AnalysisContext<'tcx>, func_def: FuncDef<'tcx>) -> bool {
    // Check cache first
    if let Some(&result) = acx.may_unwind_resume.borrow().get(&func_def) {
        return result;
    }

    // If MIR is not available, conservatively assume it may unwind
    if !acx.tcx.is_mir_available(func_def.def_id) {
        acx.may_unwind_resume.borrow_mut().insert(func_def, true);
        return true;
    }

    let mut visited = HashSet::new();
    let result = may_unwind_resume_impl(acx, func_def, &mut visited);
    
    // Cache the result
    acx.may_unwind_resume.borrow_mut().insert(func_def, result);
    result
}

fn may_unwind_resume_impl<'tcx>(acx: &AnalysisContext<'tcx>, func_def: FuncDef<'tcx>, visited: &mut HashSet<FuncDef<'tcx>>) -> bool {
    // Check cache first 
    if let Some(&result) = acx.may_unwind_resume.borrow().get(&func_def) {
        return result;
    }
    // Check if we're already analyzing this function (recursion detection)
    if visited.contains(&func_def) {
        return false;
    }

    if !acx.tcx.is_mir_available(func_def.def_id) {
        return false;
    }

    // Add this function to the visited set
    visited.insert(func_def);

    let mir = acx.tcx.optimized_mir(func_def.def_id);
    
    // Use BFS to traverse all reachable basic blocks
    let mut bb_visited = std::collections::HashSet::new();
    let mut queue = VecDeque::new();
    
    // Start from the first basic block
    let start_bb = rustc_middle::mir::BasicBlock::ZERO;
    queue.push_back(start_bb);
    
    while let Some(bb) = queue.pop_front() {
        if bb_visited.contains(&bb) {
            continue;
        }
        bb_visited.insert(bb);
        
        // Get the basic block data
        let bb_data = &mir.basic_blocks[bb];
        
        // Check the terminator of this basic block
        if let Some(ref terminator) = bb_data.terminator {
            match &terminator.kind {
                // Direct unwind resume - return true
                TerminatorKind::UnwindResume => {
                    return true;
                }
                
                // Function call - check if it may unwind
                TerminatorKind::Call { target, unwind, .. } => {
                    // Add the normal successor to the queue if it exists
                    if let Some(target_bb) = target {
                        queue.push_back(*target_bb);
                    }

                    let call_location = rustc_middle::mir::Location { 
                        block: bb, 
                        statement_index: bb_data.statements.len() 
                    };
                    let callsite = Unit::new(func_def, call_location);
                    let mut call_may_unwind = false;
                    if let Some(call_graph) = &acx.call_graph {
                        let callees: Vec<crate::mir::function::FuncDef<'tcx>> = call_graph.get_callees(&callsite);           
                        if callees.is_empty() {
                            // If we can't determine callees, conservatively assume it may unwind
                            call_may_unwind = true;
                        }
                        
                        // Check if any callee may unwind resume
                        for callee in callees {
                            if may_unwind_resume_impl(acx, callee, visited) {
                                call_may_unwind = true;
                                break;
                            }
                        }
                    } else {
                        call_may_unwind = true;
                    };
                    
                    // Check unwind action
                    match unwind {
                        rustc_middle::mir::UnwindAction::Continue => {
                            // This means the call may unwind and continue unwinding
                            // If target is None, this call never returns normally and 
                            // always unwinds, so it definitely may unwind resume
                            if target.is_none() || call_may_unwind {
                                return true;
                            }
                        }
                        rustc_middle::mir::UnwindAction::Cleanup(unwind_bb) => {
                            // Add the unwind basic block to the queue
                            if call_may_unwind {
                                queue.push_back(*unwind_bb);
                            }
                        }
                        rustc_middle::mir::UnwindAction::Terminate(_)
                        | rustc_middle::mir::UnwindAction::Unreachable => {
                        }
                    }
                }
                
                // Drop statement - similar to call
                TerminatorKind::Drop { target, unwind, .. } => {
                    queue.push_back(*target);
                    
                    match unwind {
                        rustc_middle::mir::UnwindAction::Continue => {
                            // Drop may unwind resume
                            // For now, we conservatively assume that drop may unwind resume
                            return true;
                        }
                        rustc_middle::mir::UnwindAction::Cleanup(unwind_bb) => {
                            queue.push_back(*unwind_bb);
                        }
                        rustc_middle::mir::UnwindAction::Terminate(_)
                        | rustc_middle::mir::UnwindAction::Unreachable => {
                        }
                    }
                }
                
                // Assert statement
                TerminatorKind::Assert { target, unwind, .. } => {
                    queue.push_back(*target);
                    
                    match unwind {
                        rustc_middle::mir::UnwindAction::Continue => {
                            return true;
                        }
                        rustc_middle::mir::UnwindAction::Cleanup(unwind_bb) => {
                            queue.push_back(*unwind_bb);
                        }
                        rustc_middle::mir::UnwindAction::Terminate(_)
                        | rustc_middle::mir::UnwindAction::Unreachable => {
                        }
                    }
                }
                
                // Other terminators that don't unwind but have successors
                TerminatorKind::Goto { target } => {
                    queue.push_back(*target);
                }
                
                TerminatorKind::SwitchInt { targets, .. } => {
                    for target in targets.all_targets() {
                        queue.push_back(*target);
                    }
                }
                
                TerminatorKind::FalseEdge { real_target, imaginary_target } => {
                    queue.push_back(*real_target);
                    queue.push_back(*imaginary_target);
                }
                
                TerminatorKind::FalseUnwind { real_target, unwind } => {
                    queue.push_back(*real_target);
                    if let rustc_middle::mir::UnwindAction::Cleanup(unwind_bb) = unwind {
                        queue.push_back(*unwind_bb);
                    }
                }
                
                // Terminal nodes - no successors
                TerminatorKind::Return | 
                TerminatorKind::TailCall { .. } |
                TerminatorKind::CoroutineDrop |
                TerminatorKind::Unreachable |
                TerminatorKind::UnwindTerminate(_) => {
                    // These are terminal - no successors to add
                }
                
                TerminatorKind::Yield { resume, drop, .. } => {
                    queue.push_back(*resume);
                    if let Some(drop_bb) = drop {
                        queue.push_back(*drop_bb);
                    }
                }
                
                TerminatorKind::InlineAsm { .. } => {
                    // Conservatively assume inline assembly may unwind
                    // without analyzing the specific asm block
                    return true;
                }
            }
        }
    }
    
    // If we've traversed all reachable blocks and found no unwind resume
    false
}