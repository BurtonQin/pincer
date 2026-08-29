use log::*;
use std::collections::HashSet;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_path::AccessPath;
use crate::mir::unit::Unit;
use crate::infoflow::{dealloc_arg, is_dealloc, is_realloc};
use crate::mir::function::FuncDef;
use crate::mir::known_names::KnownNames;
use crate::tsa::abstract_value::ConstantValue;
use crate::tsa::analyses::memory_safety_analysis::null_state::{ErrorKind, NullState};
use crate::tsa::state::{ConstantKind, ExecutionState, SymbState, SymbStateSupport};
use crate::tsa::state_transition::TypeStateTransition;
use crate::util::type_util;
use colored::*;
use rustc_middle::mir::{self, Operand, Place};
use rustc_span::symbol::Symbol;
use rustc_abi::VariantIdx;
use smallvec::{smallvec, SmallVec};

#[derive(Copy, Clone)]
pub struct NullStateTransition<'analysis, 'tcx> {
    acx: &'analysis AnalysisContext<'tcx>,
}

impl<'analysis, 'tcx> NullStateTransition<'analysis, 'tcx> {
    pub fn new(acx: &'analysis AnalysisContext<'tcx>) -> Self {
        NullStateTransition { acx }
    }

    pub fn on_dealloc(
        &self,
        in_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
        callsite: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[SymbState<'tcx, NullState, AccessPath<'tcx>>; 1]> {
        let Some(dealloc_ptr) = dealloc_arg(&self.acx, callsite, callee) else {
            return smallvec![in_state.clone()];
        };
        let mut new_type_state = in_state.type_state;
        let new_aliases = in_state.aliases().clone();
        match dealloc_ptr {
            Operand::Copy(ptr) | Operand::Move(ptr) => {
                for alias in in_state.aliases() {
                    if alias.is_projection_of(self.acx, &ptr) {
                        if !alias.is_indirect() {
                            // The tracked pointer is freed. We need to set the type
                            // state to Null. If the type state is Null already, we
                            // discover a potential double free issue.
                            if in_state.type_state.is_null() {
                                // TODO: Handle double free issue
                                new_type_state = NullState::Error(ErrorKind::DoubleFree);
                                println!("{}", "Double Free detected".red());
                            } else {
                                new_type_state = NullState::Null;
                            }
                            break;
                        }
                    }
                }
            }
            _ => {}
        }

        smallvec![SymbState::new_symb_state(
            new_type_state,
            ExecutionState::new_exec_state(
                new_aliases,
                in_state.execution_state.constants().clone()
            ),
        )]
    }

    pub fn on_realloc(
        &self,
        in_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
        callsite: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[SymbState<'tcx, NullState, AccessPath<'tcx>>; 1]> {
        let known_name = self.acx.get_known_name_for(callee.def_id);
        let args = callsite.call_args(self.acx.tcx);
        let call_dest = callsite.call_destination(self.acx.tcx);
        let (ptr_dest, ptr_arg) = match known_name {
            KnownNames::RustRealloc | KnownNames::StdAllocRealloc => (call_dest, &args[0]),
            KnownNames::StdAllocAllocatorGrow
            | KnownNames::StdAllocAllocatorGrowZeroed
            | KnownNames::StdAllocAllocatorShrink => (
                call_dest.project_deeper(
                    &[mir::PlaceElem::Downcast(
                        Some(Symbol::intern("Ok")),
                        VariantIdx::from_u32(0),
                    )],
                    self.acx.tcx,
                ),
                &args[1],
            ),
            _ => unreachable!(),
        };
        let mut new_type_state = in_state.type_state;
        let mut new_aliases = in_state.aliases().clone();
        match ptr_arg {
            Operand::Copy(ptr) | Operand::Move(ptr) => {
                for alias in in_state.aliases() {
                    if alias.is_projection_of(self.acx, ptr) {
                        if !alias.is_indirect() {
                            // The tracked pointer is freed. We need to set the type
                            // state to Null. If the type state is Null already, we
                            // discover a potential double free issue.
                            if in_state.type_state.is_null() {
                                // TODO: Handle double free issue
                                new_type_state = NullState::Error(ErrorKind::DoubleFree);
                                println!("{}", "Double Free detected".red());
                            } else {
                                new_type_state = NullState::Null;
                            }
                            break;
                        } else {
                            // In this case, we are tracking a pointer like `(*p).f`,
                            // where the memory that `p` points to is reallocated.
                            // Given `q = realloc(p)`, after the reallocation, `(*q).f`
                            // should have the same value as original `(*p).f`, and
                            // `(*p).f` is no longer valid.
                            let new_alias = alias.derive_with_new_base(self.acx, ptr, &ptr_dest);
                            new_aliases.remove(alias);
                            new_aliases.insert(new_alias);
                        }
                    }
                }
            }
            _ => {}
        }

        let mut constants = in_state.execution_state.constants().clone();
        if matches!(
            known_name,
            KnownNames::StdAllocAllocatorGrow
                | KnownNames::StdAllocAllocatorGrowZeroed
                | KnownNames::StdAllocAllocatorShrink
        ) {
            constants.insert(
                ConstantKind::EnumDiscriminant(call_dest),
                ConstantValue::Constant(0),
            );
        }
        smallvec![SymbState::new_symb_state(
            new_type_state,
            ExecutionState::new_exec_state(new_aliases, constants),
        )]
    }

    // `unsafe fn drop_in_place<T>(to_drop: *mut T)`
    // This function executes the destructor (if any) of the pointed-to value.
    // This is almost the same as calling `ptr::read`` and discarding the result
    //
    // `Vec<T>`'s drop function employs `drop_in_place` to deallocate the elements.
    pub fn on_drop_in_place(
        &self,
        in_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
        _callsite: Unit<'tcx>,
        _callee: FuncDef<'tcx>,
    ) -> SmallVec<[SymbState<'tcx, NullState, AccessPath<'tcx>>; 1]> {
        // TODO: handle drop_in_place
        smallvec![in_state.clone()]
    }
}

impl<'analysis, 'tcx> TypeStateTransition<'tcx, NullState, AccessPath<'tcx>>
    for NullStateTransition<'analysis, 'tcx>
{
    fn is_transition_function(&self, callee: FuncDef<'tcx>) -> bool {
        is_realloc(&self.acx, callee) || is_dealloc(&self.acx, callee)
    }

    fn on_transition_function_call(
        &self,
        in_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
        callsite: Unit<'tcx>,
        callee: FuncDef<'tcx>,
    ) -> SmallVec<[SymbState<'tcx, NullState, AccessPath<'tcx>>; 1]> {
        if is_dealloc(&self.acx, callee) {
            return self.on_dealloc(in_state, callsite, callee);
        }

        if is_realloc(&self.acx, callee) {
            return self.on_realloc(in_state, callsite, callee);
        }

        unreachable!()
    }

    fn on_unbalanced_return(
        &self,
        func: FuncDef<'tcx>,
        init_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
        out_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
    ) -> Option<SymbState<'tcx, NullState, AccessPath<'tcx>>> {
        if !self.acx.entry_funcs.contains(&func.def_id) {
            return None;
        }

        if init_state.type_state.is_null() || !out_state.type_state.is_null() {
            return None;
        }

        // If this function is a drop implmentation
        if type_util::is_drop_impl(self.acx.tcx, func.def_id) {
            return None;
        }

        if func.to_string().contains("free") || func.to_string().contains("drop") {
            return None;
        }

        let arg_count = if self.acx.tcx.is_mir_available(func.def_id) {
            self.acx.tcx.optimized_mir(func.def_id).arg_count
        } else {
            0
        };

        trace!("On unbalanced return: {:?}", out_state.aliases());

        let has_dangling_pointer =
            |init_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
             out_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>| {
                out_state.aliases().iter().any(|pointer| {
                    if pointer.local.index() == 0 {
                        true
                    } else {
                        if pointer.local.index() <= arg_count {
                            // Returns true in the following two cases:
                            // 1. the pointer is a path indirectly accessed from a parameter,
                            // 2. the pointer is not indirect, but the parameter is copyable. This
                            // can help detect the case where a raw pointer is passed to a function
                            // and deallocated inside the function.
                            let arg_type = type_util::place_ty(
                                self.acx.tcx,
                                &Place::from(pointer.local),
                                func,
                            );
                            (pointer.is_indirect() && arg_type.is_any_ptr())
                                || (init_state.aliases().contains(pointer)
                                    && arg_type.is_trivially_pure_clone_copy())
                        } else {
                            false
                        }
                    }
                })
            };

        if has_dangling_pointer(init_state, out_state) {
            let error_state = SymbState::new_symb_state(
                NullState::Error(ErrorKind::DanglingPointer),
                ExecutionState::init_exec_state(out_state.aliases().clone()),
            );
            println!("{}", "Dangling pointer detected".red());
            return Some(error_state);
        }

        None
    }

    /// Report a use-after-free error if a null pointer is passed to a function without available mir.
    fn on_mir_unavailable_callee(
        &self,
        in_state: &SymbState<'tcx, NullState, AccessPath<'tcx>>,
        _callee: Option<FuncDef<'tcx>>,
        arg_aliases: &HashSet<&AccessPath<'tcx>>,
    ) -> Option<SymbState<'tcx, NullState, AccessPath<'tcx>>> {
        if in_state.type_state.is_null() {
            if !arg_aliases.is_empty() {
                let error_state = SymbState::new_symb_state(
                    NullState::Error(ErrorKind::UseAfterFree),
                    ExecutionState::init_exec_state(in_state.aliases().clone()),
                );
                println!("{}", "Use-After-Free detected".red());
                return Some(error_state);
            }
        }
        None
    }

    fn on_pointer_dereference(
        &self,
        state: &mut SymbState<'tcx, NullState, AccessPath<'tcx>>,
        deref_ptr: &Place<'tcx>,
    ) {
        if state.type_state.is_non_null() {
            return;
        } else if state.type_state.is_null() {
            if !state.aliases().is_empty() {
                let func = state.aliases().iter().next().unwrap().func_def;
                let deref_path = AccessPath::from_rustc_place(self.acx, func, deref_ptr);
                if state.aliases().contains(&deref_path) {
                    // A Null pointer dereference or Use-After-Free issue is detected.
                    state
                        .borrow_mut()
                        .set_type_state(NullState::Error(ErrorKind::UseAfterFree));
                    println!("{}", "Use-After-Free detected".red());
                }
            }
        }
    }
}
