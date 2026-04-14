// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use std::collections::HashSet;

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{self, Body, Location};
use rustc_middle::ty::{TyCtxt, TyKind};

use crate::infoflow::CallGraph;
use crate::util;

#[derive(Debug, Copy, Clone, Eq, Hash, PartialEq)]
pub enum RawPtrSourceKind {
    RefToRawPtrCast,
    AddressToRawPtrCast,
    LibraryCall,
}

#[derive(Debug, Clone, Eq, Hash, PartialEq)]
pub struct RawPtrSource<'tcx> {
    /// Container function of the raw pointer source.
    pub func_def: DefId,
    /// Location of the source.
    pub location: Location,
    /// What kind of the source is.
    pub kind: RawPtrSourceKind,
    /// The raw pointer that is initiated.
    pub raw_ptr: mir::Place<'tcx>,
}


pub struct GatherRawPtrSources<'tcx> {
    pub tcx: TyCtxt<'tcx>,
    pub raw_ptr_sources: HashSet<RawPtrSource<'tcx>>,
}

impl<'tcx> GatherRawPtrSources<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>) -> Self {
        Self {
            tcx,
            raw_ptr_sources: HashSet::new(),
        }
    }

    pub fn visit_local_funcs(&mut self, call_graph: &CallGraph<'tcx>) {
        let mut visited = HashSet::new();
        for func in call_graph.reachable_funcs_iter() {
            let func_def = func.def_id;
            if func_def.is_local() && visited.insert(func_def) {
                if self.tcx.is_mir_available(func_def) {
                    let body = self.tcx.optimized_mir(func_def);
                    self.visit_body(func_def, body);
                }
            }
        }
    }

    pub fn visit_reachable_funcs(&mut self, call_graph: &CallGraph<'tcx>) {
        let mut visited = HashSet::new();
        for func in call_graph.reachable_funcs_iter() {
            let func_def = func.def_id;
            if visited.insert(func_def) {
                if util::is_std_lib_func(self.tcx, func_def) {
                    continue;
                }
                if self.tcx.is_mir_available(func_def) {
                    let body = self.tcx.optimized_mir(func_def);
                    self.visit_body(func_def, body);
                }
            }
        }
    }

    pub fn visit_body(&mut self, def_id: DefId, body: &Body<'tcx>) {
        for bb in body.basic_blocks.indices() {
            self.visit_basic_block(def_id, body, bb);
        }
    }

    pub fn visit_basic_block(&mut self, def_id: DefId, body: &Body<'tcx>, bb: mir::BasicBlock) {
        let mir::BasicBlockData {
            ref statements,
            ref terminator,
            ..
        } = &body[bb];
        let mut location = bb.start_location();
        let terminator_index = statements.len();

        while location.statement_index < terminator_index {
            self.visit_statement(def_id, location, body, &statements[location.statement_index]);
            location.statement_index += 1;
        }

        if let Some(mir::Terminator {
            ref source_info,
            ref kind,
        }) = *terminator
        {
            self.visit_terminator(def_id, location, body, kind, *source_info);
        }
    }

    pub fn visit_statement(
        &mut self, 
        def_id: DefId, 
        location: Location, 
        body: &Body<'tcx>,
        statement: &mir::Statement<'tcx>
    ) {
        let mir::Statement {kind, source_info: _} = statement;
        match kind {
            mir::StatementKind::Assign(box (assigned_place, rvalue)) => {
                match rvalue {
                    // Creates a raw pointer with the indicated mutability to the place.
                    // Replaced with Rvalue::RawPtr in the newer version of rustc
                    mir::Rvalue::RawPtr(_mutability, _place) => {
                        self.raw_ptr_sources.insert(
                            RawPtrSource {
                                func_def: def_id, 
                                location, 
                                kind: RawPtrSourceKind::RefToRawPtrCast,
                                raw_ptr: *assigned_place
                            }
                        );
                    }
                    mir::Rvalue::Cast(mir::CastKind::Transmute, operand, ty) => {
                        if ty.is_unsafe_ptr() {
                            let operand_ty = operand.ty(&body.local_decls, self.tcx);
                            if operand_ty.is_ref() {
                                self.raw_ptr_sources.insert(
                                    RawPtrSource {
                                        func_def: def_id, 
                                        location, 
                                        kind: RawPtrSourceKind::RefToRawPtrCast,
                                        raw_ptr: *assigned_place
                                    }
                                );
                            } else if !operand_ty.is_any_ptr() {
                                self.raw_ptr_sources.insert(
                                    RawPtrSource {
                                        func_def: def_id, 
                                        location, 
                                        kind: RawPtrSourceKind::AddressToRawPtrCast,
                                        raw_ptr: *assigned_place
                                    }
                                );
                            }
                        }
                    }
                    // An address-to-pointer cast that picks up an exposed provenance.
                    mir::Rvalue::Cast(
                        mir::CastKind::PointerWithExposedProvenance, 
                        _operand, 
                        ty
                    ) => {
                        assert!(ty.is_unsafe_ptr());
                        self.raw_ptr_sources.insert(
                            RawPtrSource {
                                func_def: def_id, 
                                location, 
                                kind: RawPtrSourceKind::AddressToRawPtrCast,
                                raw_ptr: *assigned_place
                            }
                        );
                    }
                    _ => {}
                }
            }
            _ => (),
        }
    }

    pub fn visit_terminator(
        &mut self, 
        def_id: DefId, 
        location: Location, 
        body: &Body<'tcx>,
        kind: &mir::TerminatorKind<'tcx>,
        _source_info: mir::SourceInfo,
    ) {
        match kind {
            mir::TerminatorKind::Call {
                func,
                args: _,
                destination,
                target: _,
                unwind: _,
                call_source: _,
                fn_span: _,
            } => {
                // Detecting library functions calls that return raw pointers.
                let dest_ty = destination.ty(body, self.tcx).ty;
                if dest_ty.is_unsafe_ptr() {
                    if let mir::Operand::Constant(box constant) = func {
                        match constant.ty().kind() {
                            TyKind::FnDef(callee_def_id, ..) => {
                                if !callee_def_id.is_local() {
                                    // Ignore calls to `exchange_malloc`.
                                    if is_exchange_malloc(self.tcx, *callee_def_id) {
                                        return;
                                    }
                                    self.raw_ptr_sources.insert(
                                        RawPtrSource {
                                            func_def: def_id, 
                                            location, 
                                            kind: RawPtrSourceKind::LibraryCall,
                                            raw_ptr: *destination
                                        }
                                    );
                                }
                            }
                            _ => {}
                        }
                    }
                }
            }
            _ => {}
        }
    }
}

pub fn is_exchange_malloc<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let path_str = tcx.def_path_str(def_id);
    path_str == "alloc::alloc::exchange_malloc"
}