// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use lazy_static::lazy_static;
use regex::Regex;
use rustc_middle::mir::{self, Operand, Place};
use rustc_middle::ty::TyCtxt;
use rustc_span::symbol::Symbol;
use rustc_target::abi::VariantIdx;
use serde::Deserialize;

use crate::analysis_context::AnalysisContext;
use crate::mir::function::FuncDef;
use crate::mir::known_names::KnownNames;
use crate::mir::unit::Unit;

// ---------------------------------------------------------------------------
// Config types for user-declared builtin functions
// ---------------------------------------------------------------------------

fn default_match_kind() -> MatchKind {
    MatchKind::Exact
}

#[derive(Debug, Clone, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum MatchKind {
    Exact,
    Suffix,
    Contains,
    Regex,
}

#[derive(Debug, Clone, Deserialize)]
pub struct BuiltinPattern {
    pub pattern: String,
    #[serde(default = "default_match_kind")]
    pub match_kind: MatchKind,
    #[serde(skip)]
    compiled_regex: Option<Regex>,
}

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "lowercase")]
pub enum FunctionEffect {
    Alloc,
    Dealloc {
        #[serde(default)]
        arg: usize,
    },
    Realloc {
        #[serde(default)]
        arg: usize,
    },
    Copy {
        from_arg: usize,
    },
    Move {
        from_arg: usize,
    },
    Load {
        from_arg: usize,
    },
    Store {
        to_arg: usize,
        #[serde(default)]
        from_arg: Option<usize>,
    },
}

#[derive(Debug, Clone, Deserialize)]
pub struct FunctionEffectEntry {
    #[serde(flatten)]
    pub base: BuiltinPattern,
    pub effects: Vec<FunctionEffect>,
}

#[derive(Debug, Clone, Deserialize)]
struct RawBuiltinsConfig {
    #[serde(default)]
    functions: Vec<FunctionEffectEntry>,
}

/// Pre-partitioned builtin function config for efficient lookup.
#[derive(Debug)]
pub struct BuiltinsConfig {
    /// Entries whose effects contain `Alloc`.
    alloc: Vec<FunctionEffectEntry>,
    /// Entries whose effects contain `Dealloc`.
    dealloc: Vec<FunctionEffectEntry>,
    /// Entries whose effects contain `Realloc`.
    realloc: Vec<FunctionEffectEntry>,
    /// All entries (for general `function_effects` lookup).
    functions: Vec<FunctionEffectEntry>,
}

impl BuiltinPattern {
    pub(crate) fn compile_regex(&mut self) {
        if matches!(self.match_kind, MatchKind::Regex) {
            self.compiled_regex = Some(
                Regex::new(&self.pattern)
                    .unwrap_or_else(|e| panic!("Invalid regex pattern '{}': {}", self.pattern, e)),
            );
        }
    }
}

lazy_static! {
    static ref BUILTINS_CONFIG: BuiltinsConfig = {
        const DEFAULT_BUILTINS_YAML: &str = include_str!("../../config/builtins.yaml");
        let mut raw: RawBuiltinsConfig = serde_yaml::from_str(DEFAULT_BUILTINS_YAML)
            .expect("embedded default builtins.yaml is invalid");
        for entry in &mut raw.functions {
            entry.base.compile_regex();
        }

        let has = |entry: &FunctionEffectEntry, f: fn(&FunctionEffect) -> bool| {
            entry.effects.iter().any(f)
        };
        let alloc = raw.functions.iter()
            .filter(|e| has(e, |f| matches!(f, FunctionEffect::Alloc)))
            .cloned().collect();
        let dealloc = raw.functions.iter()
            .filter(|e| has(e, |f| matches!(f, FunctionEffect::Dealloc { .. })))
            .cloned().collect();
        let realloc = raw.functions.iter()
            .filter(|e| has(e, |f| matches!(f, FunctionEffect::Realloc { .. })))
            .cloned().collect();

        BuiltinsConfig { alloc, dealloc, realloc, functions: raw.functions }
    };
}

impl BuiltinPattern {
    /// Check if a function's `def_path_str` matches this pattern.
    pub fn matches(&self, tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> bool {
        let path_str = tcx.def_path_str(def_id);
        match self.match_kind {
            MatchKind::Exact => path_str == self.pattern,
            MatchKind::Suffix => path_str.ends_with(&self.pattern),
            MatchKind::Contains => path_str.contains(&self.pattern),
            MatchKind::Regex => self.compiled_regex.as_ref().unwrap().is_match(&path_str),
        }
    }
}

/// Look up configured function effects for a given function.
pub fn function_effects(tcx: TyCtxt<'_>, def_id: rustc_hir::def_id::DefId) -> Option<&'static [FunctionEffect]> {
    for entry in &BUILTINS_CONFIG.functions {
        if entry.base.matches(tcx, def_id) {
            return Some(&entry.effects);
        }
    }
    None
}

pub fn is_alloc<'tcx>(acx: &AnalysisContext<'tcx>, func: FuncDef<'tcx>) -> bool {
    let known_name = acx.get_known_name_for(func.def_id);
    match known_name {
        KnownNames::RustAlloc
        | KnownNames::RustAllocZeroed
        | KnownNames::StdAllocAlloc
        | KnownNames::StdAllocAllocZeroed
        | KnownNames::StdAllocExchangeMalloc
        | KnownNames::StdAllocAllocatorAllocate
        | KnownNames::StdAllocAllocatorAllocateZeroed => return true,
        _ => {}
    }

    // Check config-driven alloc patterns
    BUILTINS_CONFIG.alloc.iter().any(|e| e.base.matches(acx.tcx, func.def_id))
}

pub fn is_realloc<'tcx>(acx: &AnalysisContext<'tcx>, func: FuncDef<'tcx>) -> bool {
    let known_name = acx.get_known_name_for(func.def_id);
    match known_name {
        KnownNames::RustRealloc
        | KnownNames::StdAllocRealloc
        | KnownNames::StdAllocAllocatorGrow
        | KnownNames::StdAllocAllocatorGrowZeroed
        | KnownNames::StdAllocAllocatorShrink => return true,
        _ => {}
    }

    // Check config-driven realloc patterns
    BUILTINS_CONFIG.realloc.iter().any(|e| e.base.matches(acx.tcx, func.def_id))
}

pub fn is_dealloc<'tcx>(acx: &AnalysisContext<'tcx>, func: FuncDef<'tcx>) -> bool {
    let known_name = acx.get_known_name_for(func.def_id);
    match known_name {
        KnownNames::RustDealloc
        | KnownNames::StdAllocDealloc
        | KnownNames::StdAllocBoxFree
        | KnownNames::StdAllocAllocatorDeallocate => return true,
        _ => {}
    }

    // Check config-driven dealloc patterns
    BUILTINS_CONFIG.dealloc.iter().any(|e| e.base.matches(acx.tcx, func.def_id))
}

pub fn is_intrinsics_copy<'tcx>(acx: &AnalysisContext<'tcx>, func: FuncDef<'tcx>) -> bool {
    let known_name = acx.get_known_name_for(func.def_id);
    matches!(
        known_name,
        KnownNames::StdIntrinsicsCopy | KnownNames::StdIntrinsicsCopyNonOverlapping
    )
}

pub fn dealloc_arg<'tcx>(
    acx: &AnalysisContext<'tcx>,
    dealloc_site: Unit<'tcx>,
    dealloc_func: FuncDef<'tcx>,
) -> Option<Operand<'tcx>> {
    let known_name = acx.get_known_name_for(dealloc_func.def_id);
    // The dealloc function cannot be called in a drop body, therefore we
    // do not need to worry about if the function's mir is unavailable.
    let args = dealloc_site.call_args(acx.tcx);
    // KnownNames::RustDealloc: fn __rust_dealloc(ptr: *mut u8, size: usize, align: usize);
    // | KnownNames::StdAllocDealloc: fn dealloc(ptr: *mut u8, layout: Layout)
    // | KnownNames::StdAllocBoxFree: fn box_free(ptr: Unique<T>, alloc: A)
    // | KnownNames::StdAllocAllocatorDeallocate: fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
    match known_name {
        KnownNames::RustDealloc | KnownNames::StdAllocDealloc | KnownNames::StdAllocBoxFree => {
            return Some(args[0].clone());
        }
        KnownNames::StdAllocAllocatorDeallocate => {
            return Some(args[1].clone());
        }
        _ => {}
    };

    // Check config-driven dealloc patterns for ptr_arg
    for entry in &BUILTINS_CONFIG.dealloc {
        if entry.base.matches(acx.tcx, dealloc_func.def_id) {
            for effect in &entry.effects {
                if let FunctionEffect::Dealloc { arg } = effect {
                    return Some(args[*arg].clone());
                }
            }
        }
    }

    None
}

/// Returns `(result_place, ptr_operand)` for a realloc call: the place where the
/// new allocation is written and the operand of the pointer being reallocated.
pub fn realloc_arg_and_dst<'tcx>(
    acx: &AnalysisContext<'tcx>,
    realloc_site: Unit<'tcx>,
    realloc_func: FuncDef<'tcx>,
) -> Option<(Place<'tcx>, Operand<'tcx>)> {
    let known_name = acx.get_known_name_for(realloc_func.def_id);
    let call_dest = realloc_site.call_destination(acx.tcx);
    let args = realloc_site.call_args(acx.tcx);
    match known_name {
        KnownNames::RustRealloc | KnownNames::StdAllocRealloc => {
            return Some((call_dest, args[0].clone()));
        }
        KnownNames::StdAllocAllocatorGrow
        | KnownNames::StdAllocAllocatorGrowZeroed
        | KnownNames::StdAllocAllocatorShrink => {
            let result_place = call_dest.project_deeper(
                &[mir::PlaceElem::Downcast(
                    Some(Symbol::intern("Ok")),
                    VariantIdx::from_u32(0),
                )],
                acx.tcx,
            );
            return Some((result_place, args[1].clone()));
        }
        _ => {}
    };

    // Check config-driven realloc patterns
    for entry in &BUILTINS_CONFIG.realloc {
        if entry.base.matches(acx.tcx, realloc_func.def_id) {
            for effect in &entry.effects {
                if let FunctionEffect::Realloc { arg } = effect {
                    return Some((call_dest, args[*arg].clone()));
                }
            }
        }
    }

    None
}
