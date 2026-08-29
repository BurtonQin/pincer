use lazy_static::lazy_static;
use serde::Deserialize;
use std::collections::HashSet;
use std::sync::Mutex;

use rustc_middle::mir::{BasicBlock, Local, Location, Operand, Place, Terminator, TerminatorKind};
use rustc_middle::ty::TyKind;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_path::AccessPath;
use crate::mir::builtins::BuiltinPattern;
use crate::mir::function::FuncDef;
use crate::mir::unit::Unit;

// ---------------------------------------------------------------------------
// YAML deserialization types (private to this module)
// ---------------------------------------------------------------------------

#[derive(Debug, Clone, Deserialize)]
#[serde(tag = "kind", rename_all = "snake_case")]
enum RawVulnerablePointerPattern {
    Parameter {
        #[serde(flatten)]
        base: BuiltinPattern,
        param_index: usize,
    },
    CallArgument {
        #[serde(flatten)]
        base: BuiltinPattern,
        arg_index: usize,
    },
    CallDestination {
        #[serde(flatten)]
        base: BuiltinPattern,
    },
}

#[derive(Debug, Deserialize)]
struct RawVulnerablePointersConfig {
    #[serde(default)]
    patterns: Vec<RawVulnerablePointerPattern>,
}

// ---------------------------------------------------------------------------
// Public pattern type
// ---------------------------------------------------------------------------

/// Pattern for identifying vulnerable pointers
#[derive(Debug, Clone)]
pub enum VulnerablePointerPattern {
    Parameter {
        base: BuiltinPattern,
        param_index: usize,
    },
    CallArgument {
        base: BuiltinPattern,
        arg_index: usize,
    },
    CallDestination {
        base: BuiltinPattern,
    },
}

impl From<RawVulnerablePointerPattern> for VulnerablePointerPattern {
    fn from(raw: RawVulnerablePointerPattern) -> Self {
        match raw {
            RawVulnerablePointerPattern::Parameter { base, param_index } => {
                VulnerablePointerPattern::Parameter { base, param_index }
            }
            RawVulnerablePointerPattern::CallArgument { base, arg_index } => {
                VulnerablePointerPattern::CallArgument { base, arg_index }
            }
            RawVulnerablePointerPattern::CallDestination { base } => {
                VulnerablePointerPattern::CallDestination { base }
            }
        }
    }
}

#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct VulnerablePointer<'tcx> {
    pub ptr_path: AccessPath<'tcx>,
    pub unit: Unit<'tcx>,
}

lazy_static! {
    /// Global list of vulnerable pointer patterns loaded from config/vuln_ptrs.yaml.
    /// Users can add custom patterns at runtime via `add_vulnerable_pointer_pattern`.
    static ref VULNERABLE_POINTER_PATTERNS: Mutex<Vec<VulnerablePointerPattern>> = {
        const DEFAULT_YAML: &str = include_str!("../../../../config/vuln_ptrs.yaml");
        let mut raw: RawVulnerablePointersConfig =
            serde_yaml::from_str(DEFAULT_YAML)
                .expect("embedded vuln_ptrs.yaml is invalid");
        for p in &mut raw.patterns {
            match p {
                RawVulnerablePointerPattern::Parameter { base, .. }
                | RawVulnerablePointerPattern::CallArgument { base, .. }
                | RawVulnerablePointerPattern::CallDestination { base } => base.compile_regex(),
            }
        }
        let patterns = raw.patterns.into_iter().map(Into::into).collect();
        Mutex::new(patterns)
    };
}

/// Add a new vulnerable pointer pattern at runtime
pub fn add_vulnerable_pointer_pattern(pattern: VulnerablePointerPattern) {
    let mut patterns = VULNERABLE_POINTER_PATTERNS.lock().unwrap();
    patterns.push(pattern);
}

/// Collect vulnerable pointers based on the configured patterns
pub fn collect_vulnerable_pointers<'tcx>(
    acx: &AnalysisContext<'tcx>,
) -> HashSet<VulnerablePointer<'tcx>> {
    let mut vulnerable_pointers = HashSet::new();

    let call_graph = acx.get_call_graph();

    for func in call_graph.reachable_funcs_iter() {
        if !func.def_id.is_local() {
            continue;
        }
        visit_parameter(acx, func, &mut vulnerable_pointers);
        visit_body(acx, func, &mut vulnerable_pointers);
    }

    vulnerable_pointers
}

/// Collect vulnerable pointers from function parameters
fn visit_parameter<'tcx>(
    acx: &AnalysisContext<'tcx>,
    func: FuncDef<'tcx>,
    vulnerable_pointers: &mut HashSet<VulnerablePointer<'tcx>>,
) {
    if !acx.tcx.is_mir_available(func.def_id) {
        return;
    }

    let mir = acx.tcx.optimized_mir(func.def_id);
    let patterns = VULNERABLE_POINTER_PATTERNS.lock().unwrap();
    for pattern in patterns.iter() {
        if let VulnerablePointerPattern::Parameter { base, param_index } = pattern {
            if base.matches(acx.tcx, func.def_id) {
                if *param_index > mir.arg_count {
                    break;
                }
                let param_ty = mir.local_decls[Local::from_usize(*param_index)].ty;
                if param_ty.is_any_ptr() {
                    vulnerable_pointers.insert(VulnerablePointer {
                        ptr_path: AccessPath::from_rustc_place(
                            acx,
                            func,
                            &Place::from(Local::from_usize(*param_index)),
                        ),
                        unit: Unit::new(func, BasicBlock::from_usize(0).start_location()),
                    });
                }
            }
        }
    }
}

/// Collect vulnerable pointers from function call arguments and return values
fn visit_body<'tcx>(
    acx: &AnalysisContext<'tcx>,
    func: FuncDef<'tcx>,
    vulnerable_pointers: &mut HashSet<VulnerablePointer<'tcx>>,
) {
    if !acx.tcx.is_mir_available(func.def_id) {
        return;
    }

    let mir = acx.tcx.optimized_mir(func.def_id);

    for (bb_index, bb_data) in mir.basic_blocks.iter_enumerated() {
        if let Some(terminator) = &bb_data.terminator {
            let location = Location {
                block: bb_index,
                statement_index: bb_data.statements.len(),
            };
            visit_terminator(acx, func, location, terminator, mir, vulnerable_pointers);
        }
    }
}

fn visit_terminator<'tcx>(
    acx: &AnalysisContext<'tcx>,
    func: FuncDef<'tcx>,
    location: Location,
    terminator: &Terminator<'tcx>,
    mir: &rustc_middle::mir::Body<'tcx>,
    vulnerable_pointers: &mut HashSet<VulnerablePointer<'tcx>>,
) {
    if let TerminatorKind::Call {
        args, destination, ..
    } = &terminator.kind
    {
        let call_unit = Unit::new(func, location);

        let callees: Vec<FuncDef<'tcx>> = acx.get_call_graph().get_callees(&call_unit);
        for callee in callees {
            let patterns = VULNERABLE_POINTER_PATTERNS.lock().unwrap();
            for pattern in patterns.iter() {
                match pattern {
                    VulnerablePointerPattern::CallArgument { base, arg_index } => {
                        if base.matches(acx.tcx, callee.def_id) {
                            if args.len() > *arg_index {
                                if let Operand::Copy(arg_place) | Operand::Move(arg_place) =
                                    args[*arg_index].node
                                {
                                    let arg_ty = arg_place.ty(&mir.local_decls, acx.tcx).ty;
                                    if arg_ty.is_any_ptr() {
                                        vulnerable_pointers.insert(VulnerablePointer {
                                            ptr_path: AccessPath::from_rustc_place(
                                                acx, func, &arg_place,
                                            ),
                                            unit: call_unit,
                                        });
                                    }
                                }
                            }
                        }
                    }
                    VulnerablePointerPattern::CallDestination { base } => {
                        if base.matches(acx.tcx, callee.def_id) {
                            let dst_ty = destination.ty(&mir.local_decls, acx.tcx).ty;
                            let is_vulnerable = if dst_ty.is_any_ptr() {
                                true
                            } else if let TyKind::Tuple(tys) = dst_ty.kind() {
                                tys.get(0).map(|ty| ty.is_any_ptr()).unwrap_or(false)
                            } else {
                                false
                            };
                            if is_vulnerable {
                                if let Some(target_unit) = call_unit.call_succ_unit(acx.tcx) {
                                    vulnerable_pointers.insert(VulnerablePointer {
                                        ptr_path: AccessPath::from_rustc_place(
                                            acx,
                                            func,
                                            destination,
                                        ),
                                        unit: target_unit,
                                    });
                                }
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
    }
}
