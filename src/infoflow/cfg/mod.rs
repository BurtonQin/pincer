use rustc_middle::mir;

use crate::mir::function::FuncDef;

pub mod backward_infoflow_cfg;
pub mod block_cfg;
pub mod cfg_factory;
pub mod infoflow_cfg;
pub mod interprocedural_cfg;

/// Determines the structure of a CFG instance.
/// Used as the cache key in `CfgFactory`: the same config always yields the same reference.
/// Whether a dummy head node is inserted is encoded in the constructor choice
/// (`InfoflowCFG::new` vs `InfoflowCFG::new_with_dummy_head`) rather than in this config.
#[derive(Hash, Eq, PartialEq, Clone, Debug, Default)]
pub struct CFGConfig {
    /// Insert a synthetic `UnwindResume` tail reachable from `Call`/`Drop`/`Assert`
    /// terminators with `UnwindAction::Continue`.
    pub dummy_resume: bool,
    /// Model `Drop` terminators as interprocedural call nodes (entering the drop shim body).
    /// Currently reserved — has no behavioral effect until `UnitGraph` implements it.
    pub model_drop_calls: bool,
}

/// Trait for CFG-specific queries needed by flow functions.
/// Abstracts over block-level (BBCFGNode) and statement-level (Unit) granularity.
pub trait CFGQueries<'tcx, N> {
    fn is_conditional_branch_from(&self, node: N) -> bool;
    fn get_switch_int(&self, node: N) -> Option<SwitchInt<'tcx>>;
    fn is_switch_discr(&self, func: FuncDef<'tcx>, place: &mir::Place<'tcx>) -> bool;
    fn is_unwind_branch(&self, from: N, to: N) -> bool;
    fn is_dummy_resume(&self, n: N) -> bool;
    fn get_tail_kind(&self, n: N) -> TailKind;
}

#[derive(Debug, Clone)]
pub struct SwitchInt<'tcx> {
    pub discr: mir::Operand<'tcx>,
    pub targets: mir::SwitchTargets,
}

impl<'tcx> SwitchInt<'tcx> {
    pub fn new(discr: mir::Operand<'tcx>, targets: mir::SwitchTargets) -> Self {
        SwitchInt { discr, targets }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TailKind {
    /// Returns from the function.
    Return,
    /// Indicates a terminator that can never be reached.
    Unreachable,
    /// Indicates that the landing pad is finished and that the process should continue unwinding.
    /// Including TerminatorKind::UnwindResume and UnwindAction::Continue.
    UnwindResume,
    /// Indicates that the landing pad is finished and that the process should terminate.
    /// Including TerminatorKind::UnwindTerminate and UnwindAction::Terminate.
    UnwindTerminate,
}

pub fn tail_kind(terminator_kind: &mir::TerminatorKind) -> Option<TailKind> {
    match terminator_kind {
        mir::TerminatorKind::Return 
        | mir::TerminatorKind::TailCall { .. } 
        | mir::TerminatorKind::CoroutineDrop => {
            Some(TailKind::Return)
        }
        mir::TerminatorKind::UnwindResume => Some(TailKind::UnwindResume),
        mir::TerminatorKind::UnwindTerminate(..) => Some(TailKind::UnwindTerminate),
        mir::TerminatorKind::Unreachable => Some(TailKind::Unreachable),
        mir::TerminatorKind::Call { target, unwind, .. } => {
            if target.is_some() {
                None
            } else {
                match unwind {
                    mir::UnwindAction::Continue => Some(TailKind::UnwindResume),
                    mir::UnwindAction::Unreachable => Some(TailKind::Unreachable),
                    mir::UnwindAction::Terminate(..) => Some(TailKind::UnwindTerminate),
                    _ => {
                        None
                    }
                }
            }
        }
        _ => None,
    }
}
