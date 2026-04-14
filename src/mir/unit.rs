// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use rustc_middle::mir::{Body, Location, Operand, Place, StatementKind, TerminatorKind};
use rustc_middle::ty::TyCtxt;

use crate::infoflow::cfg::infoflow_cfg::{DUMMY_HEAD_LOCATION, DUMMY_RESUME_LOCATION};
use crate::mir::drop_shim;
use crate::mir::function::FuncDef;
use crate::util;

/// A unit represents a specific location in a rust program.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub struct BaseUnit<F> {
    pub func: F,
    pub location: Location,
}

impl<F: std::fmt::Debug> std::fmt::Debug for BaseUnit<F> {
    default fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}@{:?}", self.func, self.location)
    }
}

impl<F: std::cmp::PartialEq> BaseUnit<F> {
    pub fn new(func: F, location: Location) -> Self {
        BaseUnit { func, location }
    }

    /// Returns `true` if `self` is reachable from `other` from the same function.
    pub fn is_reachable_from<'tcx>(&self, other: &BaseUnit<F>, body: &Body<'tcx>) -> bool {
        other.is_predecessor_of(self, body)
    }

    /// Returns `true` if `other` is earlier in the control flow graph thant `self`.
    pub fn is_predecessor_of<'tcx>(&self, other: &BaseUnit<F>, body: &Body<'tcx>) -> bool {
        if self.func != other.func {
            return false;
        }
        if self.location == DUMMY_HEAD_LOCATION || other.location == DUMMY_RESUME_LOCATION {
            return true;
        }
        self.location.is_predecessor_of(other.location, body)
    }
}

pub trait ContainingFunction<F> {
    fn containing_function(self) -> F;
}

impl<F> ContainingFunction<F> for BaseUnit<F> {
    fn containing_function(self) -> F {
        self.func
    }
}

// --- Specialized impls for Unit<'tcx> = BaseUnit<FuncDef<'tcx>> ---

pub type Unit<'tcx> = BaseUnit<FuncDef<'tcx>>;

#[derive(Debug)]
pub enum StatementOrTerminator<'tcx> {
    Statement(&'tcx StatementKind<'tcx>),
    Terminator(&'tcx TerminatorKind<'tcx>),
}

// StatementKind::Nop is a zero-sized type (ZST), it can be safely treated as having any lifetime, including 'tcx.
pub fn nop_statement_kind<'tcx>() -> &'tcx StatementKind<'tcx> {
    &StatementKind::Nop
}

pub fn statement_or_terminator_at<'tcx>(
    tcx: TyCtxt<'tcx>,
    unit: Unit<'tcx>,
) -> StatementOrTerminator<'tcx> {
    if unit.location == DUMMY_HEAD_LOCATION {
        return StatementOrTerminator::Statement(nop_statement_kind());
    }
    if unit.location == DUMMY_RESUME_LOCATION {
        return StatementOrTerminator::Terminator(&TerminatorKind::UnwindResume);
    }

    let mir = if drop_shim::is_drop_shim(tcx, unit.func) {
        drop_shim::drop_shim_body(tcx, unit.func)
    } else {
        tcx.optimized_mir(unit.func.def_id)
    };
    let basic_block = mir.basic_blocks.get(unit.location.block).unwrap();
    if unit.location.statement_index < basic_block.statements.len() {
        let stmt = &basic_block.statements[unit.location.statement_index];
        return StatementOrTerminator::Statement(&stmt.kind);
    } else {
        assert!(unit.location.statement_index == basic_block.statements.len());
        let terminator = basic_block.terminator();
        return StatementOrTerminator::Terminator(&terminator.kind);
    }
}


impl<'tcx> std::fmt::Debug for Unit<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let func_name = util::parse_func_name_from_def_id(self.func.def_id);
        if self.location == DUMMY_HEAD_LOCATION {
            write!(f, "{}::DUMMY_HEAD", func_name)
        } else if self.location == DUMMY_RESUME_LOCATION {
            write!(f, "{}::DUMMY_RESUME", func_name)
        } else {
            write!(f, "{}::{:?}", func_name, self.location)
        }
    }
}

impl<'tcx> Unit<'tcx> {
    pub fn is_call_stmt(&self, tcx: TyCtxt<'tcx>) -> bool {
        if let StatementOrTerminator::Terminator(terminator) =
            statement_or_terminator_at(tcx, *self)
        {
            if let TerminatorKind::Call { .. } = terminator {
                return true;
            }
        }
        return false;
    }

    pub fn is_drop_stmt(&self, tcx: TyCtxt<'tcx>) -> bool {
        if let StatementOrTerminator::Terminator(terminator) =
            statement_or_terminator_at(tcx, *self)
        {
            matches!(terminator, TerminatorKind::Drop { .. })
        } else {
            false
        }
    }

    pub fn is_block_start_stmt(&self) -> bool {
        return self.location.statement_index == 0;
    }

    /// Returns the arguments and destination of a call statement.
    pub fn args_and_destination(&self, tcx: TyCtxt<'tcx>) -> (Vec<Operand<'tcx>>, Place<'tcx>) {
        let (args, destination) =
            match statement_or_terminator_at(tcx, *self) {
                StatementOrTerminator::Statement(stmt) => unreachable!(
                    "Expect a call statement at {:?}, found {:?}",
                    self.location, stmt,
                ),
                StatementOrTerminator::Terminator(terminator) => match terminator {
                    TerminatorKind::Call {
                        func: _,
                        args,
                        destination,
                        ..
                    } => (args, destination),
                    _ => unreachable!(
                        "Expect a call statement at {:?}, found {:?}",
                        self, terminator,
                    ),
                },
            };
        (
            args.iter().map(|arg| arg.node.clone()).collect(),
            *destination,
        )
    }

    /// Returns the destination place of a call statement.
    pub fn call_destination(&self, tcx: TyCtxt<'tcx>) -> Place<'tcx> {
        let (_, destination) = self.args_and_destination(tcx);
        destination
    }

    /// Returns the arguments of a call statement.
    pub fn call_args(&self, tcx: TyCtxt<'tcx>) -> Vec<Operand<'tcx>> {
        let (args, _) = self.args_and_destination(tcx);
        args
    }

    /// Returns the successor unit after a call returns.
    pub fn call_succ_unit(&self, tcx: TyCtxt<'tcx>) -> Option<Unit<'tcx>> {
        if let StatementOrTerminator::Terminator(terminator) =
            statement_or_terminator_at(tcx, *self)
        {
            match terminator {
                TerminatorKind::Call { target, .. } => {
                    target.map(|target| Unit::new(self.func, target.start_location()))
                }
                _ => {
                    panic!("Expect a call terminator at {:?}", self);
                }
            }
        } else {
            panic!("Expect a terminator at {:?}", self);
        }
    }
}
