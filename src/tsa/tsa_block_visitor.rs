#![allow(dead_code, unused_imports)]
use rustc_middle::mir::{BasicBlock, BasicBlockData};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_path::AccessPath;
use crate::mir::function::FuncDef;
use crate::tsa::state::{SymbState, SymbStateSupport, TypeState};
use crate::tsa::state_transition::TypeStateTransition;
use crate::tsa::tsa_statement_visitor::TSAStatementVisitor;

/// Block-level visitor that iterates over all statements in a basic block,
/// delegating each statement to TSAStatementVisitor.
pub struct TSABlockVisitor<
    'tcx,
    'analysis,
    'b,
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
> {
    acx: &'analysis AnalysisContext<'tcx>,
    func: FuncDef<'tcx>,
    bb: BasicBlock,
    block_data: &'b BasicBlockData<'tcx>,
    pub out_state: SymbState<'tcx, S, AccessPath<'tcx>>,
    pub trans: T,
}

impl<'tcx, 'analysis, 'b, S, T> TSABlockVisitor<'tcx, 'analysis, 'b, S, T>
where
    S: TypeState,
    T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
{
    pub fn new(
        acx: &'analysis AnalysisContext<'tcx>,
        func: FuncDef<'tcx>,
        bb: BasicBlock,
        block_data: &'b BasicBlockData<'tcx>,
        in_state: &SymbState<'tcx, S, AccessPath<'tcx>>,
        trans: T,
    ) -> Self {
        TSABlockVisitor {
            acx,
            func,
            bb,
            block_data,
            out_state: in_state.clone_owned(),
            trans,
        }
    }

    /// Iterate over all statements in the block, delegating each to TSAStatementVisitor.
    /// Creates one TSAStatementVisitor for the whole block — no per-statement cloning.
    pub fn visit(&mut self) {
        let BasicBlockData { ref statements, .. } = self.block_data;
        if statements.is_empty() {
            return;
        }

        // Create one statement visitor initialized with current out_state.
        // visit_statement mutates out_state in place — no clone per iteration.
        let mut sv = TSAStatementVisitor::new(
            self.acx,
            self.func,
            &self.out_state,
            self.trans,
        );

        let mut location = self.bb.start_location();
        while location.statement_index < statements.len() {
            sv.visit_statement(location, &statements[location.statement_index]);
            location.statement_index += 1;
        }

        self.out_state = sv.out_state;
    }
}
