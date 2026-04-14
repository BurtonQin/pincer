use std::collections::HashSet;
use rustc_middle::ty::TyCtxt;
use rustc_middle::mir::Place;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::cfg::block_cfg::BBCFGNode;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::path_edge::{PathEdge, PathEdgeData, PathEdgeNode};
use crate::mir::drop_shim;
use crate::mir::unit::{Unit, StatementOrTerminator, statement_or_terminator_at};
use crate::mir::ContainingFunction;
use crate::mir::function::FuncDef;
use crate::tsa::state::{ExecutionState, SymbState, SymbStateSupport, TypeState};
use crate::tsa::state_transition::TypeStateTransition;
use crate::tsa::tsa_statement_visitor::TSAStatementVisitor;

pub mod abstract_value;
pub mod analyses;
pub mod aliasing_xor_mutability;
pub mod state;
pub mod state_transition;
pub mod tsa_block_visitor;
pub mod tsa_statement_visitor;
pub mod tsa_flow_functions;
pub mod tsa_call_handlers;
pub mod tsa_path_edge_functions;
pub mod tsa_problem;
pub mod tsa_solver;

/// Trait for nodes used in TSA analysis, abstracting over block-level and statement-level granularity.
pub trait TSAPathEdgeNode<'tcx>: PathEdgeNode + ContainingFunction<FuncDef<'tcx>> + std::fmt::Debug {
    /// Extract the callsite Unit from this node. Panics if the node is not a callsite.
    fn as_callsite(&self) -> Unit<'tcx>;
    /// Convert this node to a Unit. For BBCFGNode::BlockBody, returns the block's start location.
    fn as_unit(&self) -> Unit<'tcx>;
    /// Construct a node from a Unit.
    fn from_unit(tcx: TyCtxt<'tcx>, unit: Unit<'tcx>) -> Self;

    /// Apply normal flow for this node to `state`, returning the updated state.
    /// Returns `None` for pure terminator nodes; the caller should invoke `terminator_normal_flow` from `tsa_flow_functions`.
    fn apply_normal_flow<S, T>(
        &self,
        acx: &AnalysisContext<'tcx>,
        state: &SymbState<'tcx, S, AccessPath<'tcx>>,
        trans: T,
    ) -> Option<SymbState<'tcx, S, AccessPath<'tcx>>>
    where
        S: TypeState,
        T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>;
}

impl<'tcx> TSAPathEdgeNode<'tcx> for BBCFGNode<'tcx> {
    fn as_callsite(&self) -> Unit<'tcx> {
        match self {
            BBCFGNode::Terminator(unit) => *unit,
            BBCFGNode::BlockBody { .. } => panic!("BlockBody is not a callsite"),
        }
    }

    fn as_unit(&self) -> Unit<'tcx> {
        match self {
            BBCFGNode::BlockBody { func, bb } => Unit::new(*func, bb.start_location()),
            BBCFGNode::Terminator(unit) => *unit,
        }
    }

    fn from_unit(tcx: TyCtxt<'tcx>, unit: Unit<'tcx>) -> Self {
        match statement_or_terminator_at(tcx, unit) {
            StatementOrTerminator::Terminator(_) => BBCFGNode::Terminator(unit),
            StatementOrTerminator::Statement(_) => BBCFGNode::BlockBody {
                func: unit.func,
                bb: unit.location.block,
            },
        }
    }

    fn apply_normal_flow<S, T>(
        &self,
        acx: &AnalysisContext<'tcx>,
        state: &SymbState<'tcx, S, AccessPath<'tcx>>,
        trans: T,
    ) -> Option<SymbState<'tcx, S, AccessPath<'tcx>>>
    where
        S: TypeState,
        T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
    {
        match self {
            BBCFGNode::BlockBody { func, bb } => {
                let body = if drop_shim::is_drop_shim(acx.tcx, *func) {
                    acx.drop_shim_body(*func)
                } else {
                    acx.tcx.optimized_mir(func.def_id)
                };
                let block_data = &body.basic_blocks[*bb];
                let mut sv = TSAStatementVisitor::new(acx, *func, state, trans);
                let mut loc = bb.start_location();
                for stmt in &block_data.statements {
                    sv.visit_statement(loc, stmt);
                    loc.statement_index += 1;
                }
                Some(sv.out_state)
            }
            BBCFGNode::Terminator(_) => None,
        }
    }
}

impl<'tcx> TSAPathEdgeNode<'tcx> for Unit<'tcx> {
    fn as_callsite(&self) -> Unit<'tcx> {
        *self
    }

    fn as_unit(&self) -> Unit<'tcx> {
        *self
    }

    fn from_unit(_tcx: TyCtxt<'tcx>, unit: Unit<'tcx>) -> Self {
        unit
    }

    fn apply_normal_flow<S, T>(
        &self,
        acx: &AnalysisContext<'tcx>,
        state: &SymbState<'tcx, S, AccessPath<'tcx>>,
        trans: T,
    ) -> Option<SymbState<'tcx, S, AccessPath<'tcx>>>
    where
        S: TypeState,
        T: TypeStateTransition<'tcx, S, AccessPath<'tcx>>,
    {
        let body = if drop_shim::is_drop_shim(acx.tcx, self.func) {
            acx.drop_shim_body(self.func)
        } else {
            acx.tcx.optimized_mir(self.func.def_id)
        };
        let block_data = &body.basic_blocks[self.location.block];
        let stmt = block_data.statements.get(self.location.statement_index)?;
        let mut sv = TSAStatementVisitor::new(acx, self.func, state, trans);
        sv.visit_statement(self.location, stmt);
        Some(sv.out_state)
    }
}

pub type TSAPathEdgeData<'tcx, S> = SymbState<'tcx, S, AccessPath<'tcx>>;
pub type TSAPathEdge<'tcx, S, N> = PathEdge<N, TSAPathEdgeData<'tcx, S>>;

impl<'tcx, S, P> PathEdgeData for SymbState<'tcx, S, P>
where
    S: TypeState,
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
}

impl<'tcx> PathEdgeNode for BBCFGNode<'tcx> {}

pub struct PrevEdgeOfErrorState<'tcx, S, N, P>
where
    S: TypeState,
    N: TSAPathEdgeNode<'tcx>,
    P: std::cmp::Eq + std::hash::Hash + Copy,
{
    pub prev_edge: TSAPathEdge<'tcx, S, N>,
    pub error_state: SymbState<'tcx, S, P>,
}

/// Return all aliases that are projections starting from the given place
pub fn aliases_project_from<'tcx, 'a>(
    acx: &AnalysisContext<'tcx>,
    aliases: &'a HashSet<AccessPath<'tcx>>,
    place: &Place<'tcx>,
) -> Vec<&'a AccessPath<'tcx>> {
    aliases
        .iter()
        .filter(|alias| {
            if alias.has_ref_elem() {
                if !alias.is_indirect() {
                    false
                } else {
                    let alias_base = alias.truncate_from_last_deref().unwrap();
                    alias_base.is_projection_of(acx, &place)
                }
            } else {
                alias.is_projection_of(acx, &place)
            }
        })
        .collect::<Vec<_>>()
}

pub fn initial_seed<'tcx, S, N>(
    tcx: TyCtxt<'tcx>,
    init_aliases: HashSet<AccessPath<'tcx>>,
    init_type_state: S,
    start_unit: Unit<'tcx>,
) -> (N, TSAPathEdgeData<'tcx, S>)
where
    S: TypeState,
    N: TSAPathEdgeNode<'tcx>,
{
    let start_node = N::from_unit(tcx, start_unit);
    let exec_state = ExecutionState::init_exec_state(init_aliases);
    let state = SymbState::new_symb_state(init_type_state, exec_state);
    (start_node, state)
}
