use smallvec::{smallvec, SmallVec};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use rustc_middle::mir::{self, BasicBlocks};
use rustc_middle::ty::{Ty, TyCtxt};

use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::cfg::{CFGConfig, CFGQueries, SwitchInt, TailKind, tail_kind};
use crate::infoflow::{CallGraph, Unit};
use crate::mir::drop_shim::{self, is_drop_shim, DropShims};
use crate::mir::function::FuncDef;
use crate::mir::ContainingFunction;
use crate::util::{self, type_util};
use crate::infoflow::cfg::infoflow_cfg::DUMMY_RESUME_LOCATION;

pub const HEAD_BLOCK: mir::BasicBlock = mir::BasicBlock::ZERO;

/// A node representation in the Basic Block Control Flow Graph.
#[derive(Copy, Clone, PartialEq, Eq, Hash)]
pub enum BBCFGNode<'tcx> {
    BlockBody {
        func: FuncDef<'tcx>,
        bb: mir::BasicBlock,
    },
    Terminator(Unit<'tcx>),
}

pub struct BasicBlockCFG<'tcx> {
    tcx: TyCtxt<'tcx>,
    call_graph: Rc<CallGraph<'tcx>>,
    drop_shims: Rc<DropShims<'tcx>>,
    block_graph_map: RefCell<HashMap<FuncDef<'tcx>, BlockGraph<'tcx>>>,
    config: CFGConfig,
}

impl<'tcx> std::fmt::Debug for BBCFGNode<'tcx> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BBCFGNode::BlockBody { func, bb } => {
                let func_name = util::parse_func_name_from_def_id(func.def_id);
                write!(f, "{}::{:?}", func_name, bb)
            }
            BBCFGNode::Terminator(unit) => {
                write!(f, "{:?}", unit)
            }
        }
    }
}

impl<'tcx> ContainingFunction<FuncDef<'tcx>> for BBCFGNode<'tcx> {
    fn containing_function(self) -> FuncDef<'tcx> {
        match self {
            BBCFGNode::BlockBody { func, .. } => func,
            BBCFGNode::Terminator(unit) => unit.func,
        }
    }
}

impl<'tcx> BBCFGNode<'tcx> {
    pub fn block(&self) -> mir::BasicBlock {
        match self {
            BBCFGNode::BlockBody { bb, .. } => *bb,
            BBCFGNode::Terminator(unit) => unit.location.block,
        }
    }
}

impl<'tcx> BasicBlockCFG<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        call_graph: Rc<CallGraph<'tcx>>,
        drop_shims: Rc<DropShims<'tcx>>,
        config: CFGConfig,
    ) -> Self {
        BasicBlockCFG {
            tcx,
            call_graph,
            drop_shims,
            block_graph_map: RefCell::new(HashMap::new()),
            config,
        }
    }

    pub fn drop_func_def(&self, ty: Ty<'tcx>) -> FuncDef<'tcx> {
        drop_shim::drop_func_def(self.tcx, ty)
    }

    fn new_block_graph(&self, func: FuncDef<'tcx>) -> BlockGraph<'tcx> {
        if is_drop_shim(self.tcx, func) {
            let body = self.drop_shims.body(self.tcx, func);
            BlockGraph::new(func, &body.basic_blocks, self.config.dummy_resume)
        } else if self.tcx.is_mir_available(func.def_id) {
            let mir = self.tcx.optimized_mir(func.def_id);
            BlockGraph::new(func, &mir.basic_blocks, self.config.dummy_resume)
        } else {
            unreachable!("No MIR available for non-drop function {:?}", func.def_id);
        }
    }

    fn with_block_graph<T>(
        &self,
        func: FuncDef<'tcx>,
        f: impl Fn(&mut BlockGraph<'tcx>) -> T,
    ) -> T {
        let mut block_graph_map = self.block_graph_map.borrow_mut();
        let block_graph = block_graph_map
            .entry(func)
            .or_insert_with(|| self.new_block_graph(func));
        f(block_graph)
    }

    fn model_drop_calls(&self) -> bool {
        self.config.model_drop_calls
    }

}

impl<'tcx> InterproceduralCFG<BBCFGNode<'tcx>, FuncDef<'tcx>> for BasicBlockCFG<'tcx> {
    fn get_function_of(&self, n: BBCFGNode<'tcx>) -> FuncDef<'tcx> {
        n.containing_function()
    }

    fn get_preds_of(&self, n: BBCFGNode<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        self.with_block_graph(self.get_function_of(n), |block_graph| {
            block_graph.get_preds_of(n)
        })
    }

    fn get_succs_of(&self, n: BBCFGNode<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        self.with_block_graph(self.get_function_of(n), |block_graph| {
            block_graph.get_succs_of(n)
        })
    }

    fn get_callees_of_call_at(&self, n: BBCFGNode<'tcx>) -> SmallVec<[FuncDef<'tcx>; 1]> {
        self.with_block_graph(self.get_function_of(n), |block_graph| {
            match n {
                BBCFGNode::BlockBody { .. } => panic!("Get callees for a block body!"),
                BBCFGNode::Terminator(callsite) => {
                    if block_graph.get_call_nodes().contains(&n) {
                        // A call site — works uniformly for regular functions and drop shims
                        self.call_graph.get_callees(&callsite)
                    } else if self.model_drop_calls() && block_graph.get_drop_nodes().contains_key(&n) {
                        // A drop site (only reachable when model_drop_calls is enabled)
                        let drop_place = block_graph.get_drop_nodes().get(&n).unwrap();
                        let drop_ty = type_util::place_ty(self.tcx, drop_place, n.containing_function());
                        let callee = self.drop_func_def(drop_ty);
                        smallvec![callee]
                    } else {
                        panic!("Get callees for a Non-Call site!");
                    }
                }
            }
        })
    }

    fn get_callers_of(&self, f: FuncDef<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        // We currently do not get callers of drop functions.
        // It is safe since we do not start analysis from drop functions
        if is_drop_shim(self.tcx, f) {
            return SmallVec::new();
        }
        self.call_graph
            .get_callers(&f)
            .cloned()
            .unwrap_or_default()
            .iter()
            .map(|callsite| BBCFGNode::Terminator(callsite.clone()))
            .collect()
    }

    fn get_start_points_of(&self, f: FuncDef<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        if !self.tcx.is_mir_available(f.def_id) && !is_drop_shim(self.tcx, f) {
            return SmallVec::new();
        }
        self.with_block_graph(f, |block_graph| smallvec![block_graph.get_head()])
    }

    fn get_end_points_of(&self, f: FuncDef<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        if !self.tcx.is_mir_available(f.def_id) && !is_drop_shim(self.tcx, f) {
            return SmallVec::new();
        }
        self.with_block_graph(f, |block_graph| block_graph.get_tails().clone())
    }

    fn get_return_sites_of_call_at(&self, n: BBCFGNode<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        self.get_succs_of(n)
    }

    fn get_preds_of_call_at(&self, n: BBCFGNode<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        self.get_preds_of(n)
    }

    /// Returns true if the node is a call site, or a drop node when `model_drop_calls` is enabled.
    fn is_call_node(&self, n: BBCFGNode<'tcx>) -> bool {
        self.with_block_graph(self.get_function_of(n), |block_graph| {
            block_graph.get_call_nodes().contains(&n)
                || (self.model_drop_calls() && block_graph.get_drop_nodes().contains_key(&n))
        })
    }

    fn is_exit_node(&self, n: BBCFGNode<'tcx>) -> bool {
        self.with_block_graph(self.get_function_of(n), |block_graph| {
            block_graph.get_tails().contains(&n)
        })
    }

    fn is_start_point(&self, n: BBCFGNode<'tcx>) -> bool {
        self.with_block_graph(self.get_function_of(n), |block_graph| {
            block_graph.get_head() == n
        })
    }

    fn is_feasible_interprocedural_flow(
        &self,
        call_site: BBCFGNode<'tcx>,
        source: BBCFGNode<'tcx>,
        target: BBCFGNode<'tcx>,
    ) -> bool {
        if self.is_exit_node(source) {
            // process_exit case: source is a callee exit node, target is a return site.
            let tail_kind = self.get_tail_kind(source);
            let is_unwind = self.is_unwind_branch(call_site, target);
            match tail_kind {
                TailKind::Return => !is_unwind,
                TailKind::UnwindResume => {
                    // Block unwind flows from drop shims 
                    if is_drop_shim(self.tcx, source.containing_function()) {
                        return false;
                    }
                    is_unwind
                }
                TailKind::UnwindTerminate => false,
                TailKind::Unreachable => {
                    self.get_end_points_of(source.containing_function()).len() <= 1
                }
            }
        } else {
            true
        }
    }
}

impl<'tcx> CFGQueries<'tcx, BBCFGNode<'tcx>> for BasicBlockCFG<'tcx> {
    fn is_conditional_branch_from(&self, node: BBCFGNode<'tcx>) -> bool {
        self.with_block_graph(node.containing_function(), |block_graph| {
            block_graph.is_conditional_branch_from(node)
        })
    }

    fn get_switch_int(&self, node: BBCFGNode<'tcx>) -> Option<SwitchInt<'tcx>> {
        self.with_block_graph(node.containing_function(), |block_graph| {
            block_graph.get_switch_int(node)
        })
    }

    fn is_switch_discr(&self, func: FuncDef<'tcx>, place: &mir::Place<'tcx>) -> bool {
        self.with_block_graph(func, |block_graph| block_graph.is_switch_discr(place))
    }

    fn is_unwind_branch(&self, from: BBCFGNode<'tcx>, to: BBCFGNode<'tcx>) -> bool {
        assert!(from.containing_function() == to.containing_function());
        self.with_block_graph(from.containing_function(), |block_graph| {
            block_graph.is_unwind_branch(from, to)
        })
    }

    fn is_dummy_resume(&self, n: BBCFGNode<'tcx>) -> bool {
        match n {
            BBCFGNode::Terminator(unit) => unit.location == DUMMY_RESUME_LOCATION,
            _ => false,
        }
    }

    fn get_tail_kind(&self, n: BBCFGNode<'tcx>) -> TailKind {
        self.with_block_graph(n.containing_function(), |block_graph| {
            block_graph.get_tail_kind(n)
        })
    }
}

pub struct BlockGraph<'tcx> {
    head: BBCFGNode<'tcx>,
    // A function call may unwind continue directly. Instead of treating the call node as a tail node, 
    // we create a dummy resume node and let the call node branch to the dummy resume node. 
    dummy_resume: BBCFGNode<'tcx>,
    tails: SmallVec<[BBCFGNode<'tcx>; 2]>,
    calls: HashSet<BBCFGNode<'tcx>>,
    drops: HashMap<BBCFGNode<'tcx>, mir::Place<'tcx>>,
    tail_kinds: HashMap<BBCFGNode<'tcx>, TailKind>,
    switches: HashMap<BBCFGNode<'tcx>, SwitchInt<'tcx>>,
    switch_discrs: HashSet<mir::Place<'tcx>>,
    unwind_branchs: HashSet<(BBCFGNode<'tcx>, BBCFGNode<'tcx>)>,
    node_to_succs: HashMap<BBCFGNode<'tcx>, SmallVec<[BBCFGNode<'tcx>; 2]>>,
    node_to_preds: HashMap<BBCFGNode<'tcx>, SmallVec<[BBCFGNode<'tcx>; 2]>>,
}

impl<'tcx> BlockGraph<'tcx> {
    pub fn new(func: FuncDef<'tcx>, basic_blocks: &BasicBlocks<'tcx>, dummy_resume: bool) -> Self {
        let dummy_resume_node = BBCFGNode::Terminator(
            Unit::new(func, DUMMY_RESUME_LOCATION)
        );
        let mut tails = SmallVec::new();
        let mut calls = HashSet::new();
        let mut drops = HashMap::new();
        let mut tail_kinds = HashMap::new();
        let mut switches = HashMap::new();
        let mut switch_discrs = HashSet::new();
        let mut unwind_branchs = HashSet::new();
        let mut node_to_succs: HashMap<BBCFGNode<'tcx>, SmallVec<[BBCFGNode<'tcx>; 2]>> =
            HashMap::new();
        let mut node_to_preds: HashMap<BBCFGNode<'tcx>, SmallVec<[BBCFGNode<'tcx>; 2]>> =
            HashMap::new();
        let head = BBCFGNode::BlockBody { func, bb: HEAD_BLOCK };

        let mut reach_dummy_resume = false;
        
        for bb in basic_blocks.indices() {
            let bb_node = BBCFGNode::BlockBody { func, bb };
            let mir::BasicBlockData {
                ref statements,
                ref terminator,
                ..
            } = &basic_blocks[bb];
            if let Some(mir::Terminator {
                source_info: _,
                ref kind,
            }) = *terminator
            {
                let terminator_unit = Unit::new(
                    func,
                    mir::Location {
                        block: bb,
                        statement_index: statements.len(),
                    },
                );
                let terminator_node = BBCFGNode::Terminator(terminator_unit);
                node_to_succs.entry(bb_node).or_default().push(terminator_node);
                node_to_preds.entry(terminator_node).or_default().push(bb_node);
                match kind {
                    mir::TerminatorKind::Call { .. } => {
                        // Some function calls, like `panic`, do not have return targets, 
                        // we regard them as tail node.
                        let tail_kind = tail_kind(kind);
                        match tail_kind {
                            Some(TailKind::Unreachable) 
                            | Some(TailKind::UnwindTerminate) => {
                                tails.push(terminator_node);
                                tail_kinds.insert(terminator_node, tail_kind.unwrap());
                            }
                            _ => {
                                calls.insert(terminator_node);
                            }
                        }
                    }
                    mir::TerminatorKind::Drop { place, .. } => {
                        drops.insert(terminator_node, place.clone());
                    }
                    _ => {}
                }
                if dummy_resume {
                    match kind {
                        mir::TerminatorKind::Call { unwind, .. }
                        | mir::TerminatorKind::Drop { unwind, .. }
                        | mir::TerminatorKind::Assert { unwind, .. } => {
                            if let mir::UnwindAction::Continue = unwind {
                                node_to_succs.entry(terminator_node).or_default().push(dummy_resume_node);
                                node_to_preds.entry(dummy_resume_node).or_default().push(terminator_node);
                                unwind_branchs.insert((terminator_node, dummy_resume_node));
                                reach_dummy_resume = true;
                            }
                        }
                        _ => {}
                    }
                }
                let terminator_edges = kind.edges();
                match terminator_edges {
                    mir::TerminatorEdges::None => {
                        tails.push(terminator_node);
                        let tail_kind = tail_kind(kind).unwrap();
                        tail_kinds.insert(terminator_node, tail_kind);
                    }
                    mir::TerminatorEdges::Single(target) => {
                        let next_node = BBCFGNode::BlockBody { func, bb: target };
                        node_to_succs.entry(terminator_node).or_default().push(next_node);
                        node_to_preds.entry(next_node).or_default().push(terminator_node);
                    }
                    mir::TerminatorEdges::Double(target, unwind) => {
                        let next_node = BBCFGNode::BlockBody { func, bb: target };
                        node_to_succs.entry(terminator_node).or_default().push(next_node);
                        node_to_preds.entry(next_node).or_default().push(terminator_node);
                        let unwind_node = BBCFGNode::BlockBody { func, bb: unwind };
                        node_to_succs.entry(terminator_node).or_default().push(unwind_node);
                        node_to_preds.entry(unwind_node).or_default().push(terminator_node);
                        unwind_branchs.insert((terminator_node, unwind_node));
                    }
                    mir::TerminatorEdges::AssignOnReturn {
                        return_, cleanup, ..
                    } => {
                        for target in return_ {
                            let next_node = BBCFGNode::BlockBody { func, bb: *target };
                            node_to_succs.entry(terminator_node).or_default().push(next_node);
                            node_to_preds.entry(next_node).or_default().push(terminator_node);
                        }
                        if let Some(unwind) = cleanup {
                            let unwind_node = BBCFGNode::BlockBody { func, bb: unwind };
                            node_to_succs.entry(terminator_node).or_default().push(unwind_node);
                            node_to_preds.entry(unwind_node).or_default().push(terminator_node);
                            unwind_branchs.insert((terminator_node, unwind_node));
                        }
                    }
                    mir::TerminatorEdges::SwitchInt { targets, discr } => {
                        switches.insert(terminator_node, SwitchInt::new(discr.clone(), targets.clone()));
                        if let mir::Operand::Copy(place) | mir::Operand::Move(place) = discr {
                            switch_discrs.insert(*place);
                        }
                        for &target in targets.all_targets() {
                            let next_node = BBCFGNode::BlockBody { func, bb: target };
                            node_to_succs.entry(terminator_node).or_default().push(next_node);
                            node_to_preds.entry(next_node).or_default().push(terminator_node);
                        }
                    }
                }
            }
        }
        if reach_dummy_resume {
            tails.push(dummy_resume_node);
            tail_kinds.insert(dummy_resume_node, TailKind::UnwindResume);
        }
        BlockGraph {
            head,
            dummy_resume: dummy_resume_node,
            tails,
            calls,
            drops,
            tail_kinds,
            switches,
            switch_discrs,
            unwind_branchs,
            node_to_succs,
            node_to_preds,
        }
    }

    pub fn get_head(&self) -> BBCFGNode<'tcx> {
        self.head
    }

    pub fn get_tails(&self) -> &SmallVec<[BBCFGNode<'tcx>; 2]> {
        &self.tails
    }
    
    pub fn get_dummy_resume(&self) -> BBCFGNode<'tcx> {
        self.dummy_resume
    }

    pub fn get_call_nodes(&self) -> &HashSet<BBCFGNode<'tcx>> {
        &self.calls
    }

    pub fn get_drop_nodes(&self) -> &HashMap<BBCFGNode<'tcx>, mir::Place<'tcx>> {
        &self.drops
    }

    pub fn get_succs_of(&self, n: BBCFGNode<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        if let Some(succs) = self.node_to_succs.get(&n) {
            succs.clone()
        } else {
            SmallVec::new()
        }
    }

    pub fn get_preds_of(&self, n: BBCFGNode<'tcx>) -> SmallVec<[BBCFGNode<'tcx>; 2]> {
        if let Some(preds) = self.node_to_preds.get(&n) {
            preds.clone()
        } else {
            SmallVec::new()
        }
    }

    pub fn get_tail_kind(&self, n: BBCFGNode<'tcx>) -> TailKind {
        self.tail_kinds.get(&n).unwrap().clone()
    }

    pub fn is_switch_discr(&self, place: &mir::Place<'tcx>) -> bool {
        self.switch_discrs.contains(place)
    }

    pub fn is_unwind_branch(&self, from: BBCFGNode<'tcx>, to: BBCFGNode<'tcx>) -> bool {
        self.unwind_branchs.contains(&(from, to))
    }
    
    pub fn is_conditional_branch_from(&self, from: BBCFGNode<'tcx>) -> bool {
        self.switches.contains_key(&from)
    }

    pub fn get_switch_int(&self, n: BBCFGNode<'tcx>) -> Option<SwitchInt<'tcx>> {
        self.switches.get(&n).cloned()
    }
}
