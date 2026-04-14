use rustc_middle::mir::{self, Location, TerminatorEdges};
use rustc_middle::ty::TyCtxt;
use smallvec::{smallvec, SmallVec};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::cfg::{CFGConfig, CFGQueries, SwitchInt, TailKind, tail_kind};
use crate::infoflow::{CallGraph, Unit};
use crate::mir::drop_shim::{self, is_drop_shim, DropShims};
use crate::mir::function::FuncDef;
use crate::util::type_util;

pub const HEAD_LOCATION: Location = Location {
    block: mir::BasicBlock::ZERO,
    statement_index: 0,
};

pub const DUMMY_HEAD_LOCATION: Location = Location {
    block: mir::BasicBlock::MAX,
    statement_index: 0,
};

pub const DUMMY_RESUME_LOCATION: Location = Location {
    block: mir::BasicBlock::from_u32(mir::BasicBlock::MAX_AS_U32 - 1),
    statement_index: 0,
};

pub struct InfoflowCFG<'tcx> {
    tcx: TyCtxt<'tcx>,
    call_graph: Rc<CallGraph<'tcx>>,
    drop_shims: Rc<DropShims<'tcx>>,
    unit_graph_map: RefCell<HashMap<FuncDef<'tcx>, UnitGraph<'tcx>>>,
    dummy_head: bool,
    config: CFGConfig,
}

impl<'tcx> InfoflowCFG<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        call_graph: Rc<CallGraph<'tcx>>,
        drop_shims: Rc<DropShims<'tcx>>,
        config: CFGConfig,
    ) -> InfoflowCFG<'tcx> {
        InfoflowCFG {
            tcx,
            call_graph,
            drop_shims,
            unit_graph_map: RefCell::new(HashMap::new()),
            dummy_head: false,
            config,
        }
    }

    pub fn new_with_dummy_head(
        tcx: TyCtxt<'tcx>,
        call_graph: Rc<CallGraph<'tcx>>,
        drop_shims: Rc<DropShims<'tcx>>,
        config: CFGConfig,
    ) -> InfoflowCFG<'tcx> {
        InfoflowCFG {
            tcx,
            call_graph,
            drop_shims,
            unit_graph_map: RefCell::new(HashMap::new()),
            dummy_head: true,
            config,
        }
    }

    fn model_drop_calls(&self) -> bool {
        self.config.model_drop_calls
    }

    pub fn new_unit_graph(&self, func: FuncDef<'tcx>) -> UnitGraph<'tcx> {
        if is_drop_shim(self.tcx, func) {
            let body = self.drop_shims.body(self.tcx, func);
            UnitGraph::new(func, body, self.dummy_head, self.config.dummy_resume)
        } else if self.tcx.is_mir_available(func.def_id) {
            let mir = self.tcx.optimized_mir(func.def_id);
            UnitGraph::new(func, mir, self.dummy_head, self.config.dummy_resume)
        } else {
            unreachable!("No MIR available for non-drop function {:?}", func.def_id);
        }
    }

    pub fn with_unit_graph<T>(&self, func: FuncDef<'tcx>, f: impl Fn(&mut UnitGraph<'tcx>) -> T) -> T {
        let mut unit_graph_map = self.unit_graph_map.borrow_mut();
        let unit_graph = unit_graph_map
            .entry(func)
            .or_insert_with(|| self.new_unit_graph(func));
        f(unit_graph)
    }
}

impl<'tcx> InterproceduralCFG<Unit<'tcx>, FuncDef<'tcx>> for InfoflowCFG<'tcx> {
    fn get_function_of(&self, n: Unit<'tcx>) -> FuncDef<'tcx> {
        n.func
    }

    fn get_preds_of(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.with_unit_graph(n.func, |unit_graph| unit_graph.get_preds_of(n))
    }

    fn get_succs_of(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.with_unit_graph(n.func, |unit_graph| unit_graph.get_succs_of(n))
    }

    fn get_callees_of_call_at(&self, n: Unit<'tcx>) -> SmallVec<[FuncDef<'tcx>; 1]> {
        self.with_unit_graph(n.func, |unit_graph| {
            if unit_graph.get_call_stmts().contains(&n) {
                // A call site — works uniformly for regular functions and drop shims
                self.call_graph.get_callees(&n)
            } else if self.model_drop_calls() && unit_graph.get_drop_stmts().contains_key(&n) {
                // A drop site (only reachable when model_drop_calls is enabled)
                let drop_place = unit_graph.get_drop_stmts().get(&n).unwrap();
                let drop_ty = type_util::place_ty(self.tcx, drop_place, n.func);
                let callee = drop_shim::drop_func_def(self.tcx, drop_ty);
                smallvec![callee]
            } else {
                panic!("Get callees for a Non-Call site!");
            }
        })
    }

    fn get_callers_of(&self, f: FuncDef<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        // We currently do not get callers of drop functions.
        // It is safe since we do not start analysis from drop functions.
        if is_drop_shim(self.tcx, f) {
            return SmallVec::new();
        }
        self.call_graph.get_callers(&f).cloned().unwrap_or_default()
    }

    fn get_start_points_of(&self, f: FuncDef<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        if !self.tcx.is_mir_available(f.def_id) && !is_drop_shim(self.tcx, f) {
            return SmallVec::new();
        }
        self.with_unit_graph(f, |unit_graph| smallvec![unit_graph.get_head()])
    }

    fn get_end_points_of(&self, f: FuncDef<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        if !self.tcx.is_mir_available(f.def_id) && !is_drop_shim(self.tcx, f) {
            return SmallVec::new();
        }
        self.with_unit_graph(f, |unit_graph| unit_graph.get_tails().clone())
    }

    fn get_return_sites_of_call_at(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.get_succs_of(n)
    }

    fn get_preds_of_call_at(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.get_preds_of(n)
    }

    fn is_call_node(&self, n: Unit<'tcx>) -> bool {
        self.with_unit_graph(n.func, |unit_graph| {
            unit_graph.get_call_stmts().contains(&n)
                || (self.model_drop_calls() && unit_graph.get_drop_stmts().contains_key(&n))
        })
    }

    fn is_exit_node(&self, n: Unit<'tcx>) -> bool {
        self.with_unit_graph(n.func, |unit_graph| unit_graph.get_tails().contains(&n))
    }

    fn is_start_point(&self, n: Unit<'tcx>) -> bool {
        self.with_unit_graph(n.func, |unit_graph| unit_graph.get_head() == n)
    }

    fn is_feasible_interprocedural_flow(
        &self,
        call_site: Unit<'tcx>,
        source: Unit<'tcx>,
        target: Unit<'tcx>,
    ) -> bool {
        if self.is_exit_node(source) {
            // process_exit case: source is a callee exit node, target is a return site.
            let tail_kind = self.with_unit_graph(source.func, |ug| ug.get_tail_kind(source));
            let is_unwind = self.with_unit_graph(call_site.func, |ug| ug.is_unwind_branch(call_site, target));
            match tail_kind {
                TailKind::Return => !is_unwind,
                TailKind::UnwindResume => {
                    // Block unwind flows from drop shims
                    if is_drop_shim(self.tcx, source.func) {
                        return false;
                    }
                    is_unwind
                }
                TailKind::UnwindTerminate => false,
                // Unreachable exits block flow unless it's the only exit of the callee
                // (e.g., intrinsics like `std::intrinsics::size_of_val`).
                TailKind::Unreachable => {
                    self.get_end_points_of(source.func).len() <= 1
                }
            }
        } else {
            true
        }
    }
}

impl<'tcx> CFGQueries<'tcx, Unit<'tcx>> for InfoflowCFG<'tcx> {
    fn is_conditional_branch_from(&self, node: Unit<'tcx>) -> bool {
        self.with_unit_graph(node.func, |ug| ug.is_conditional_branch_from(node))
    }

    fn get_switch_int(&self, node: Unit<'tcx>) -> Option<SwitchInt<'tcx>> {
        self.with_unit_graph(node.func, |ug| ug.get_switch_int(node))
    }

    fn is_switch_discr(&self, func: FuncDef<'tcx>, place: &mir::Place<'tcx>) -> bool {
        self.with_unit_graph(func, |ug| ug.is_switch_discr(place))
    }

    fn is_unwind_branch(&self, from: Unit<'tcx>, to: Unit<'tcx>) -> bool {
        assert!(from.func == to.func);
        self.with_unit_graph(from.func, |ug| ug.is_unwind_branch(from, to))
    }

    fn is_dummy_resume(&self, n: Unit<'tcx>) -> bool {
        n.location == DUMMY_RESUME_LOCATION
    }

    fn get_tail_kind(&self, n: Unit<'tcx>) -> TailKind {
        self.with_unit_graph(n.func, |ug| ug.get_tail_kind(n))
    }
}

pub struct UnitGraph<'tcx> {
    head: Unit<'tcx>,
    dummy_resume: Unit<'tcx>,
    tails: SmallVec<[Unit<'tcx>; 2]>,
    call_stmts: HashSet<Unit<'tcx>>,
    drop_stmts: HashMap<Unit<'tcx>, mir::Place<'tcx>>,
    tail_kinds: HashMap<Unit<'tcx>, TailKind>,
    unwind_branches: HashSet<(Unit<'tcx>, Unit<'tcx>)>,
    switches: HashMap<Unit<'tcx>, SwitchInt<'tcx>>,
    switch_discrs: HashSet<mir::Place<'tcx>>,
    unit_to_succs: HashMap<Unit<'tcx>, SmallVec<[Unit<'tcx>; 2]>>,
    unit_to_preds: HashMap<Unit<'tcx>, SmallVec<[Unit<'tcx>; 2]>>,
}

impl<'tcx> UnitGraph<'tcx> {
    pub fn new(func: FuncDef<'tcx>, mir: &mir::Body<'tcx>, dummy_head: bool, dummy_resume: bool) -> UnitGraph<'tcx> {
        let dummy_resume_unit = Unit::new(func, DUMMY_RESUME_LOCATION);
        let mut tails = SmallVec::new();
        let mut call_stmts = HashSet::new();
        let mut drop_stmts: HashMap<Unit<'tcx>, mir::Place<'tcx>> = HashMap::new();
        let mut tail_kinds: HashMap<Unit<'tcx>, TailKind> = HashMap::new();
        let mut unwind_branches: HashSet<(Unit<'tcx>, Unit<'tcx>)> = HashSet::new();
        let mut switches: HashMap<Unit<'tcx>, SwitchInt<'tcx>> = HashMap::new();
        let mut switch_discrs: HashSet<mir::Place<'tcx>> = HashSet::new();
        let mut unit_to_succs: HashMap<Unit<'tcx>, SmallVec<[Unit<'tcx>; 2]>> = HashMap::new();
        let mut unit_to_preds: HashMap<Unit<'tcx>, SmallVec<[Unit<'tcx>; 2]>> = HashMap::new();
        let head = if dummy_head {
            let dummy_head = Unit::new(func, DUMMY_HEAD_LOCATION);
            let head = Unit::new(func, HEAD_LOCATION);
            unit_to_succs.entry(dummy_head).or_default().push(head);
            unit_to_preds.entry(head).or_default().push(dummy_head);
            dummy_head
        } else {
            Unit::new(func, HEAD_LOCATION)
        };

        let mut reach_dummy_resume = false;

        for bb in mir.basic_blocks.indices() {
            let mir::BasicBlockData {
                ref statements,
                ref terminator,
                ..
            } = &mir[bb];
            let mut location = bb.start_location();
            let terminator_index = statements.len();

            while location.statement_index < terminator_index {
                let u1 = Unit::new(func, location);
                location.statement_index += 1;
                let u2 = Unit::new(func, location);
                unit_to_succs.entry(u1).or_default().push(u2);
                unit_to_preds.entry(u2).or_default().push(u1);
            }

            if let Some(mir::Terminator {
                source_info: _,
                ref kind,
            }) = *terminator
            {
                let terminator_unit = Unit::new(func, location);
                match kind {
                    mir::TerminatorKind::Call { .. } => {
                        call_stmts.insert(terminator_unit);
                    }
                    mir::TerminatorKind::Drop { place, .. } => {
                        drop_stmts.insert(terminator_unit, place.clone());
                    }
                    _ => {}
                }
                // For Call/Drop/Assert with UnwindAction::Continue,
                // add an edge to dummy_resume_unit so it acts as an implicit unwind sink.
                if dummy_resume {
                    match kind {
                        mir::TerminatorKind::Call { unwind, .. }
                        | mir::TerminatorKind::Drop { unwind, .. }
                        | mir::TerminatorKind::Assert { unwind, .. } => {
                            if let mir::UnwindAction::Continue = unwind {
                                unit_to_succs
                                    .entry(terminator_unit)
                                    .or_default()
                                    .push(dummy_resume_unit);
                                unit_to_preds
                                    .entry(dummy_resume_unit)
                                    .or_default()
                                    .push(terminator_unit);
                                unwind_branches.insert((terminator_unit, dummy_resume_unit));
                                reach_dummy_resume = true;
                            }
                        }
                        _ => {}
                    }
                }
                let terminator_edges = kind.edges();
                match terminator_edges {
                    TerminatorEdges::None => {
                        tails.push(terminator_unit);
                        if let Some(tk) = tail_kind(kind) {
                            tail_kinds.insert(terminator_unit, tk);
                        }
                    }
                    TerminatorEdges::Single(target) => {
                        let next_unit = Unit::new(func, target.start_location());
                        unit_to_succs
                            .entry(terminator_unit)
                            .or_default()
                            .push(next_unit);
                        unit_to_preds
                            .entry(next_unit)
                            .or_default()
                            .push(terminator_unit);
                    }
                    TerminatorEdges::Double(target, unwind) => {
                        let next_unit1 = Unit::new(func, target.start_location());
                        unit_to_succs
                            .entry(terminator_unit)
                            .or_default()
                            .push(next_unit1);
                        unit_to_preds
                            .entry(next_unit1)
                            .or_default()
                            .push(terminator_unit);
                        let next_unit2 = Unit::new(func, unwind.start_location());
                        unit_to_succs
                            .entry(terminator_unit)
                            .or_default()
                            .push(next_unit2);
                        unit_to_preds
                            .entry(next_unit2)
                            .or_default()
                            .push(terminator_unit);
                        unwind_branches.insert((terminator_unit, next_unit2));
                    }
                    TerminatorEdges::AssignOnReturn {
                        return_, cleanup, ..
                    } => {
                        for target in return_ {
                            let next_unit = Unit::new(func, target.start_location());
                            unit_to_succs
                                .entry(terminator_unit)
                                .or_default()
                                .push(next_unit);
                            unit_to_preds
                                .entry(next_unit)
                                .or_default()
                                .push(terminator_unit);
                        }
                        if let Some(cleanup) = cleanup {
                            let next_unit = Unit::new(func, cleanup.start_location());
                            unit_to_succs
                                .entry(terminator_unit)
                                .or_default()
                                .push(next_unit);
                            unit_to_preds
                                .entry(next_unit)
                                .or_default()
                                .push(terminator_unit);
                            unwind_branches.insert((terminator_unit, next_unit));
                        }
                        if let Some(tk) = tail_kind(kind) {
                            tails.push(terminator_unit);
                            tail_kinds.insert(terminator_unit, tk);
                        }
                    }
                    TerminatorEdges::SwitchInt { targets, discr } => {
                        switches.insert(terminator_unit, SwitchInt::new(discr.clone(), targets.clone()));
                        if let mir::Operand::Copy(place) | mir::Operand::Move(place) = discr {
                            switch_discrs.insert(*place);
                        }
                        for &target in targets.all_targets() {
                            let next_unit = Unit::new(func, target.start_location());
                            unit_to_succs
                                .entry(terminator_unit)
                                .or_default()
                                .push(next_unit);
                            unit_to_preds
                                .entry(next_unit)
                                .or_default()
                                .push(terminator_unit);
                        }
                    }
                }
            }
        }

        if reach_dummy_resume {
            tails.push(dummy_resume_unit);
            tail_kinds.insert(dummy_resume_unit, TailKind::UnwindResume);
        }

        UnitGraph {
            head,
            dummy_resume: dummy_resume_unit,
            tails,
            call_stmts,
            drop_stmts,
            tail_kinds,
            unwind_branches,
            switches,
            switch_discrs,
            unit_to_succs,
            unit_to_preds,
        }
    }

    pub fn get_head(&self) -> Unit<'tcx> {
        self.head
    }

    pub fn get_tails(&self) -> &SmallVec<[Unit<'tcx>; 2]> {
        &self.tails
    }

    pub fn get_dummy_resume(&self) -> Unit<'tcx> {
        self.dummy_resume
    }

    pub fn get_call_stmts(&self) -> &HashSet<Unit<'tcx>> {
        &self.call_stmts
    }

    pub fn get_drop_stmts(&self) -> &HashMap<Unit<'tcx>, mir::Place<'tcx>> {
        &self.drop_stmts
    }

    pub fn is_unwind_branch(&self, from: Unit<'tcx>, to: Unit<'tcx>) -> bool {
        self.unwind_branches.contains(&(from, to))
    }

    pub fn get_tail_kind(&self, n: Unit<'tcx>) -> TailKind {
        self.tail_kinds.get(&n).unwrap().clone()
    }

    pub fn is_conditional_branch_from(&self, n: Unit<'tcx>) -> bool {
        self.switches.contains_key(&n)
    }

    pub fn get_switch_int(&self, n: Unit<'tcx>) -> Option<SwitchInt<'tcx>> {
        self.switches.get(&n).cloned()
    }

    pub fn is_switch_discr(&self, place: &mir::Place<'tcx>) -> bool {
        self.switch_discrs.contains(place)
    }

    pub fn get_succs_of(&self, u: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        if let Some(succs) = self.unit_to_succs.get(&u) {
            succs.clone()
        } else {
            SmallVec::new()
        }
    }

    pub fn get_preds_of(&self, u: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        if let Some(preds) = self.unit_to_preds.get(&u) {
            preds.clone()
        } else {
            SmallVec::new()
        }
    }
}
