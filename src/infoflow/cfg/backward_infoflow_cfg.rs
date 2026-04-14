use rustc_middle::ty::TyCtxt;
use smallvec::SmallVec;
use std::rc::Rc;

use crate::infoflow::cfg::CFGConfig;
use crate::infoflow::cfg::TailKind;
use crate::infoflow::cfg::infoflow_cfg::InfoflowCFG;
use crate::infoflow::cfg::interprocedural_cfg::InterproceduralCFG;
use crate::infoflow::{CallGraph, Unit};
use crate::mir::drop_shim::DropShims;
use crate::mir::function::FuncDef;

pub struct BackwardInfoflowCFG<'tcx> {
    delegate: InfoflowCFG<'tcx>,
}

impl<'tcx> BackwardInfoflowCFG<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        call_graph: Rc<CallGraph<'tcx>>,
        drop_shims: Rc<DropShims<'tcx>>,
        config: CFGConfig,
    ) -> BackwardInfoflowCFG<'tcx> {
        BackwardInfoflowCFG {
            delegate: InfoflowCFG::new_with_dummy_head(tcx, call_graph, drop_shims, config),
        }
    }
}

impl<'tcx> InterproceduralCFG<Unit<'tcx>, FuncDef<'tcx>> for BackwardInfoflowCFG<'tcx> {
    fn get_function_of(&self, n: Unit<'tcx>) -> FuncDef<'tcx> {
        self.delegate.get_function_of(n)
    }

    fn get_preds_of(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_succs_of(n)
    }

    fn get_succs_of(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_preds_of(n)
    }

    fn get_callees_of_call_at(&self, n: Unit<'tcx>) -> SmallVec<[FuncDef<'tcx>; 1]> {
        self.delegate.get_callees_of_call_at(n)
    }

    fn get_callers_of(&self, f: FuncDef<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_callers_of(f)
    }

    fn get_start_points_of(&self, f: FuncDef<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_end_points_of(f)
    }

    fn get_end_points_of(&self, f: FuncDef<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_start_points_of(f)
    }

    fn get_return_sites_of_call_at(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_preds_of_call_at(n)
    }

    fn get_preds_of_call_at(&self, n: Unit<'tcx>) -> SmallVec<[Unit<'tcx>; 2]> {
        self.delegate.get_succs_of(n)
    }

    fn is_call_node(&self, n: Unit<'tcx>) -> bool {
        self.delegate.is_call_node(n)
    }

    fn is_exit_node(&self, n: Unit<'tcx>) -> bool {
        self.delegate.is_start_point(n)
    }

    fn is_start_point(&self, n: Unit<'tcx>) -> bool {
        self.delegate.is_exit_node(n)
    }

    fn is_feasible_interprocedural_flow(
        &self,
        _call_site: Unit<'tcx>,
        _source: Unit<'tcx>,
        target: Unit<'tcx>,
    ) -> bool {
        if self.is_start_point(target) {
            // Backward process_call: source=call_site, target=forward exit (backward start point).
            // Ideally we'd check whether the specific return site that brought flow to the
            // call node is compatible with this exit's TailKind (e.g., only enter through an
            // UnwindResume exit if flow arrived from the unwind return site). However,
            // process_call's inc_edge only carries the call node — the originating return site
            // is lost. So we can only filter exits that are unconditionally infeasible.
            let tail_kind = self.delegate.with_unit_graph(target.func, |ug| ug.get_tail_kind(target));
            match tail_kind {
                TailKind::UnwindTerminate => false,
                TailKind::Unreachable => {
                    self.delegate.get_end_points_of(target.func).len() <= 1
                }
                _ => true,
            }
        } else {
            true
        }
    }
}
