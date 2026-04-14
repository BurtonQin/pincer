use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use rustc_middle::ty::TyCtxt;

use crate::infoflow::cfg::CFGConfig;
use crate::infoflow::cfg::backward_infoflow_cfg::BackwardInfoflowCFG;
use crate::infoflow::cfg::block_cfg::BasicBlockCFG;
use crate::infoflow::cfg::infoflow_cfg::InfoflowCFG;
use crate::infoflow::CallGraph;
use crate::mir::drop_shim::DropShims;

/// Unified factory that creates and caches all three CFG types keyed by `CFGConfig`.
/// The same config always returns the same reference (singleton per config per type).
pub(crate) struct CFGFactory<'tcx> {
    tcx: TyCtxt<'tcx>,
    call_graph: Rc<CallGraph<'tcx>>,
    drop_shims: Rc<DropShims<'tcx>>,
    fw_cache: RefCell<HashMap<CFGConfig, Box<InfoflowCFG<'tcx>>>>,
    bw_cache: RefCell<HashMap<CFGConfig, Box<BackwardInfoflowCFG<'tcx>>>>,
    bb_cache: RefCell<HashMap<CFGConfig, Box<BasicBlockCFG<'tcx>>>>,
}

impl<'tcx> CFGFactory<'tcx> {
    pub fn new(
        tcx: TyCtxt<'tcx>,
        call_graph: Rc<CallGraph<'tcx>>,
        drop_shims: Rc<DropShims<'tcx>>,
    ) -> Self {
        CFGFactory {
            tcx,
            call_graph,
            drop_shims,
            fw_cache: RefCell::new(HashMap::new()),
            bw_cache: RefCell::new(HashMap::new()),
            bb_cache: RefCell::new(HashMap::new()),
        }
    }

    /// Returns the `InfoflowCFG` for `config`, creating it on first request.
    pub fn get_fw_icfg(&self, config: CFGConfig) -> &InfoflowCFG<'tcx> {
        let mut cache = self.fw_cache.borrow_mut();
        if !cache.contains_key(&config) {
            let cfg = Box::new(InfoflowCFG::new(
                self.tcx,
                Rc::clone(&self.call_graph),
                Rc::clone(&self.drop_shims),
                config.clone(),
            ));
            cache.insert(config.clone(), cfg);
        }
        // SAFETY: `Box<InfoflowCFG>` heap-allocates the CFG; HashMap reallocation moves
        // the Box (a pointer) but not the InfoflowCFG data. Entries are never removed,
        // so the data lives as long as `self`. The returned reference borrows `&self`.
        let ptr: *const InfoflowCFG<'tcx> = &**cache.get(&config).unwrap();
        drop(cache);
        unsafe { &*ptr }
    }

    /// Returns the `BackwardInfoflowCFG` for `config`, creating it on first request.
    pub fn get_bw_icfg(&self, config: CFGConfig) -> &BackwardInfoflowCFG<'tcx> {
        let mut cache = self.bw_cache.borrow_mut();
        if !cache.contains_key(&config) {
            let cfg = Box::new(BackwardInfoflowCFG::new(
                self.tcx,
                Rc::clone(&self.call_graph),
                Rc::clone(&self.drop_shims),
                config.clone(),
            ));
            cache.insert(config.clone(), cfg);
        }
        // SAFETY: same reasoning as `get_fw_icfg`.
        let ptr: *const BackwardInfoflowCFG<'tcx> = &**cache.get(&config).unwrap();
        drop(cache);
        unsafe { &*ptr }
    }

    /// Returns the `BasicBlockCFG` for `config`, creating it on first request.
    pub fn get_bb_cfg(&self, config: CFGConfig) -> &BasicBlockCFG<'tcx> {
        let mut cache = self.bb_cache.borrow_mut();
        if !cache.contains_key(&config) {
            let cfg = Box::new(BasicBlockCFG::new(
                self.tcx,
                Rc::clone(&self.call_graph),
                Rc::clone(&self.drop_shims),
                config.clone(),
            ));
            cache.insert(config.clone(), cfg);
        }
        // SAFETY: same reasoning as `get_fw_icfg`.
        let ptr: *const BasicBlockCFG<'tcx> = &**cache.get(&config).unwrap();
        drop(cache);
        unsafe { &*ptr }
    }
}
