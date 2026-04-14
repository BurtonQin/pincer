// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

use log::*;
use std::cell::{Ref, RefCell};
use std::collections::{HashMap, HashSet};
use std::rc::Rc;
use rustc_hir::def::DefKind;
use rustc_hir::def_id::{DefId, DefIndex};
use rustc_middle::ty::{Ty, TyCtxt};
use rustc_session::config::CrateType;

use crate::infoflow::aliasing::query::{Query, QueryCache};
use crate::infoflow::cfg::backward_infoflow_cfg::BackwardInfoflowCFG;
use crate::infoflow::cfg::block_cfg::BasicBlockCFG;
use crate::infoflow::cfg::cfg_factory::CFGFactory;
use crate::infoflow::cfg::infoflow_cfg::InfoflowCFG;
use crate::infoflow::cfg::CFGConfig;
use crate::infoflow::data::access_elem::{AccessElem, AccessElems};
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::ifds::summaries::Summaries;
use crate::infoflow::{CallGraph, PointerFlowOrigin};
use crate::infoflow::points_of_aliasing::POACache;
use crate::mir::drop_shim::DropShims;
use crate::mir::function::FuncDef;
use crate::mir::known_names::{KnownNames, KnownNamesCache};
use crate::mir::projection::{
    PlaceElemsAndTy, ZeroByteOffsetProjectionsCache, ProjectionIdx, 
    ProjectionIndexer
};
use crate::mir::reference_set::ReferenceSet; 
use crate::mir::projection::PlaceElems;
use crate::mir::unit::Unit;
use crate::util::{self, interners::SliceInterner, options::AnalysisOptions};

/// Global information of the analysis
pub struct AnalysisContext<'tcx> {
    /// The central data structure of the compiler.
    pub(crate) tcx: TyCtxt<'tcx>,

    pub(crate) analysis_options: AnalysisOptions,

    pub(crate) entry_funcs: HashSet<DefId>,

    pub(crate) call_graph: Option<Rc<CallGraph<'tcx>>>,

    pub(crate) drop_shims: Rc<DropShims<'tcx>>,

    pub(crate) cfg_factory: Option<CFGFactory<'tcx>>,

    pub(crate) known_names_cache: KnownNamesCache,

    pub(crate) reference_set: RefCell<ReferenceSet<'tcx>>,

    pub(crate) zero_byte_offset_projs_cache: ZeroByteOffsetProjectionsCache<'tcx>,

    pub(crate) projection_indexer: ProjectionIndexer<'tcx>,

    pub(crate) access_elems_interner: SliceInterner<'tcx, AccessElem>,

    pub(crate) units_interner: SliceInterner<'tcx, Unit<'tcx>>,

    pub(crate) query_cache: QueryCache<'tcx>,

    pub(crate) poa_cache: POACache<'tcx>,

    pub(crate) may_unwind_resume: RefCell<HashMap<FuncDef<'tcx>, bool>>,

    pub(crate) dropped_access_paths: RefCell<HashSet<AccessPath<'tcx>>>,

    pub(crate) bw_summaries: Rc<RefCell<Summaries<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>>>,

    pub(crate) fw_summaries: Rc<RefCell<Summaries<Unit<'tcx>, AccessPath<'tcx>, FuncDef<'tcx>>>>,
}

impl<'tcx> AnalysisContext<'tcx> {
    pub fn new(tcx: TyCtxt<'tcx>, analysis_options: AnalysisOptions) -> Option<Self> {
        info!("Initializing AnalysisContext");
        let mut entry_funcs = HashSet::<DefId>::new();

        // Find the DefId for the entry function
        if let Some(ref entry_func) = analysis_options.entry_func {
            for local_def_id in tcx.hir().body_owners() {
                let def_kind = tcx.def_kind(local_def_id);
                if def_kind == DefKind::Fn || def_kind == DefKind::AssocFn {
                    let item_name = tcx.item_name(local_def_id.to_def_id());
                    if item_name.to_string() == *entry_func {
                        entry_funcs.insert(local_def_id.to_def_id());
                    }
                }
            }
        } else {
            // If no entry point specified, use the default logic to select entries
            if matches!(tcx.crate_types()[0], CrateType::Executable) {
                let entry_fn_def_id = if let Some((def_id, _)) = tcx.entry_fn(()) {
                    def_id
                } else {
                    DefId::local(DefIndex::from_u32(0))
                };
                entry_funcs.insert(entry_fn_def_id);
            } else {
                // Add all public functions as entry functions for a library crate
                for local_def_id in tcx.hir().body_owners() {
                    let def_id = local_def_id.to_def_id();
                    if !matches!(tcx.def_kind(def_id), DefKind::Fn | DefKind::AssocFn) {
                        continue;
                    }

                    if !util::is_public(def_id, tcx) {
                        // skipping functions not public
                        continue;
                    } 
                    if analysis_options.skip_generics
                        && tcx.generics_of(def_id).requires_monomorphization(tcx)
                    {
                        // skipping generic functions
                        continue;
                    } 
                    if tcx.is_const_fn_raw(def_id) {
                        // skipping constant functions
                        continue;
                    } 
                    if util::is_higher_order_function(def_id, tcx) {
                        //skipping higher order functions
                        continue;
                    } 
                    
                    entry_funcs.insert(def_id);
                }
            }
        }

        if !entry_funcs.is_empty() {
            Some(Self {
                tcx,
                analysis_options,
                entry_funcs,
                call_graph: None,
                drop_shims: Rc::new(DropShims::new()),
                cfg_factory: None,
                known_names_cache: KnownNamesCache::create_cache_from_language_items(),
                reference_set: RefCell::new(ReferenceSet::new()),
                zero_byte_offset_projs_cache: ZeroByteOffsetProjectionsCache::new(),
                projection_indexer: ProjectionIndexer::new(),
                access_elems_interner: SliceInterner::new(),
                units_interner: SliceInterner::new(),
                query_cache: QueryCache::new(),
                poa_cache: POACache::new(),
                may_unwind_resume: RefCell::new(HashMap::new()),
                dropped_access_paths: RefCell::new(HashSet::new()),
                bw_summaries: Rc::new(RefCell::new(Summaries::new())),
                fw_summaries: Rc::new(RefCell::new(Summaries::new())),
            })
        } else {
            error!("Entry point not found");
            None
        }
    }

    pub fn tcx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    pub fn set_up(&mut self, call_graph: CallGraph<'tcx>) {
        self.call_graph = Some(Rc::new(call_graph));
        self.cfg_factory = Some(CFGFactory::new(
            self.tcx,
            self.call_graph.as_ref().unwrap().clone(),
            self.drop_shims.clone(),
        ));
    }

    pub fn get_call_graph(&self) -> Rc<CallGraph<'tcx>> {
        self.call_graph
            .as_ref()
            .expect("Set call graph first")
            .clone()
    }

    /// Get the drop shim body, using the cache if available.
    pub fn drop_shim_body(&self, func_def: FuncDef<'tcx>) -> &'tcx rustc_middle::mir::Body<'tcx> {
        self.drop_shims.body(self.tcx, func_def)
    }

    fn cfg_factory(&self) -> &CFGFactory<'tcx> {
        self.cfg_factory.as_ref().expect("Set call graph first")
    }

    pub fn get_fw_icfg(&self, config: CFGConfig) -> &InfoflowCFG<'tcx> {
        self.cfg_factory().get_fw_icfg(config)
    }

    pub fn get_bw_icfg(&self, config: CFGConfig) -> &BackwardInfoflowCFG<'tcx> {
        self.cfg_factory().get_bw_icfg(config)
    }

    pub fn get_bb_cfg(&self, config: CFGConfig) -> &BasicBlockCFG<'tcx> {
        self.cfg_factory().get_bb_cfg(config)
    }

    pub fn get_known_name_for(&self, def_id: DefId) -> KnownNames {
        self.known_names_cache.get(self.tcx, def_id)
    }

    pub fn get_zero_byte_offset_projections(&self, ty: Ty<'tcx>) -> &'tcx [PlaceElemsAndTy<'tcx>] {
        self.zero_byte_offset_projs_cache
            .get_zero_byte_offset_projections(self.tcx, ty)
    }

    pub fn get_projection_idx(
        &self,
        base_ty: Ty<'tcx>,
        projection: PlaceElems<'tcx>,
    ) -> Option<ProjectionIdx> {
        self.projection_indexer
            .get_projection_idx(self.tcx, base_ty, projection)
    }

    pub fn get_possible_types_of_projection(
        &self,
        base_ty: Ty<'tcx>,
        projection_idx: ProjectionIdx,
    ) -> Option<HashSet<Ty<'tcx>>> {
        self.projection_indexer
            .get_possible_types_of_projection(self.tcx, base_ty, projection_idx)
    }

    pub fn max_projection_idx_of_type(&self, base_ty: Ty<'tcx>) -> ProjectionIdx {
        self.projection_indexer
            .max_projection_idx_of_type(self.tcx, base_ty)
    }

    pub fn is_std_ops_fntrait_call(&self, def_id: DefId) -> bool {
        let known_name = self.get_known_name_for(def_id);
        match known_name {
            KnownNames::StdOpsFunctionFnCall
            | KnownNames::StdOpsFunctionFnMutCallMut
            | KnownNames::StdOpsFunctionFnOnceCallOnce => true,
            _ => false,
        }
    }

    pub fn call_may_unwind(&self, callsite: &Unit<'tcx>) -> bool {
        util::call_may_unwind(self, callsite)
    }

    pub fn may_unwind_resume(&self, func_def: FuncDef<'tcx>) -> bool {
        util::may_unwind_resume(self, func_def)
    }

    pub fn def_in_ops_func_namespace(&self, def_id: DefId) -> bool {
        let known_name = self.get_known_name_for(def_id);
        match known_name {
            KnownNames::StdOpsFunctionImpls
            | KnownNames::StdOpsFunctionFnCall
            | KnownNames::StdOpsFunctionFnMutCallMut
            | KnownNames::StdOpsFunctionFnOnceCallOnce => true,
            _ => false,
        }
    }

    pub fn mk_access_elems(&self, access_elems: &[AccessElem]) -> AccessElems<'tcx> {
        // Normalize the access_elems by removing AggTyElem(0) elems
        let normalized_elems = access_elems
            .iter()
            .filter(|&&elem| elem != AccessElem::AggTyProj(ProjectionIdx::from_usize(0)))
            .cloned()
            .collect::<Vec<AccessElem>>();
        self.access_elems_interner
            .intern(self.tcx, &normalized_elems)
    }

    pub fn concat_access_elems(
        &self,
        first_elems: &[AccessElem],
        second_elems: &[AccessElem],
    ) -> AccessElems<'tcx> {
        let mut elems = Vec::with_capacity(first_elems.len() + second_elems.len());
        elems.extend_from_slice(first_elems);
        elems.extend_from_slice(second_elems);
        self.mk_access_elems(&elems)
    }

    pub fn empty_access_elems(&self) -> AccessElems<'tcx> {
        self.access_elems_interner.intern(self.tcx, &[])
    }

    pub fn mk_units(&self, units: &[Unit<'tcx>]) -> &'tcx [Unit<'tcx>] {
        self.units_interner.intern(self.tcx, units)
    }

    pub fn append_unit(&self, units: &[Unit<'tcx>], unit: Unit<'tcx>) -> &'tcx [Unit<'tcx>] {
        let mut units = units.to_vec();
        units.push(unit);
        self.mk_units(&units)
    }

    pub fn has_processed_query(&self, query: &Query<'tcx>) -> bool {
        self.query_cache.has_query(query)
    }

    pub fn is_query_finished(&self, query: &Query<'tcx>) -> bool {
        self.query_cache.is_query_finished(query)
    }

    pub fn get_flow_origins(&self, query: &Query<'tcx>) -> HashSet<PointerFlowOrigin<'tcx>> {
        self.query_cache.get_flow_origins(query)
    }

    pub fn get_aliases(&self, query: &Query<'tcx>) -> HashSet<AccessPath<'tcx>> {
        self.query_cache.get_aliases(query)
    }

    pub fn analysis_options(&self) -> &AnalysisOptions {
        &self.analysis_options
    }

    pub fn analysis_options_mut(&mut self) -> &mut AnalysisOptions {
        &mut self.analysis_options
    }

    pub fn add_dropped_access_path(&self, access_path: AccessPath<'tcx>) {
        self.dropped_access_paths.borrow_mut().insert(access_path);
    }

    pub fn get_dropped_access_paths(&self) -> Ref<HashSet<AccessPath<'tcx>>> {
        self.dropped_access_paths.borrow()
    }
}
