use std::collections::HashMap;
use multimap::MultiMap;

use rustc_hir::def_id::DefId;
use rustc_middle::mir;
use rustc_middle::mir::{Location, Place};
use rustc_middle::ty::TyCtxt;

use crate::mir::place_ext::PlaceExt;

/// Set of Ref and RawPtr rvalues in each function.
pub struct ReferenceSet<'tcx> {
    pub(crate) func_to_ref_set: HashMap<DefId, PerFunctionReferenceSet<'tcx>>,
}

pub struct PerFunctionReferenceSet<'tcx> {
    pub location_map: MultiMap<Place<'tcx>, Location>,
}

impl<'tcx> ReferenceSet<'tcx> {
    pub fn new() -> Self {
        ReferenceSet {
            func_to_ref_set: HashMap::new(),
        }
    }
    
    pub fn get_ref_locations(&mut self, def_id: DefId, tcx: TyCtxt<'tcx>) -> &PerFunctionReferenceSet<'tcx> {
        self.func_to_ref_set.entry(def_id).or_insert_with(|| {
            if tcx.is_mir_available(def_id) {
                PerFunctionReferenceSet::visit_body(tcx, def_id)
            } else {
                PerFunctionReferenceSet::new()
            }
        })
    }

    pub fn get_ref_locations_of_place(
        &self,
        def_id: DefId,
        place: Place<'tcx>,
    ) -> Option<&Vec<Location>> {
        self.func_to_ref_set
            .get(&def_id)
            .and_then(|per_func_ref_set| per_func_ref_set.get_ref_locations(place))
            .map(|locations| locations)
    }

    pub fn get_ref_locations_by<P>(
        &self,
        def_id: DefId,
        predicate: P
    ) -> Option<Vec<(Place<'tcx>, Location)>>
    where
        P: Fn(&Place<'tcx>) -> bool
    {
        self.func_to_ref_set
            .get(&def_id)
            .map(|per_func_ref_set| per_func_ref_set.get_ref_locations_by(predicate))
    }
}

impl<'tcx> PerFunctionReferenceSet<'tcx> {
    pub fn new() -> Self {
        PerFunctionReferenceSet {
            location_map: MultiMap::new(),
        }
    }

    pub fn visit_body(tcx: TyCtxt<'tcx>, def_id: DefId) -> Self {
        let mut per_func_ref_set = PerFunctionReferenceSet::new();
        let mir = tcx.optimized_mir(def_id);
        for bb in mir.basic_blocks.indices() {
            let data = &mir[bb];
            let mut location = bb.start_location();
            while location.statement_index < data.statements.len() {
                let stmt = &data.statements[location.statement_index];
                match &stmt.kind {
                    mir::StatementKind::Assign(box (_place, rvalue)) => {
                        match rvalue {
                            mir::Rvalue::Ref(_, _, place) | mir::Rvalue::RawPtr(_, place) => {
                                let place = place.expand_box_deref(tcx, def_id);
                                // Ignore statements like `let _ = &(*x);`
                                if !place.is_indirect() || place.projection.len() > 1 {
                                    per_func_ref_set.add_ref(place, location);
                                }
                            }
                            _ => {}
                        }
                    }
                    _ => {}
                }
                location.statement_index += 1;
            }
        }
        per_func_ref_set
    }

    pub fn add_ref(&mut self, place: Place<'tcx>, location: Location) {
        self.location_map.insert(place, location);
    }

    pub fn get_ref_locations(&self, place: Place<'tcx>) -> Option<&Vec<Location>> {
        self.location_map.get_vec(&place)
    }

    pub fn get_ref_locations_by<P>(&self, predicate: P) -> Vec<(Place<'tcx>, Location)> 
    where
        P: Fn(&Place<'tcx>) -> bool
    {
        self.location_map
            .iter()
            .filter(|(place, _)| predicate(place))
            .map(|(place, location)| (place.clone(), location.clone()))
            .collect()
    }
}
