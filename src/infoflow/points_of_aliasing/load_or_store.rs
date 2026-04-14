use log::*;
use std::collections::HashSet;
use rustc_middle::mir::Place;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::points_of_aliasing::{self, POAKind};
use crate::infoflow::{aliasing, Unit};

/// Helps process the load and store points-of-aliasing.
///
/// During forward analysis, when encountering a store statement `(*p).f = q`,
/// or during backward analysis, when encountering a load statement `q = (*p).f`,
/// we need to instantiate a new subquery to track the aliases of `p`.
///
/// If `r` is an alias of `p`, we must include `(*r).f` in our forward/backward analysis.
///
/// This function processes such cases by computing the aliases of `p` given a data fact
/// (e.g., `(*p).f` at a particular statement) and returns the set of aliases,
/// each appended with the dereference and the field `f`.
pub fn process_load_or_store_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    fact: &AccessPath<'tcx>,
    curr_unit: Unit<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    assert!(fact.access_elems.len() >= 1 && fact.access_elems[0].is_deref());
    let poa = POAKind::new_load_or_store_poa(curr_unit, fact.clone());
    if let Some(poa_results) = acx.poa_cache.get_poa_results(&poa) {
        return poa_results;
    }

    trace!("Process load or store poa for {:?} at {:?}", fact, curr_unit);
    let mut set = HashSet::new();

    // Start a backward analysis to search the aliases of the base place
    let base_place = Place::from(fact.local);
    let proj_after_base = fact.projection_after_base(acx, &base_place).unwrap();

    let query = Query::new(
        AccessPath::from_rustc_place(acx, curr_unit.func, &base_place),
        curr_unit,
    );

    // Suppose that the base place `p` has an alias `q`, and `q` had its
    // address taken: `let r = &q`. Then `*r` should be included in the aliases
    // set computed by calling `find_aliases`.
    let aliases = aliasing::find_aliases(acx, query);

    // To construct the target access paths, we append `proj_after_base` to each
    // alias. We must account for cases where a target place, such as `(*q).f`
    // also has its address taken
    // TODO: invoking `process_address_taken_poa` here would lead to some
    // unnecessary address taken infoflow. For example, given a target place
    // `(*q).f`, where `q` had its address taken: `let r = &q`, we do not need
    // to analyze it again since (*r) should have been included in the aliases.
    for alias in aliases {
        let target = alias.project_deeper(acx, proj_after_base);
        set.insert(target);

        set.extend(
            points_of_aliasing::address_taken::process_address_taken_poa(acx, &target, curr_unit),
        );
    }

    trace!("Results of load or store poa for {:?}: {:?}", fact, set);
    acx.poa_cache.add_poa_results(poa, set.clone());
    set
}
