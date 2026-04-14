use log::*;
use std::collections::HashSet;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::points_of_aliasing;
use crate::infoflow::{aliasing, Unit};

use super::POAKind;

/// Helps process the return points-of-aliasing in forward analysis.
pub fn process_forward_return_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    outcoming: AccessPath<'tcx>,
    callsite: Unit<'tcx>,
    _return_site: Unit<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let poa = POAKind::new_forward_return_poa(callsite, outcoming);
    if let Some(poa_results) = acx.poa_cache.get_poa_results(&poa) {
        return poa_results;
    }
    
    trace!("Process forward return poa for {:?} at {:?}", outcoming, callsite);
    let (destination, is_projection_of_destination) = if callsite.is_drop_stmt(acx.tcx) {
        (None, false)
    } else {
        let destination = callsite.call_destination(acx.tcx);
        (Some(destination), outcoming.is_projection_of(acx, &destination))
    };
    let res = if is_projection_of_destination {
        let mut set = HashSet::new();
        set.insert(outcoming);

        // The destination may have its address taken, thus there may be pointers
        // that point to it at return site, although it definitely violates
        // Rust's aliasing XOR mutability rules.
        let dest_aliases = points_of_aliasing::address_taken::process_address_taken_poa(
            acx,
            &AccessPath::from_rustc_place(acx, callsite.func, &destination.unwrap()),
            callsite,
        );
        let proj = outcoming.access_elems;
        set.extend(
            dest_aliases
                .iter()
                .map(|alias| alias.project_deeper(acx, proj)),
        );
        set
    } else {
        // A projection from an argument
        assert!(outcoming.is_indirect());
        // let arg_path =
        //     AccessPath::from_rustc_place(acx, callsite.func, &Place::from(outcoming.local));
        let (arg_path, proj) = outcoming.deref_base_and_proj().unwrap();
        let query = Query::new(arg_path, callsite);
        let arg_aliases = aliasing::find_aliases(acx, query);
        if !acx.is_query_finished(&query) {
            warn!("Query {:?} is not finished", query);
        }
        // let proj = outcoming.access_elems;
        points_of_aliasing::find_aliases_recursively(acx, callsite, arg_aliases, proj)
    };
    
    trace!("Results of forward return poa for {:?}: {:?}", outcoming, res);
    acx.poa_cache.add_poa_results(poa, res.clone());
    res
}
