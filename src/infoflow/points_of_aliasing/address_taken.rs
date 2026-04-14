use log::*;
use std::collections::HashSet;

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_elem::AccessElem;
use crate::infoflow::data::access_path::AccessPath;
use crate::infoflow::forward::forward_solver::ForwardSolver;
use crate::infoflow::get_lplace_of_assignment;
use crate::infoflow::points_of_aliasing::POAKind;
use crate::infoflow::Unit;

/// Helps process the address taken points-of-aliasing.
///
/// A newly discovered fact may either have its address taken or have a prefix whose address was taken.  
/// This implies that the fact can be indirectly accessed through other references at this point.
///
/// ### Example:
/// Suppose we are searching for aliases of `q` in the following code:
///
/// `
/// let mut foo = Foo { f: &a };
/// let p = &mut foo;
/// (*p).f = &b;
/// let q = foo.f;
/// `
///
/// Here, `q` is assigned from `foo.f`. Since `foo` had its address taken and was assigned to `p`,
/// `foo.f` can also be accessed through `(*p).f`. Thus, when analyzing `foo.f`, we must also
/// consider `(*p).f` to capture all potential aliases, such as `&b` for `q`.
///
/// Given a data fact, e.g. `foo.f` at a certain statement, this function returns the set of facts
/// that can be used to access `foo.f` indirectly, e.g. `(*p).f`
pub fn process_address_taken_poa<'tcx>(
    acx: &AnalysisContext<'tcx>,
    fact: &AccessPath<'tcx>,
    curr_unit: Unit<'tcx>,
) -> HashSet<AccessPath<'tcx>> {
    let poa = POAKind::new_address_taken_poa(curr_unit, fact.clone());
    if let Some(poa_results) = acx.poa_cache.get_poa_results(&poa) {
        return poa_results;
    }
    trace!("Processing address taken POA for {:?} at {:?}", fact, curr_unit);
    let prefixes = fact.get_address_taken_prefixes(acx);
    let curr_func = curr_unit.func;
    let mut set = HashSet::new();
    for (prefix, ref_locs) in prefixes {
        let mut proj_after_prefix = fact.projection_after_base(acx, &prefix).unwrap();
        proj_after_prefix = acx.concat_access_elems(&[AccessElem::Deref], proj_after_prefix);
        for ref_loc in ref_locs {
            let ref_unit = Unit::new(curr_func, ref_loc);
            let ref_place =
                get_lplace_of_assignment(acx.tcx, ref_unit).unwrap();

            if ref_unit == curr_unit {
                continue;
            }

            let body = acx.tcx.optimized_mir(curr_unit.func.def_id);
            if !ref_unit.is_predecessor_of(&curr_unit, body) {
                continue;
            }

            // Start a forward analysis to search for aliases of lplace from the address taken unit to
            // the current unit.

            // todo
            // We currently consider that lplace is not a indirect place, so we can start the forward
            // analysis directly.
            // However, if lplace is an indirect place, like `(*p).f`, we need to search the aliases for
            // `p` first

            let mut forward_solver = ForwardSolver::new(acx);
            let src = AccessPath::from_rustc_place(acx, curr_func, ref_place);
            forward_solver.start_propagation_between_units(src, ref_unit, curr_unit, true);
            if let Some(path_edges) = forward_solver.path_edges_at_stmt(curr_unit) {
                for path_edge in path_edges {
                    // The start and dsource should be `ref_loc` and `prefix` respectively.
                    // The dtarget should be the aliases of `prefix` at the target unit.
                    let target = path_edge
                        .fact_at_target()
                        .project_deeper(acx, &proj_after_prefix);
                    set.insert(target);
                }
            }
        }
    }
    trace!("Results of address taken POA for {:?}: {:?}", fact, set);
    acx.poa_cache.add_poa_results(poa, set.clone());
    set
}
