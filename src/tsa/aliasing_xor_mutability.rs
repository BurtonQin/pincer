use std::collections::{HashMap, HashSet, VecDeque};

use rustc_hir::def_id::DefId;
use rustc_middle::ty::{ClauseKind, Mutability, Region, Ty, TyCtxt, TyKind};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::data::access_elem::{
    try_to_eval_possible_pointer_types, AccessElem, AccessElems,
};
use crate::infoflow::data::access_path::AccessPath;

/// Determine if the data flow is compliant with the Aliasing-XOR-Mutability enforcement.
/// TODO: Handle a special case where the initial_param_path is a indirect pointer, like `(*_1).f`, and this path is
/// later killed by rewriting a value to the base pointer `_1`. In this case, the initial path is not killed in the callers.
pub fn is_axm_compliant<'tcx>(
    acx: &AnalysisContext<'tcx>,
    source_path: AccessPath<'tcx>,
    result_aliases: &HashSet<AccessPath<'tcx>>,
) -> bool {
    if result_aliases.len() <= 1 {
        return true;
    }

    let func = source_path.func_def;

    if acx.tcx.is_closure_like(func.def_id) {
        return false;
    }
    
    let ret_ty = acx
        .tcx
        .fn_sig(func.def_id)
        .skip_binder()
        .skip_binder()
        .output();
    let arg_tys = acx
        .tcx
        .fn_sig(func.def_id)
        .skip_binder()
        .skip_binder()
        .inputs();

    let aliases_tys = result_aliases
        .iter()
        .map(|alias| {
            if alias.local.index() == 0 {
                let alias_ty =
                    try_to_eval_possible_pointer_types(acx, ret_ty, alias.access_elems());
                (*alias, alias_ty)
            } else {
                let arg_type = arg_tys[alias.local.index() - 1];
                let alias_ty =
                    try_to_eval_possible_pointer_types(acx, arg_type, alias.access_elems());
                (*alias, alias_ty)
            }
        })
        .collect::<HashMap<_, _>>();

    // return false if there are new raw pointers or pointers with unknown type
    if aliases_tys.iter().any(|(alias, tys)| {
        *alias != source_path 
            && (tys.is_none()
                || tys.as_ref().unwrap().is_empty()
                || tys.as_ref().unwrap().iter().any(|ty| ty.is_raw_ptr()))
    }) {
        return false;
    }

    let source_arg_ty = arg_tys[source_path.local.index() - 1];
    let source_tys =
        try_to_eval_possible_pointer_types(acx, source_arg_ty, source_path.access_elems());

    if source_tys.is_none() {
        return false;
    }

    let source_tys = source_tys.unwrap();
    if source_tys.is_empty() {
        return false;
    }
    // If the source path is a direct raw pointer, like _1: *const T, we consider the data flow
    // as axm-non-compliant if it has any new alias
    if !source_path.is_indirect() && source_tys.iter().any(|ty| ty.is_raw_ptr()) {
        if result_aliases
            .iter()
            .filter(|alias| **alias != source_path)
            .count()
            > 0
        {
            return false;
        }
    }

    return check_aliasing_xor_mutability(acx, source_path, source_arg_ty, &aliases_tys);
}

/// All aliase should be mutable/shared references.
pub fn check_aliasing_xor_mutability<'tcx>(
    acx: &AnalysisContext<'tcx>,
    source_path: AccessPath<'tcx>,
    source_base_ty: Ty<'tcx>,
    aliases_tys: &HashMap<AccessPath<'tcx>, Option<HashSet<Ty<'tcx>>>>,
) -> bool {
    let has_mutable_reference = aliases_tys.iter().any(|(alias, tys)| {
        if *alias == source_path {
            return false;
        }
        if let Some(tys) = tys {
            return tys.iter().any(|ty| ty.is_mutable_ptr());
        }
        false
    });
    // There are more than one references aliasing with the source path and at least one of them is a mutable reference
    if has_mutable_reference
        && aliases_tys
            .iter()
            .filter(|(alias, _)| **alias != source_path)
            .count()
            > 1
    {
        return false;
    }

    let outlive_predicates = region_outlives_predicates(acx.tcx, source_path.func_def.def_id);
    let implicit_outlive_relations =
        region_outlives_relations_in_path(acx, source_base_ty, source_path.access_elems());

    // If the source path is a shared borrow, the new aliases should not outlive the shared borrow region.
    // For example, if the source path is `(*(*(*_1).f).g).h` where `*(*_1).f).g` is an immutable borrow with lifetime `'a`,
    // even if the source path itself is a mutable reference, it is still a shared borrow.
    // It is safe to create multiple new aliases that are shared borrows with lifetimes no longer than `a`.
    // Othereise, if the source is a mutable borrow, the new aliases should not outlive the source's mutable borrow region,
    // as the new aliases are treated as reborrows of the source.
    // For example, if the source path is `(*(*(*_1).f).g).h`, the source path itself, along with `(*_1).f` and `*(*_1).f).g`
    // are all mutable references, the new aliases, not matter mutable or immutable, should not outlive the source's
    // mutable borrow region.
    let safe_borrow_region: Region<'tcx> = if let Some(region) =
        max_immutable_borrow_region(acx, source_base_ty, source_path.access_elems())
    {
        region
    } else {
        if let Some(region) = reference_region(source_base_ty) {
            region
        } else {
            // If the source argument is a raw pointer, we consider the data flow as axm-non-compliant
            return false;
        }
    };
    let mut outlived_by_safe_borrow_region: HashSet<_> =
        regions_outlived_by(&outlive_predicates, safe_borrow_region);
    outlived_by_safe_borrow_region.extend(regions_outlived_by(
        &implicit_outlive_relations,
        safe_borrow_region,
    ));
    for (alias, alias_tys) in aliases_tys {
        if *alias == source_path {
            continue;
        }
        for ty in alias_tys.as_ref().unwrap() {
            let borrow_region = reference_region(*ty).unwrap();
            if !outlived_by_safe_borrow_region.contains(&borrow_region) {
                return false;
            }
        }
    }
    return true;
}

pub fn regions_outlived_by<'tcx>(
    outlive_relations: &HashSet<(Region<'tcx>, Region<'tcx>)>,
    region: Region<'tcx>,
) -> HashSet<Region<'tcx>> {
    let mut result = HashSet::new();
    result.insert(region);
    let mut rev_outlives_map: HashMap<Region<'tcx>, Vec<Region<'tcx>>> = HashMap::new();
    for (r1, r2) in outlive_relations {
        rev_outlives_map.entry(*r1).or_insert(vec![]).push(*r2);
    }
    let mut queue = VecDeque::new();
    queue.push_back(region);
    while let Some(curr) = queue.pop_front() {
        if let Some(regions) = rev_outlives_map.get(&curr) {
            for &r in regions {
                if result.insert(r) {
                    queue.push_back(r);
                }
            }
        }
    }
    result
}

pub fn regions_that_outlive<'tcx>(
    outlives: &HashSet<(Region<'tcx>, Region<'tcx>)>,
    region: Region<'tcx>,
) -> HashSet<Region<'tcx>> {
    let mut result = HashSet::new();
    result.insert(region);
    let mut outlives_map: HashMap<Region<'tcx>, Vec<Region<'tcx>>> = HashMap::new();
    for (r1, r2) in outlives {
        outlives_map.entry(*r2).or_insert(vec![]).push(*r1);
    }
    let mut queue = VecDeque::new();
    queue.push_back(region);
    while let Some(curr) = queue.pop_front() {
        if let Some(regions) = outlives_map.get(&curr) {
            for &r in regions {
                if result.insert(r) {
                    queue.push_back(r);
                }
            }
        }
    }
    result
}

pub fn region_outlives_predicates<'tcx>(
    tcx: TyCtxt<'tcx>,
    func_def: DefId,
) -> HashSet<(Region<'tcx>, Region<'tcx>)> {
    let mut outlives_predicates = HashSet::new();
    for (predicate, _) in tcx.predicates_of(func_def).predicates {
        if let ClauseKind::RegionOutlives(outlives_predicate) = predicate.kind().skip_binder() {
            outlives_predicates.insert((outlives_predicate.0, outlives_predicate.1));
        }
    }
    outlives_predicates
}

pub fn region_outlives_relations_in_path<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
    access_elems: AccessElems<'tcx>,
) -> HashSet<(Region<'tcx>, Region<'tcx>)> {
    let mut outlives_relations = HashSet::new();
    let br_chains = borrow_region_chains(acx, base_ty, access_elems);
    for chain in br_chains {
        for window in chain.windows(2) {
            outlives_relations.insert((window[1].0, window[0].0));
        }
    }
    outlives_relations
}

pub fn immutable_reference_region<'tcx>(ref_ty: Ty<'tcx>) -> Option<Region<'tcx>> {
    if let TyKind::Ref(region, _, mutability) = ref_ty.kind() {
        if mutability.is_not() {
            return Some(region.clone());
        }
    }
    None
}

pub fn reference_region<'tcx>(ref_ty: Ty<'tcx>) -> Option<Region<'tcx>> {
    if let TyKind::Ref(region, _, _) = ref_ty.kind() {
        return Some(region.clone());
    }
    None
}

pub fn possible_pointer_types<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
) -> Option<HashSet<Ty<'tcx>>> {
    try_to_eval_possible_pointer_types(acx, base_ty, &acx.mk_access_elems(&[]))
}

// Get the maximum shared borrow region of an access path with the given base type and access elements.
pub fn max_immutable_borrow_region<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
    access_elems: AccessElems<'tcx>,
) -> Option<Region<'tcx>> {
    let br_chains = borrow_region_chains(acx, base_ty, access_elems);
    if br_chains.is_empty() {
        return None;
    }
    let mut iter = br_chains.iter();
    let mut imm_borrow_regions = iter
        .next()
        .unwrap()
        .iter()
        .filter(|(_, mutbl)| mutbl.is_not())
        .collect::<Vec<_>>();
    for chain in iter {
        imm_borrow_regions
            .retain(|(region, _)| chain.iter().any(|(r, mutbl)| r == region && mutbl.is_not()));
    }
    if !imm_borrow_regions.is_empty() {
        return Some(imm_borrow_regions.last().unwrap().0);
    }
    None
}

// Get the borrow region chains of an access path with the given base type and access elements.
fn borrow_region_chains<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
    access_elems: AccessElems<'tcx>,
) -> Vec<Vec<(Region<'tcx>, Mutability)>> {
    let mut br_chains: Vec<Vec<(Region<'tcx>, Mutability)>> = vec![];
    if access_elems.len() == 0 {
        if let Some(ptr_tys) = possible_pointer_types(acx, base_ty) {
            for ptr_ty in ptr_tys {
                if let TyKind::Ref(region, _, mutbl) = ptr_ty.kind() {
                    br_chains.push(vec![(*region, *mutbl)]);
                }
            }
        }
        return br_chains;
    }
    match access_elems[0] {
        AccessElem::Deref => {
            if let Some(ptr_tys) = possible_pointer_types(acx, base_ty) {
                for ptr_ty in ptr_tys {
                    if let TyKind::Ref(_, ty, _) | TyKind::RawPtr(ty, _) = ptr_ty.kind() {
                        let mut br_chains_after =
                            borrow_region_chains(acx, *ty, &access_elems[1..]);
                        if let TyKind::Ref(region, _, mutbl) = ptr_ty.kind() {
                            if br_chains_after.is_empty() {
                                br_chains.push(vec![(*region, *mutbl)]);
                            } else {
                                for br_chain in &mut br_chains_after {
                                    br_chain.insert(0, (*region, *mutbl));
                                }
                                br_chains.extend(br_chains_after);
                            }
                        }
                    } else {
                        continue;
                    }
                }
            }
        }
        AccessElem::AggTyProj(proj) => {
            if let Some(ptr_tys) = try_to_eval_possible_pointer_types(
                acx,
                base_ty,
                &acx.mk_access_elems(&[AccessElem::AggTyProj(proj)]),
            ) {
                for ptr_ty in ptr_tys {
                    br_chains.extend(borrow_region_chains(acx, ptr_ty, &access_elems[1..]));
                }
            }
        }
        _ => {}
    }
    br_chains
}

/// Given the access elements and the base type of an access path, retrieve the region
/// constraints of the path.
///
/// For example, given an access path `(*foo).f`, where `foo` is a reference of type
/// `&'a Foo<'b>` and its field `f` is a reference with region `'b`, its region
/// constraints include `'a` and `'b`. This means if we have another reference with
/// `'a` or `'b` region, we cannot modify `(*foo).f` since it is assumed borrow.
pub fn all_regions_of<'tcx>(
    acx: &AnalysisContext<'tcx>,
    base_ty: Ty<'tcx>,
    access_elems: AccessElems<'tcx>,
) -> HashSet<Region<'tcx>> {
    let mut regions = HashSet::new();
    if access_elems.len() == 0 {
        if let Some(ptr_tys) = possible_pointer_types(acx, base_ty) {
            for ptr_ty in ptr_tys {
                if let Some(region) = reference_region(ptr_ty) {
                    regions.insert(region.clone());
                }
            }
        }
        return regions;
    }
    match access_elems[0] {
        AccessElem::Deref => {
            if let Some(ptr_tys) = possible_pointer_types(acx, base_ty) {
                for ptr_ty in ptr_tys {
                    if let TyKind::Ref(region, ty, _) = ptr_ty.kind() {
                        regions.insert(region.clone());
                        // Recursively retrieve the region of the field access
                        regions.extend(all_regions_of(acx, *ty, &access_elems[1..]));
                    }
                }
            }
        }
        AccessElem::AggTyProj(proj) => {
            if let Some(ptr_tys) = try_to_eval_possible_pointer_types(
                acx,
                base_ty,
                &acx.mk_access_elems(&[AccessElem::AggTyProj(proj)]),
            ) {
                // For simplicity, we include all the regions for all possible pointer types
                for ptr_ty in ptr_tys {
                    regions.extend(all_regions_of(acx, ptr_ty, &access_elems[1..]));
                }
            }
        }
        _ => {}
    }

    regions
}

#[cfg(test)]
mod tests {
    use rustc_middle::ty::TyCtxt;

    use crate::analysis_context::AnalysisContext;
    use crate::infoflow::data::access_elem::AccessElem;
    use crate::tsa::aliasing_xor_mutability::{
        borrow_region_chains, max_immutable_borrow_region, region_outlives_relations_in_path,
        regions_outlived_by, regions_that_outlive,
    };
    use crate::util::options::AnalysisOptions;
    use crate::util::test_util::{compile, get_func};

    #[test]
    fn test_max_immutable_borrow_region() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut u32,
            }

            struct Bar<'a, 'b> {
                foo: &'b Foo<'a>,
            }

            union Baz<'a, 'b, 'c, 'd> {
                bar: &'c Bar<'a, 'b>,
                foo: &'c &'d Foo<'a>,
            }

            pub fn bar<'a, 'b, 'c>(bar: &'c Bar<'a, 'b>) {
            }

            pub fn baz<'a, 'b, 'c, 'd>(baz: &Baz<'a, 'b, 'c, 'd>) {
            }
        "#;

        let test_fn = |tcx: TyCtxt<'_>| {
            let acx = AnalysisContext::new(tcx, AnalysisOptions::default()).unwrap();
            let func_def_id = get_func(tcx, "bar").unwrap();
            let src_base_ty = acx
                .tcx
                .fn_sig(func_def_id)
                .skip_binder()
                .skip_binder()
                .inputs()[0];
            let access_elems = acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref]);
            let br_chains = borrow_region_chains(&acx, src_base_ty, access_elems);
            assert_eq!(br_chains.len(), 1);
            println!("Borrow chains: {:?}", br_chains);
            let max_imm_borrow_region =
                max_immutable_borrow_region(&acx, src_base_ty, access_elems);
            println!("Max immutable borrow region: {:?}", max_imm_borrow_region);
            let outlives_relations =
                region_outlives_relations_in_path(&acx, src_base_ty, access_elems);
            println!("Outlives relations: {:?}", outlives_relations);

            let func_def_id = get_func(tcx, "baz").unwrap();
            let src_base_ty = acx
                .tcx
                .fn_sig(func_def_id)
                .skip_binder()
                .skip_binder()
                .inputs()[0];
            let access_elems =
                acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref, AccessElem::Deref]);
            let br_chains = borrow_region_chains(&acx, src_base_ty, access_elems);
            assert_eq!(br_chains.len(), 2);
            println!("Borrow chains: {:?}", br_chains);
            let max_imm_borrow_region =
                max_immutable_borrow_region(&acx, src_base_ty, access_elems);
            println!("Max immutable borrow region: {:?}", max_imm_borrow_region);
            let outlives_relations =
                region_outlives_relations_in_path(&acx, src_base_ty, access_elems);
            println!("Outlives relations: {:?}", outlives_relations);
            let outlived_by =
                regions_outlived_by(&outlives_relations, max_imm_borrow_region.unwrap());
            println!("Outlived by: {:?}", outlived_by);
            let outlives =
                regions_that_outlive(&outlives_relations, max_imm_borrow_region.unwrap());
            println!("Outlives: {:?}", outlives);
        };

        compile(rust_code.to_string(), test_fn);
    }
}
