#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use pincer::analysis_context::AnalysisContext;
    use pincer::infoflow::data::access_elem::AccessElem;
    use pincer::infoflow::data::access_path::AccessPath;
    use pincer::infoflow::forward::forward_solver::ForwardSolver;
    use pincer::infoflow::Unit;
    use pincer::mir::function::FuncDef;
    use pincer::util::test_util::{
        compile, get_func, get_place, initialize_analysis_context, return_location,
    };
    use rustc_hir::def_id::DefId;
    use rustc_middle::mir::{BasicBlock, Location};

    /// Forward-propagates the given access path from the start of the function
    /// and returns all access paths it flows to at the return location.
    fn find_forward_flow_targets<'tcx>(
        acx: &AnalysisContext<'tcx>,
        func_def_id: DefId,
        access_path: AccessPath<'tcx>,
    ) -> HashSet<AccessPath<'tcx>> {
        let tcx = acx.tcx();
        let func_def = FuncDef::new_func_def(func_def_id, tcx.mk_args(&[]));
        let start_unit = Unit::new(
            func_def,
            Location { block: BasicBlock::from_usize(0), statement_index: 0 },
        );
        let end_unit = Unit::new(func_def, return_location(tcx, func_def_id));

        let mut fw_solver = ForwardSolver::new(acx);
        fw_solver.start_propagation(access_path, start_unit, true);

        let mut targets = HashSet::new();
        if let Some(path_edges) = fw_solver.path_edges_at_stmt(end_unit) {
            for edge in path_edges {
                targets.insert(*edge.fact_at_target());
            }
        }
        targets
    }

    #[test]
    fn test_store_forward_flow() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a i32,
            }

            pub fn main() {
                let x = 2;
                let y = 3;
                let mut foo = Foo { f: &x };
                let r = &mut foo;
                let s = &(*r).f;
                let t = unsafe { &*(s as *const &i32) };
                let q = &y;
                let p = r;
                (*p).f = q;
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let main_def = FuncDef::new_func_def(main, tcx.mk_args(&[]));

            // Build access path for foo.f (Foo has a single field at zero byte offset,
            // so foo.f collapses to the same access path as foo)
            let foo_place = get_place(tcx, main, "foo").unwrap();
            let foo_f_path = AccessPath::from_rustc_place(&acx, main_def, &foo_place);

            // Construct &x: access path for x with Ref element
            let x_place = get_place(tcx, main, "x").unwrap();
            let ref_x = AccessPath::from_rustc_place_with_elems(
                &acx, main_def, &x_place,
                acx.mk_access_elems(&[AccessElem::Ref]),
            );

            // Construct &y: access path for y with Ref element
            let y_place = get_place(tcx, main, "y").unwrap();
            let ref_y = AccessPath::from_rustc_place_with_elems(
                &acx, main_def, &y_place,
                acx.mk_access_elems(&[AccessElem::Ref]),
            );

            // Forward flow of &x should reach foo.f, as we do not have strong update in infoflow
            let x_targets = find_forward_flow_targets(&acx, main, ref_x);
            assert!(
                x_targets.iter().any(|t| t.activate() == foo_f_path),
                "&x should flow to foo.f"
            );

            // Forward flow of &y should reach foo.f
            let y_targets = find_forward_flow_targets(&acx, main, ref_y);
            assert!(
                y_targets.iter().any(|t| t.activate() == foo_f_path),
                "&y should flow to foo.f"
            );
        });
    }
}
