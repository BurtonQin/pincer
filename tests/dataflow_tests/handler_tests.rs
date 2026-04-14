/// Tests for config-driven external function effect handling.
///
/// These tests verify that the backward/forward effects handlers correctly
/// propagate dataflow across external functions (no MIR available) whose
/// effects are declared in `config/builtins.yaml`.
///
/// Test functions:
///   - `pincer_test_identity`: Copy effect (return = copy of arg0)
///   - `pincer_test_load`:     Load effect (return = *arg0)
///   - `pincer_test_store`:    Store effect (*arg0 = arg1)
#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use rustc_middle::ty::TyCtxt;

    use pincer::analysis_context::AnalysisContext;
    use pincer::infoflow::aliasing::query::Query;
    use pincer::infoflow::backward::backward_solver::BackwardSolver;
    use pincer::infoflow::data::access_path::AccessPath;
    use pincer::infoflow::{FlowOriginKind, PointerFlowOrigin, Unit};
    use pincer::mir::function::FuncDef;
    use pincer::util::test_util::{
        check_alias_assertions, compile, get_func, get_place, init_logger,
        initialize_analysis_context, return_location,
    };

    const MARKER_FUNCTIONS: &str = r#"
        fn may_alias<T, U>(_: &T, _: &U) {}
        #[allow(dead_code)]
        fn no_alias<T, U>(_: &T, _: &U) {}
    "#;

    fn find_var_flow_origins<'tcx>(
        acx: &AnalysisContext<'tcx>,
        func_def_id: rustc_hir::def_id::DefId,
        var_name: &str,
    ) -> HashSet<PointerFlowOrigin<'tcx>> {
        let tcx = acx.tcx();
        let func_def = FuncDef::new_func_def(func_def_id, tcx.mk_args(&[]));
        let location = return_location(tcx, func_def_id);
        let place = get_place(tcx, func_def_id, var_name)
            .unwrap_or_else(|| panic!("Variable '{}' not found", var_name));
        let query = Query::new(
            AccessPath::from_rustc_place(acx, func_def, &place),
            Unit::new(func_def, location),
        );
        let mut backward_solver = BackwardSolver::new(acx);
        backward_solver.start_propagation(query, true);
        acx.get_flow_origins(&query)
    }

    /// Check that the Reference origins in `origins` include all `expected_vars`.
    fn expect_reference_origins<'tcx>(
        acx: &AnalysisContext<'tcx>,
        func_def_id: rustc_hir::def_id::DefId,
        origins: &HashSet<PointerFlowOrigin<'tcx>>,
        expected_vars: &[&str],
    ) {
        let tcx = acx.tcx();
        let ref_locals: HashSet<_> = origins
            .iter()
            .filter_map(|o| match &o.kind {
                FlowOriginKind::Reference { ref_path, .. } => Some(ref_path.local),
                _ => None,
            })
            .collect();

        for name in expected_vars {
            let place = get_place(tcx, func_def_id, name)
                .unwrap_or_else(|| panic!("Variable '{}' not found", name));
            assert!(
                ref_locals.contains(&place.local),
                "Expected Reference origin for '{}' (local {:?}) not found in {:?}",
                name,
                place.local,
                origins,
            );
        }
    }

    fn check_alias(rust_code: &str) {
        let code = [MARKER_FUNCTIONS, rust_code].concat();
        compile(code, |tcx| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            check_alias_assertions(&acx, main);
        });
    }

    // =====================================================================
    // Copy effect tests
    // =====================================================================

    /// Backward: result of pincer_test_identity(ptr) should trace back to `a`.
    #[test]
    fn test_copy_effect_backward() {
        let rust_code = r#"
            extern "C" {
                fn pincer_test_identity(ptr: *const u8) -> *const u8;
            }

            pub fn main() {
                let a: u8 = 1;
                let ptr = &a as *const u8;
                let result = unsafe { pincer_test_identity(ptr) };
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let origins = find_var_flow_origins(&acx, main, "result");
            expect_reference_origins(&acx, main, &origins, &["a"]);
        });
    }

    /// Aliasing: result of pincer_test_identity(ptr) should alias with ptr.
    #[test]
    fn test_copy_effect_alias() {
        check_alias(
            r#"
            extern "C" {
                fn pincer_test_identity(ptr: *const u8) -> *const u8;
            }

            pub fn main() {
                let a: u8 = 1;
                let ptr = &a as *const u8;
                let result = unsafe { pincer_test_identity(ptr) };
                may_alias(&result, &ptr);
            }
        "#,
        );
    }

    /// no_alias: result of identity(ptr_a) should NOT alias with an unrelated pointer.
    #[test]
    fn test_copy_effect_no_alias() {
        check_alias(
            r#"
            extern "C" {
                fn pincer_test_identity(ptr: *const u8) -> *const u8;
            }

            pub fn main() {
                let a: u8 = 1;
                let b: u8 = 2;
                let ptr_a = &a as *const u8;
                let ptr_b = &b as *const u8;
                let result = unsafe { pincer_test_identity(ptr_a) };
                no_alias(&result, &ptr_b);
            }
        "#,
        );
    }

    // =====================================================================
    // Load effect tests
    // =====================================================================

    /// Backward: result of pincer_test_load(&inner) should trace back to `a`.
    #[test]
    fn test_load_effect_backward() {
        let rust_code = r#"
            extern "C" {
                fn pincer_test_load(ptr: *const *const u8) -> *const u8;
            }

            pub fn main() {
                let a: u8 = 1;
                let inner: *const u8 = &a;
                let result = unsafe { pincer_test_load(&inner as *const *const u8) };
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let origins = find_var_flow_origins(&acx, main, "result");
            expect_reference_origins(&acx, main, &origins, &["a"]);
        });
    }

    /// Aliasing: result of pincer_test_load(&inner) should alias with inner.
    #[test]
    fn test_load_effect_alias() {
        check_alias(
            r#"
            extern "C" {
                fn pincer_test_load(ptr: *const *const u8) -> *const u8;
            }

            pub fn main() {
                let a: u8 = 1;
                let inner: *const u8 = &a;
                let result = unsafe { pincer_test_load(&inner as *const *const u8) };
                may_alias(&result, &inner);
            }
        "#,
        );
    }

    // =====================================================================
    // Store effect tests
    // =====================================================================

    /// Backward: after pincer_test_store(&mut slot, ptr), reading slot should
    /// trace back to `b` (the stored value), not `a` (the initial value).
    #[test]
    fn test_store_effect_backward() {
        let rust_code = r#"
            extern "C" {
                fn pincer_test_store(dst: *mut *const u8, src: *const u8);
            }

            pub fn main() {
                let a: u8 = 1;
                let b: u8 = 2;
                let mut slot: *const u8 = &a as *const u8;
                let ptr: *const u8 = &b;
                unsafe { pincer_test_store(&mut slot as *mut *const u8, ptr) };
                let result = slot;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let origins = find_var_flow_origins(&acx, main, "result");
            expect_reference_origins(&acx, main, &origins, &["b"]);
        });
    }

    /// Aliasing: after pincer_test_store(&mut slot, ptr), slot should alias
    /// with ptr (both point to b).
    #[test]
    fn test_store_effect_alias() {
        check_alias(
            r#"
            extern "C" {
                fn pincer_test_store(dst: *mut *const u8, src: *const u8);
            }

            pub fn main() {
                let a: u8 = 1;
                let b: u8 = 2;
                let mut slot: *const u8 = &a as *const u8;
                let ptr: *const u8 = &b;
                unsafe { pincer_test_store(&mut slot as *mut *const u8, ptr) };
                may_alias(&slot, &ptr);
            }
        "#,
        );
    }

}
