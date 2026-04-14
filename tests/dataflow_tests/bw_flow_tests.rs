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
        compile, get_func, get_place, init_logger, initialize_analysis_context, return_location,
    };

    fn find_var_flow_origins<'tcx>(
        acx: &AnalysisContext<'tcx>,
        func_def_id: rustc_hir::def_id::DefId,
        var_name: &str,
    ) -> HashSet<PointerFlowOrigin<'tcx>> {
        let tcx = acx.tcx();
        let func_def = FuncDef::new_func_def(func_def_id, tcx.mk_args(&[]));
        let location = return_location(tcx, func_def_id);
        let place = get_place(tcx, func_def_id, var_name)
            .unwrap_or_else(|| panic!("Variable '{}' not found in {:?}", var_name, func_def_id));
        let query = Query::new(
            AccessPath::from_rustc_place(acx, func_def, &place),
            Unit::new(func_def, location),
        );
        let mut backward_solver = BackwardSolver::new(acx);
        backward_solver.start_propagation(query, true);
        acx.get_flow_origins(&query)
    }

    #[test]
    pub fn test_reference_origin() {
        let rust_code = r#"
            fn foo(x: &u32) -> &u32 {
                x
            }

            pub fn main() {
                let a = 1;
                let x = &a;
                let y = foo(x);
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "y");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Reference { .. }
            ));
        });
    }

    #[test]
    pub fn test_parameter_origin() {
        let rust_code = r#"
            fn foo(x: &u32) -> &u32 {
                x
            }

            pub fn main(x: &u32) -> &u32 {
                let y = foo(x);
                y
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "y");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Parameter { .. }
            ));
        });
    }

    #[test]
    pub fn test_heap_allocation() {
        let rust_code = r#"
            pub fn main() {
                let v = vec![1, 2, 3];
                let v_ptr = v.as_ptr();
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "v_ptr");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Allocation { .. }
            ));
        });
    }

    #[test]
    pub fn test_heap_field() {
        let rust_code = r#"
            struct Foo {
                f: u32,
                g: u32,
            }

            pub fn box_foo() -> Box<Foo> {
                Box::new(Foo { f: 1, g: 2 })
            }

            pub fn main() {
                let b = box_foo();
                let p = &b.g;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "p");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Allocation { .. }
            ));
        });
    }

    #[test]
    pub fn test_indirect_reference() {
        let rust_code = r#"
            struct Foo<'a> {
                g: u32,
                f: &'a u32,
            }

            pub fn main() {
                let a = 1;
                let foo = Foo { g: 2, f: &a };
                let p = &foo;
                let q = &(*p).f;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "q");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Reference { .. }
            ));
        });
    }

    #[test]
    pub fn test_interprocedural_indirect_reference() {
        let rust_code = r#"
            struct Foo<'a> {
                g: u32,
                f: &'a u32,
            }

            pub fn bar<'a, 'b>(foo: &'a Foo<'b>) -> &'a &'b u32 {
                &foo.f
            }

            pub fn main() {
                let mut a = 1;
                let b = 2;
                let mut foo = Foo { g: 2, f: &a };
                let p = &mut foo;
                (*p).f = &b;
                let q = bar(p);
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "q");
            // todo: two same flow origins are computed for this case
            // println!("Flow origins: {:?}", flow_origins);
            // assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Reference { .. }
            ));
        });
    }

    #[test]
    pub fn test_load() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a i32,
                g: &'a i32,
            }

            pub fn main() {
                let x = 2;
                let y = 3;
                let foo = Foo { f: &x, g: &y };
                let r = &foo;
                let p = r;
                let q = (*p).f;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "q");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Reference { .. }
            ));
        });
    }

    #[test]
    pub fn test_store() {
        let rust_code = r#"
            struct MyVec {
                capacity: usize,
                ptr: *mut u8
            }

            impl MyVec {
                fn as_ptr(&self) -> *mut u8 {
                    self.ptr
                }
            }

            pub fn main(m: &mut MyVec) {
                let mut v = Vec::with_capacity(8);
                m.ptr = v.as_mut_ptr();
                m.capacity = 8;
                let ptr = m.as_ptr();
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main_def_id, "ptr");
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Allocation { .. }
            ));
        });
    }

    #[test]
    fn test_vec_push() {
        let rust_code = r#"
            pub fn main() {
                let mut v = Vec::new();
                let r = &mut v;
                r.push(1);
                let ptr = r.as_ptr();
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main, "ptr");
            assert!(!flow_origins.is_empty());
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Allocation { .. }
            ));
        });
    }

    #[test]
    fn test_backward_call_poa() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a u32,
            }

            fn bar<'a, 'b>(foo: &'b mut Foo<'a>, x: &'a u32) {
                let r = id(foo);
                r.f = x;
            }

            fn id<'a, 'b>(foo: &'b mut Foo<'a>) -> &'b mut Foo<'a> {
                foo
            }

            pub fn main() {
                let a = 1;
                let b = 2;
                let mut foo = Foo { f: &a };
                let p = &mut foo;
                bar(p, &b);
                let q = foo.f;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main, "q");
            assert_eq!(flow_origins.len(), 2);
        });
    }

    #[test]
    fn test_address_taken_poa() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a i32,
                g: &'a i32,
            }

            pub fn main() {
                let a = 1;
                let b = 2;
                let c = 3;
                let d = 4;
                let e = 5;
                let f = 6;
                let mut foo1 = Foo { f: &a, g: &b };
                let mut foo2 = Foo { f: &c, g: &d };
                let mut p = &mut foo1;
                (*p).g = &e;
                p = &mut foo2;
                let mut q = &mut foo1.g;
                *q = &f;
                let s = foo1.g as *const i32;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            let flow_origins = find_var_flow_origins(&acx, main, "s");
            // s = foo1.g, which may point to &b (init), &e (via (*p).g = &e), &f (via *q = &f)
            assert_eq!(flow_origins.len(), 3);
            assert!(flow_origins.iter().all(|o| matches!(
                o.kind,
                FlowOriginKind::Reference { .. }
            )));
        });
    }

    #[test]
    pub fn test_multiple_queries() {
        let rust_code = r#"
            struct Foo {}
            pub fn box_foo() -> Box<Foo> {
                Box::new(Foo {})
            }

            pub fn main() {
                let b1 = box_foo();
                let b2 = box_foo();
                let p = &*b1;
                let q = &*b2;
            }
        "#;

        compile(rust_code.to_string(), |tcx: TyCtxt<'_>| {
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();

            let flow_origins = find_var_flow_origins(&acx, main_def_id, "p");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Allocation { .. }
            ));

            let flow_origins = find_var_flow_origins(&acx, main_def_id, "q");
            assert_eq!(flow_origins.len(), 1);
            assert!(matches!(
                flow_origins.iter().next().unwrap().kind,
                FlowOriginKind::Allocation { .. }
            ));
        });
    }
}
