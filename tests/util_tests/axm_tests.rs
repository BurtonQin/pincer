#[cfg(test)]
mod test {
    use std::collections::HashSet;

    use pincer::analysis_context::AnalysisContext;
    use pincer::infoflow::data::access_elem::AccessElem;
    use pincer::infoflow::data::access_path::AccessPath;
    use pincer::mir::function::FuncDef;
    use pincer::tsa::aliasing_xor_mutability;
    use pincer::util::test_util::{compile, get_func, initialize_analysis_context};
    use rustc_middle::mir::{Local, Place};

    /// Asserts that `src_path` and `ret_path` each resolve to exactly one
    /// pointer type, then checks whether `src_path` is AXM-compliant against
    /// the alias set `{src_path, ret_path}`.
    fn check_axm_compliance<'tcx>(
        acx: &AnalysisContext<'tcx>,
        src_path: AccessPath<'tcx>,
        ret_path: AccessPath<'tcx>,
        expected_compliant: bool,
    ) {
        assert_eq!(src_path.try_to_eval_possible_pointer_types(acx).unwrap().len(), 1);
        assert_eq!(ret_path.try_to_eval_possible_pointer_types(acx).unwrap().len(), 1);

        let result_aliases = HashSet::from([ret_path, src_path]);
        let is_compliant =
            aliasing_xor_mutability::is_axm_compliant(acx, src_path, &result_aliases);
        assert_eq!(
            is_compliant, expected_compliant,
            "expected AXM compliance to be {expected_compliant}"
        );
    }

    #[test]
    fn unsafe_deref_test() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut Vec<u32>,
            }

            impl<'a> Foo<'a> {
                fn add(&mut self, x: u32) {
                    self.f.push(x);
                }
            }

            fn unsafe_deref<'a>(foo: &Foo<'a>) -> &'a u32 {
                unsafe { &*(foo.f.as_ptr()) }
            }

            pub fn main() {
                let mut v = vec![1];
                let mut foo = Foo { f: &mut v };
                let x = unsafe_deref(&foo);
                foo.add(2);
                let y = *x;
                println!("{y:?}");
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "unsafe_deref").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, false);
        });
    }

    #[test]
    fn safe_deref_test() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut Vec<u32>,
            }

            fn safe_deref<'a, 'b>(foo: &'b Foo<'a>) -> &'b u32 {
                unsafe { &*(foo.f.as_ptr()) }
            }

            pub fn main() {
                let mut v = vec![1];
                let mut foo = Foo { f: &mut v };
                let x = safe_deref(&foo);
                let y = *x;
                println!("{y:?}");
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "safe_deref").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, true);
        });
    }

    #[test]
    fn safe_deref_test2() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut Vec<u32>,
            }

            fn safe_deref<'a, 'b>(foo: &'b Foo<'a>) -> &'a u32 where 'b: 'a {
                unsafe { &*(foo.f.as_ptr()) }
            }

            pub fn main() {
                let mut v = vec![1];
                let mut foo = Foo { f: &mut v };
                let x = safe_deref(&foo);
                let y = *x;
                println!("{y:?}");
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "safe_deref").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, true);
        });
    }

    #[test]
    fn unsafe_get_mut_test() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut u32,
            }

            fn get_mut<'a, 'b>(foo: &'b mut Foo<'a>) -> &'a mut u32 {
                unsafe { &mut *(foo.f as *mut u32) }
            }

            pub fn main() {
                let mut a = 1;
                let mut foo = Foo { f: &mut a };
                let f = get_mut(&mut foo);
                *foo.f = 2;
                *f = 3;
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "get_mut").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, false);
        });
    }

    #[test]
    fn safe_get_mut_test() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut u32,
            }

            fn get_mut<'a, 'b>(foo: &'b mut Foo<'a>) -> &'b mut u32 {
                unsafe { &mut *(foo.f as *mut u32) }
            }

            pub fn main() {
                let mut a = 1;
                let mut foo = Foo { f: &mut a };
                let f = get_mut(&mut foo);
                *foo.f = 2;
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "get_mut").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, true);
        });
    }

    #[test]
    fn unsafe_get_test() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut u32,
            }

            struct Bar<'a, 'b> {
                foo: &'b Foo<'a>,
            }

            fn get<'a, 'b, 'c>(bar: &'c Bar<'a, 'b>) -> &'a u32 {
                unsafe { &*(bar.foo.f as *const u32) }
            }

            pub fn main() {
                let mut a = 1;
                let foo = Foo { f: &mut a };
                let bar = Bar { foo: &foo };
                let f = get(&bar);
                println!("{f:?}");
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "get").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, false);
        });
    }

    #[test]
    fn safe_get_test() {
        let rust_code = r#"
            struct Foo<'a> {
                f: &'a mut u32,
            }

            struct Bar<'a, 'b> {
                foo: &'b Foo<'a>,
            }

            fn get<'a, 'b, 'c>(bar: &'c Bar<'a, 'b>) -> &'b u32 {
                bar.foo.f
            }

            pub fn main() {
                let mut a = 1;
                let foo = Foo { f: &mut a };
                let bar = Bar { foo: &foo };
                let f = get(&bar);
                println!("{f:?}");
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let func_def = FuncDef::new_func_def(
                get_func(tcx, "get").unwrap(), tcx.mk_args(&[]));
            let src_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(1)),
            )
            .project_deeper(&acx, acx.mk_access_elems(&[AccessElem::Deref, AccessElem::Deref]));
            let ret_path = AccessPath::from_rustc_place(
                &acx, func_def, &Place::from(Local::from_usize(0)),
            );
            check_axm_compliance(&acx, src_path, ret_path, true);
        });
    }
}
