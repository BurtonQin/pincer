#[cfg(test)]
mod test {
    use pincer::mir::function::FuncDef;
    use pincer::tsa::analyses::memory_safety_analysis::{
        vulnerable_pointer::collect_vulnerable_pointers, MemorySafetyAnalysis,
    };
    use pincer::util::test_util::{compile, get_func, initialize_analysis_context};

    /// Compiles the given Rust code, runs memory safety analysis, asserts
    /// whether error seeds are found, and verifies which user-defined functions
    /// were or were not traversed.
    fn check_modular_analysis(
        rust_code: &str,
        expect_errors: bool,
        analyzed_fns: &[&str],
        not_analyzed_fns: &[&str],
    ) {
        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let vulnerable_pointers = collect_vulnerable_pointers(&acx);

            let mut analysis = MemorySafetyAnalysis::new(&acx);
            for vulnerable_pointer in vulnerable_pointers {
                analysis.analyze_vulnerable_pointer(vulnerable_pointer);
            }

            assert_eq!(
                !analysis.error_seeds().is_empty(),
                expect_errors,
                "expected error seeds to be {}",
                if expect_errors { "non-empty" } else { "empty" }
            );

            let analyzed = analysis.analyzed_functions();
            for name in analyzed_fns {
                let def_id = get_func(tcx, name)
                    .unwrap_or_else(|| panic!("Function '{}' not found", name));
                let func_def = FuncDef::new_func_def(def_id, tcx.mk_args(&[]));
                assert!(analyzed.contains(&func_def),
                    "'{}' should be analyzed", name);
            }
            for name in not_analyzed_fns {
                let def_id = get_func(tcx, name)
                    .unwrap_or_else(|| panic!("Function '{}' not found", name));
                let func_def = FuncDef::new_func_def(def_id, tcx.mk_args(&[]));
                assert!(!analyzed.contains(&func_def),
                    "'{}' should not be analyzed", name);
            }
        });
    }

    // TODO: AXM check does not yet detect that the raw pointer is not escaped
    #[test]
    #[ignore]
    fn safe_raw_ptr_not_escaped() {
        check_modular_analysis(r#"
            pub fn foo(v: &mut Vec<u32>) -> &mut Vec<u32> {
                let ptr = v.as_mut_ptr();
                v
            }

            pub fn main() {
                let mut v = vec![1, 2, 3];
                let v2 = foo(&mut v);
            }
        "#, false, &["foo"], &["main"]);
    }

    #[test]
    fn safe_raw_ptr_deref() {
        check_modular_analysis(r#"
            pub fn foo(v: &mut Vec<u32>) -> &u32 {
                let ptr = v.as_mut_ptr();
                unsafe { &*(ptr) }
            }

            pub fn main() {
                let mut v = vec![1, 2, 3];
                let v2 = foo(&mut v);
            }
        "#, false, &["foo"], &["main"]);
    }

    #[test]
    fn safe_raw_ptr_to_ref() {
        check_modular_analysis(r#"
            pub fn foo<'a, 'b>(x: &'a &'b Vec<u32>) -> &'b u32 {
                unsafe { &*(*x).as_ptr() }
            }
            pub fn main() {
                let mut v = vec![1, 2, 3];
                let r = &v;
                let x = &r;
                let p = foo(x);
                println!("{:?}", p);
            }
        "#, false, &["foo"], &["main"]);
    }

    #[test]
    fn unsafe_raw_ptr_to_ref() {
        check_modular_analysis(r#"
            pub fn foo<'a, 'b>(x: &'a &'b mut Vec<u32>) -> &'b u32 {
                unsafe { &*(*x).as_ptr() }
            }
            pub fn main() {
                let mut v = vec![1, 2, 3];
                let r = &mut v;
                let x = &r;
                let p = foo(x);
                r.reserve(10);
                println!("{:?}", p);
            }
        "#, true, &["foo", "main"], &[]);
    }
}
