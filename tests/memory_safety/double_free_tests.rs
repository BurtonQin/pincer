#[cfg(test)]
mod test {
    use pincer::tsa::analyses::memory_safety_analysis::{
        vulnerable_pointer::collect_vulnerable_pointers, MemorySafetyAnalysis,
    };
    use pincer::util::test_util::{compile, initialize_analysis_context};

    /// Compiles the given Rust code, runs memory safety analysis, and asserts
    /// whether error seeds are found.
    fn check_double_free(rust_code: &str, expect_errors: bool) {
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
        });
    }

    #[test]
    fn df_str() {
        check_double_free(r#"
            pub fn main() {
                let mut s = String::from("a tmp string");
                let ptr = s.as_mut_ptr();
                let _v = unsafe { 
                    Vec::from_raw_parts(ptr, s.len(), s.len()) 
                };
            }
        "#, true);
    }

    #[test]
    fn df_vec() {
        check_double_free(r#"
            pub fn main() {
                let mut v = Vec::new();
                v.push(1);
                v.push(2);
                let ptr = v.as_mut_ptr();
                let _v = unsafe {
                    Vec::from_raw_parts(ptr, 2, 2)
                };
            }
        "#, true);
    }

    #[test]
    fn df_vec_macro() {
        check_double_free(r#"
            pub fn main() {
                let mut v = vec![1,2];
                let ptr = v.as_mut_ptr();
                let _v = unsafe {
                    Vec::from_raw_parts(ptr, 2, 2)
                };
            }
        "#, true);
    }

    #[test]
    fn unwind_error() {
        check_double_free(r#"
            pub fn mutate_array(data: &mut Vec<i32>, len: usize) {
                let mut user_data;

                unsafe {
                    user_data = Vec::from_raw_parts(data.as_mut_ptr(), len, len);
                }

                for i in 0..len {
                    user_data[i] += 1;
                }

                std::mem::forget(user_data);
            }
        "#, true);
    }

    #[test]
    fn interprocedural_unwind_error() {
        check_double_free(r#"
            pub fn foo(v: &Vec<u8>) {
                assert!(v.is_empty());
            }

            pub fn main() {
                let mut s = String::from("a tmp string");
                let ptr = s.as_mut_ptr();
                let v = unsafe { 
                    Vec::from_raw_parts(ptr, s.len(), s.len()) 
                };
                foo(&v);
                std::mem::forget(s);
            }
            "#, true);
    }


    #[test]
    fn take_manually_drop() {
        check_double_free(r#"
            fn take<T>(t: T) {
                // do nothing
            }

            pub fn main() {
                use std::mem::ManuallyDrop;
                let mut v = vec![1, 2, 3];
                let ptr = v.as_mut_ptr();
                let m = ManuallyDrop::new(v);
                take(m);
                let b = unsafe { Box::from_raw(ptr) };
            }
        "#, false);
    }

    #[test]
    fn rc_clone() {
        check_double_free(r#"
            use std::rc::Rc;
            use std::sync::Arc;

            pub fn main() {
                let x = Rc::new(32);
                let y = x.clone();
                let x_ptr = Rc::as_ptr(&x);

                let m = Arc::new(32);
                let n = m.clone();
                let m_ptr = Arc::as_ptr(&m);
            }
        "#, false);
    }
}
