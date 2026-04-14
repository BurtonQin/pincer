#[cfg(test)]
mod test {
    use pincer::tsa::analyses::memory_safety_analysis::{
        vulnerable_pointer::collect_vulnerable_pointers, MemorySafetyAnalysis,
    };
    use pincer::util::test_util::{compile, initialize_analysis_context};

    /// Compiles the given Rust code, runs memory safety analysis, and asserts
    /// whether use-after-free error seeds are found.
    fn check_use_after_free(rust_code: &str, expect_errors: bool) {
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
    fn uaf_vec_test() {
        check_use_after_free(r#"
            pub fn main() {
                let mut v = vec![1];
                let p = unsafe {
                    &*v.as_mut_ptr()
                };
                drop(v);
                println!("{:?}", p);
            }
        "#, true);
    }

    #[test]
    fn vec_insert_bytes() {
        check_use_after_free(r#"
            pub fn vec_insert_bytes(target: &mut Vec<u8>, idx: usize, source: &[u8]) {
                use std::ptr::copy;

                if idx > target.len() {
                    panic!("index out of bounds: the len is {} but the index is {}",
                        target.len(), idx);
                }

                let old_len = target.len();
                let insertion_len = source.len();
                let source_ptr = source.as_ptr();
                let insertion_point = unsafe {
                    // SAFE: we panic if idx > target.len(), through idx == target.len() is fine
                    target.as_mut_ptr().offset(idx as isize)
                };
                let moved_data_len = old_len - idx;

                target.reserve(insertion_len);

                unsafe {
                    copy(/*src*/insertion_point,
                        /*dest*/insertion_point.offset(insertion_len as isize),
                        /*count*/moved_data_len);

                    copy(source_ptr, insertion_point, insertion_len);

                    target.set_len(old_len + insertion_len)
                }
            }
        "#, true);
    }



    #[test]
    fn lifetime_bug_test() {
        check_use_after_free(r#"
            struct Foo<'a> {
                f: &'a mut Vec<u32>,
            }

            impl<'a> Foo<'a> {
                fn add(&mut self, x: u32) {
                    self.f.push(x);
                }
            }

            fn deref<'a>(foo: &Foo<'a>) -> &'a u32 {
                unsafe { &*(foo.f.as_ptr()) }
            }

            pub fn main() {
                let mut v = vec![1];
                let mut foo = Foo { f: &mut v };
                let x = deref(&foo);
                foo.add(2);

                let y = *x;
                println!("{y:?}");
            }
        "#, true);
    }

    #[test]
    fn lifetime_bug_test2() {
        check_use_after_free(r#"
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
        "#, true);
    }


    // TODO: analysis does not yet detect use-after-free through global raw pointers
    #[test]
    #[ignore]
    fn global_ptr_test() {
        check_use_after_free(r#"
            use std::ptr;

            // Global raw pointer
            static mut GLOBAL_PTR: *mut i32 = ptr::null_mut();

            fn allocate_and_store() {
                // Allocate a boxed integer
                let mut v: Vec<i32> = vec![1, 2, 3];

                unsafe {
                    // Store raw pointer globally
                    GLOBAL_PTR = v.as_mut_ptr();
                }
            }

            fn use_after_free() {
                unsafe {
                    // Use-after-free: GLOBAL_PTR now points to freed memory
                    if !GLOBAL_PTR.is_null() {
                        println!("Value at pointer: {}", *GLOBAL_PTR); // Undefined behavior!
                    }
                }
            }

            pub fn main() {
                allocate_and_store();
                use_after_free(); // UB happens here
            }
        "#, true);
    }
}
