#[cfg(test)]
mod test {
    use pincer::tsa::analyses::memory_safety_analysis::{
        vulnerable_pointer::collect_vulnerable_pointers, MemorySafetyAnalysis,
    };
    use pincer::util::test_util::{compile, initialize_analysis_context};

    /// Compiles the given Rust code, runs memory safety analysis, and asserts
    /// whether dangling pointer error seeds are found.
    fn check_dangling_pointer(rust_code: &str, expect_errors: bool) {
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
    fn return_dangling_pointer() {
        check_dangling_pointer(r#"
            pub fn foo() -> Vec<u8> {
                let mut s = String::from("a tmp string");
                let ptr = s.as_mut_ptr();
                let v = unsafe { 
                    Vec::from_raw_parts(ptr, s.len(), s.len()) 
                };
                v
            }
        "#, true);
    }

    #[test]
    fn dangling_pointer() {
        check_dangling_pointer(r#"
            pub fn foo(s: &mut String) {
                let ptr = s.as_mut_ptr();
                let v = unsafe {
                    Vec::from_raw_parts(ptr, s.len(), s.len())
                };
            }
        "#, true);
    }

    #[test]
    fn generic_vec() {
        check_dangling_pointer(r#"
            pub fn foo<T>(v: &mut Vec<T>) {
                let ptr = v.as_mut_ptr();
                let v2 = unsafe {
                    Vec::from_raw_parts(ptr, v.len(), v.len())
                };
            }
        "#, true);
    }

    /// RUSTSEC-2020-0038 (https://rustsec.org/advisories/RUSTSEC-2020-0038.html)
    #[test]
    fn order_of_destruction() {
        check_dangling_pointer(r#"
            use std::vec::Vec as StdVec;
            use std::ptr::NonNull;
            use std::mem::ManuallyDrop;
            use std::ptr::slice_from_raw_parts_mut;

            const MASK_LO: usize = core::u32::MAX as usize;
            const MASK_HI: usize = !(core::u32::MAX as usize);

            pub struct Vec<T> {
                ptr: NonNull<[T]>,
            }

            impl<T> Vec<T> {
                pub fn remove(&mut self, index: usize) -> T {
                    self.with(move |v| v.remove(index))
                }

                pub fn as_mut_ptr(&mut self) -> *mut T {
                    self.ptr.cast().as_ptr()
                }

                fn parts(&self) -> (usize, usize) {
                    let parts = unsafe { &*(self.ptr.as_ptr() as *const [()]) }.len();

                    (parts & MASK_LO, (parts & MASK_HI) >> 32)
                }

                fn with<'a, R: 'a, F: FnOnce(&mut StdVec<T>) -> R>(&mut self, f: F) -> R {
                    let (len, cap) = self.parts();

                    let mut stdvec = unsafe { StdVec::from_raw_parts(self.as_mut_ptr(), len, cap) };

                    let r = f(&mut stdvec);

                    ManuallyDrop::new(core::mem::replace(
                        self,
                        Self::from_stdvec_unchecked(stdvec),
                    ));

                    r
                }

                fn from_stdvec_unchecked(stdvec: StdVec<T>) -> Self {
                    let mut stdvec = ManuallyDrop::new(stdvec);

                    let ptr = stdvec.as_mut_ptr();
                    let len = stdvec.len();
                    let cap = stdvec.capacity();

                    let ptr = slice_from_raw_parts_mut(ptr, len & MASK_LO | (cap & MASK_LO) << 32);

                    Vec {
                        ptr: unsafe { NonNull::new_unchecked(ptr) },
                    }
                }
            }
        "#, true);
    }
}
