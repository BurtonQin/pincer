#[cfg(test)]
mod test {
    use pincer::util::test_util::{
        check_alias_assertions, compile, get_func, init_logger, initialize_analysis_context,
    };

    const MARKER_FUNCTIONS: &str = r#"
        fn may_alias<T, U>(_: &T, _: &U) {}
        #[allow(dead_code)]
        fn no_alias<T, U>(_: &T, _: &U) {}
    "#;

    /// Compiles the given Rust code (with marker functions prepended) and
    /// verifies all `may_alias` / `no_alias` assertions in `main`.
    fn check_alias(rust_code: &str) {
        let code = [MARKER_FUNCTIONS, rust_code].concat();
        compile(code, |tcx| {
            init_logger();
            let acx = initialize_analysis_context(tcx);
            let main = get_func(tcx, "main").unwrap();
            check_alias_assertions(&acx, main);
        });
    }

    #[test]
    fn test_heap_allocation() {
        check_alias(r#"
            pub fn main() {
                let v = vec![1, 2, 3];
                let v_ptr = v.as_ptr();
                may_alias(&v_ptr, &v);
            }
        "#);
    }

    #[test]
    fn test_as_ref() {
        check_alias(r#"
            pub fn main() {
                let v = vec![1, 2, 3];
                let v_ref: &[i32] = v.as_ref();
                may_alias(&v_ref, &v);
            }
        "#);
    }

    #[test]
    fn test_indirect_reference() {
        check_alias(r#"
            struct Foo {
                f: u32,
                g: u32,
            }

            pub fn main() {
                let foo = Foo { f: 1, g: 2 };
                let b = Box::new(foo);
                let ptr = &(*b).g;
                may_alias(&ptr, &ptr);
            }
        "#);
    }

    #[test]
    fn test_interprocedural_indirect_reference() {
        check_alias(r#"
            struct Foo<'a> {
                g: u32,
                f: &'a u32,
            }

            pub fn bar<'a, 'b>(foo: &'a Foo<'b>) -> &'a &'b u32 {
                &foo.f
            }

            pub fn main() {
                let a = 1;
                let mut foo = Foo { g: 2, f: &a };
                let p = &foo;
                let q = bar(p);
                let r = &foo.f;
                may_alias(&q, &r);
            }
        "#);
    }

    #[test]
    fn test_vec_as_ptr() {
        check_alias(r#"
            pub fn main() {
                let mut a = Vec::new();
                a.push(1);
                let ptr = a.as_mut_ptr();
                let v = unsafe {
                    Vec::from_raw_parts(ptr, 2, 2)
                };
                let vptr = v.as_ptr();
                may_alias(&vptr, &ptr);
                may_alias(&vptr, &a);
                may_alias(&vptr, &v);
            }
        "#);
    }

    #[test]
    fn test_vec_get() {
        check_alias(r#"
            pub fn main() {
                let a = 1;
                let b = 2;
                let mut v1 = Vec::new();
                let mut v2 = Vec::new();
                v1.push(&a);
                v2.push(&b);
                let c = *v1.get(0).unwrap();
                may_alias(&c, &&a);
                no_alias(&c, &&b);
            }
        "#);
    }

    #[test]
    fn test_multiple_queries() {
        check_alias(r#"
            struct Foo {}
            pub fn box_foo() -> Box<Foo> {
                Box::new(Foo {})
            }

            pub fn main() {
                let b1 = box_foo();
                let b2 = box_foo();
                let p = &*b1;
                let q = &*b2;
                may_alias(&p, &b1);
                may_alias(&q, &b2);
            }
        "#);
    }

    #[test]
    fn test_activation() {
        check_alias(r#"
            pub fn main() {
                let a = 1;
                let b = 2;
                let c = 3;
                let mut p = &a;
                let mut q = &b;
                let mut x = &mut p;
                *x = &c;
                x = &mut q;
                let s = p;
                may_alias(&s, &&c);
            }
        "#);
    }

    #[test]
    fn test_recursive_fields() {
        check_alias(r#"
            use std::alloc::{alloc, Layout};
            use std::ptr::NonNull;
            use std::cell::Cell;

            #[allow(unused)]
            struct ChunkFooter {
                data: NonNull<u8>,
                ptr: Cell<NonNull<u8>>,
                allocated_bytes: usize,
            }

            unsafe fn new_chunk() -> Option<NonNull<ChunkFooter>> {
                unsafe {
                    let layout = Layout::new::<[u32; 4]>();
                    let allocated_bytes = layout.size();
                    let data = alloc(layout);
                    let data = NonNull::new(data)?;
                    let footer_ptr = data.as_ptr() as *mut ChunkFooter;
                    let ptr = Cell::new(NonNull::new_unchecked(footer_ptr as *mut u8));
                    std::ptr::write(
                        footer_ptr,
                        ChunkFooter {
                            data,
                            ptr,
                            allocated_bytes,
                        },
                    );
                    Some(NonNull::new_unchecked(footer_ptr))
                }
            }

            pub fn main() {
                let chunk = unsafe {
                    new_chunk().unwrap()
                };
                let data = unsafe { (*chunk.as_ptr()).data };
                may_alias(&chunk, &data);
            }
        "#);
    }
}
