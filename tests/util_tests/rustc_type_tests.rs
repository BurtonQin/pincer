// Tests for rustc type utilities: zero-sized types, zero byte offset projections,
// and generic type specialization.

#[cfg(test)]
mod test {
    use pincer::analysis_context::AnalysisContext;
    use pincer::util::options::AnalysisOptions;
    use pincer::util::test_util::{self, compile, get_func, get_place};
    use pincer::util::type_util;
    use rustc_hir::def_id::DefId;
    use rustc_middle::ty::{Ty, TyCtxt, TyKind};

    /// Returns the type of a named local variable in a function's MIR.
    fn get_var_ty<'tcx>(tcx: TyCtxt<'tcx>, func: DefId, var_name: &str) -> Ty<'tcx> {
        let body = tcx.optimized_mir(func);
        let place = get_place(tcx, func, var_name)
            .unwrap_or_else(|| panic!("variable '{}' not found in MIR", var_name));
        place.ty(body, tcx).ty
    }

    #[test]
    fn test_zero_sized_type() {
        let rust_code = r#"
            pub struct Foo {}
            pub struct Bar {
                f: (),
                g: (),
            }
            pub fn main() {
                let a = Foo {};
                let b = Bar { f: (), g: () };
                let c = ();
                let d = [2; 0];
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();

            assert!(type_util::is_zst(tcx, get_var_ty(tcx, main, "a")),
                "empty struct should be ZST");
            assert!(type_util::is_zst(tcx, get_var_ty(tcx, main, "b")),
                "struct with only () fields should be ZST");
            assert!(type_util::is_zst(tcx, get_var_ty(tcx, main, "c")),
                "unit type should be ZST");
            assert!(type_util::is_zst(tcx, get_var_ty(tcx, main, "d")),
                "zero-length array should be ZST");
        });
    }

    #[test]
    fn test_zero_byte_offset_projections() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
            }
            pub struct Bar<T> {
                f: T,
            }
            pub fn main() {
                let bar: Bar<i32> = Bar { f: 0 };
                let foo: Foo<i32> = Foo { f: bar };
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = AnalysisContext::new(tcx, AnalysisOptions::default()).unwrap();
            let main = get_func(tcx, "main").unwrap();

            let bar_projs = acx.get_zero_byte_offset_projections(get_var_ty(tcx, main, "bar"));
            assert_eq!(bar_projs.len(), 1);

            let foo_projs = acx.get_zero_byte_offset_projections(get_var_ty(tcx, main, "foo"));
            assert_eq!(foo_projs.len(), 2);
        });
    }

    #[test]
    fn test_specialized_generic_type() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
            }
            pub struct Bar<T> {
                f: T,
            }
            pub fn baz<T>(bar: Bar<T>) {
                let foo: Foo<T> = Foo { f: bar };
            }
            pub fn main() {
                let bar: Bar<i32> = Bar { f: 0 };
                baz(bar);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = AnalysisContext::new(tcx, AnalysisOptions::default()).unwrap();
            let baz = get_func(tcx, "baz").unwrap();
            let baz_gen_args = test_util::get_callee_generic_args(tcx, "main", "baz").unwrap();

            let bar_ty = type_util::specialize_generic_args(
                tcx,
                get_var_ty(tcx, baz, "bar"),
                baz_gen_args,
            );

            let bar_projs = acx.get_zero_byte_offset_projections(bar_ty);
            assert_eq!(bar_projs.len(), 1);
        });
    }

    #[test]
    fn test_is_reference_counting_pointer() {
        let rust_code = r#"
            use std::rc::Rc;
            use std::sync::Arc;

            fn test_function() {
                let rc_value = Rc::new(42);
                let arc_value = Arc::new(100);
                let box_value = Box::new(200);
                let regular_value = 300;
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let func = get_func(tcx, "test_function").unwrap();

            assert!(type_util::is_reference_counting_pointer(tcx, get_var_ty(tcx, func, "rc_value")),
                "Rc<i32> should be detected as reference counting pointer");
            assert!(type_util::is_reference_counting_pointer(tcx, get_var_ty(tcx, func, "arc_value")),
                "Arc<i32> should be detected as reference counting pointer");
            assert!(!type_util::is_reference_counting_pointer(tcx, get_var_ty(tcx, func, "box_value")),
                "Box<i32> should NOT be detected as reference counting pointer");
            assert!(!type_util::is_reference_counting_pointer(tcx, get_var_ty(tcx, func, "regular_value")),
                "i32 should NOT be detected as reference counting pointer");
        });
    }

    #[test]
    fn test_nested_generic_specialization() {
        let rust_code = r#"
            pub struct Foo<T> {
                f: Bar<T>,
            }
            pub struct Bar<T> {
                f: T,
            }
            pub fn baz<T>(bar: Bar<T>) {
                let foo: Foo<T> = Foo { f: bar };
            }
            pub fn main() {
                let bar: Bar<Option<i32>> = Bar { f: Some(0) };
                baz(bar);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let acx = AnalysisContext::new(tcx, AnalysisOptions::default()).unwrap();
            let baz = get_func(tcx, "baz").unwrap();
            let baz_gen_args = test_util::get_callee_generic_args(tcx, "main", "baz").unwrap();

            let foo_ty = type_util::specialize_generic_args(
                tcx,
                get_var_ty(tcx, baz, "foo"),
                baz_gen_args,
            );

            // Verify zero byte offset projections work on nested generic types
            let foo_projs = acx.get_zero_byte_offset_projections(foo_ty);
            assert!(!foo_projs.is_empty(),
                "specialized Foo<Option<i32>> should have zero byte offset projections");

            // Verify Foo::f is correctly specialized to Bar<Option<i32>>
            let TyKind::Adt(def, args) = foo_ty.kind() else {
                panic!("expected Foo to be an ADT type");
            };
            assert!(def.is_struct(), "Foo should be a struct");
            let field_ty = def.variants().iter().next().unwrap().fields[0usize.into()].ty(tcx, args);
            assert!(
                matches!(field_ty.kind(), TyKind::Adt(inner_def, _) if inner_def.is_struct()),
                "Foo::f should be a struct type (Bar<Option<i32>>)"
            );
        });
    }
}
