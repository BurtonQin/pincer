// Tests for drop shim MIR body generation.
// Prints the MIR of drop shims for various types so we can inspect the structure.

#[cfg(test)]
mod test {
    extern crate rustc_span;
    use pincer::mir::drop_shim;
    use pincer::util::test_util::{compile, get_func};
    use rustc_hir::def_id::DefId;
    use rustc_hir::LangItem;
    use rustc_middle::mir::pretty::MirWriter;
    use rustc_middle::mir::Body;
    use rustc_middle::ty::{self, Instance, Ty, TyCtxt, TyKind};

    /// Returns the type of a named local variable in a function's MIR.
    fn get_var_ty<'tcx>(tcx: TyCtxt<'tcx>, func: DefId, var_name: &str) -> Ty<'tcx> {
        let body = tcx.optimized_mir(func);
        let place = pincer::util::test_util::get_place(tcx, func, var_name)
            .unwrap_or_else(|| panic!("variable '{}' not found in MIR", var_name));
        place.ty(body, tcx).ty
    }

    /// Pretty-prints a MIR body using rustc's built-in MIR printer.
    fn dump_drop_shim_body<'tcx>(tcx: TyCtxt<'tcx>, label: &str, ty: Ty<'tcx>, body: &Body<'tcx>) {
        println!("\n===== Drop shim for: {} (type: {:?}) =====", label, ty);
        let mut buf = Vec::new();
        MirWriter::new(tcx).write_mir_fn(body, &mut buf).unwrap();
        println!("{}", String::from_utf8(buf).unwrap());
        println!("===== End drop shim for: {} =====\n", label);
    }

    #[test]
    fn test_drop_shim_simple_struct() {
        let rust_code = r#"
            pub struct Foo {
                a: String,
                b: Vec<i32>,
            }
            pub fn main() {
                let foo = Foo {
                    a: String::from("hello"),
                    b: vec![1, 2, 3],
                };
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "foo");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "Foo { String, Vec<i32> }", ty, body);

            // Should have basic blocks for dropping fields
            assert!(body.basic_blocks.len() > 1,
                "drop shim should have more than just a return block");
        });
    }

    #[test]
    fn test_drop_shim_with_drop_impl() {
        let rust_code = r#"
            pub struct Bar {
                data: Vec<u8>,
            }
            impl Drop for Bar {
                fn drop(&mut self) {
                    // custom drop
                }
            }
            pub fn main() {
                let bar = Bar { data: vec![1] };
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "bar");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "Bar (impl Drop)", ty, body);

            // Should have a Call terminator for the custom Drop::drop
            let has_call = body.basic_blocks.iter().any(|bb| {
                matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::Call { .. })
            });
            assert!(has_call, "drop shim with Drop impl should have a Call terminator");
        });
    }

    #[test]
    fn test_drop_shim_enum() {
        let rust_code = r#"
            pub enum MyEnum {
                A(String),
                B(Vec<i32>),
                C,
            }
            pub fn main() {
                let e: MyEnum = MyEnum::A(String::from("test"));
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "e");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "MyEnum { A(String), B(Vec<i32>), C }", ty, body);

            // Enum drop shim should have a SwitchInt on the discriminant
            let has_switch = body.basic_blocks.iter().any(|bb| {
                matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::SwitchInt { .. })
            });
            assert!(has_switch,
                "enum drop shim should have SwitchInt on discriminant");
        });
    }

    #[test]
    fn test_drop_shim_nested_struct() {
        let rust_code = r#"
            pub struct Inner {
                s: String,
            }
            pub struct Outer {
                inner: Inner,
                v: Vec<u8>,
            }
            pub fn main() {
                let o = Outer {
                    inner: Inner { s: String::from("hi") },
                    v: vec![1],
                };
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "o");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "Outer { Inner { String }, Vec<u8> }", ty, body);
        });
    }

    #[test]
    fn test_drop_shim_box() {
        let rust_code = r#"
            pub fn main() {
                let b: Box<Vec<i32>> = Box::new(vec![1, 2, 3]);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "b");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "Box<Vec<i32>>", ty, body);
        });
    }

    #[test]
    fn test_drop_shim_no_drop() {
        let rust_code = r#"
            pub struct NoDrop {
                x: i32,
                y: f64,
            }
            pub fn main() {
                let nd = NoDrop { x: 1, y: 2.0 };
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "nd");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "NoDrop { i32, f64 }", ty, body);

            // A type that doesn't need drop should have a noop shim (just return)
            assert_eq!(body.basic_blocks.len(), 1,
                "noop drop shim should have exactly 1 block (return)");
        });
    }

    #[test]
    fn test_drop_shim_tuple() {
        let rust_code = r#"
            pub fn main() {
                let t: (String, Vec<i32>, i32) = (String::from("a"), vec![1], 42);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "t");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "(String, Vec<i32>, i32)", ty, body);
        });
    }

    #[test]
    fn test_drop_shim_rc() {
        let rust_code = r#"
            use std::rc::Rc;
            pub fn main() {
                let r: Rc<String> = Rc::new(String::from("hello"));
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let main = get_func(tcx, "main").unwrap();
            let ty = get_var_ty(tcx, main, "r");
            let body = drop_shim::resolve_drop_shim_body(tcx, ty);
            dump_drop_shim_body(tcx, "Rc<String>", ty, body);
        });
    }

    /// Non-concrete types (containing generic params) don't have a rustc drop shim.
    /// `drop_shim_body()` falls back to a manually constructed body for these.
    /// This happens when RTA encounters a generic type like `Vec<T>` where T
    /// is not yet monomorphized.
    #[test]
    fn test_drop_shim_generic_struct_fallback() {
        let rust_code = r#"
            pub struct Wrapper<T> {
                data: Vec<T>,
                name: String,
            }
            pub fn consume<T>(w: Wrapper<T>) {
                drop(w);
            }
            pub fn main() {
                let w = Wrapper { data: vec![1i32], name: String::from("test") };
                consume(w);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            // Get the unmonomorphized type Wrapper<T> from the generic function
            let consume = get_func(tcx, "consume").unwrap();
            let generic_ty = get_var_ty(tcx, consume, "w");
            println!("\nGeneric type: {:?}", generic_ty);
            println!("is_concrete: {}", pincer::util::type_util::is_concrete(generic_ty.kind()));

            // This type is NOT concrete (contains type param T), so rustc can't
            // generate a drop shim. Our fallback body is used instead.
            assert!(!pincer::util::type_util::is_concrete(generic_ty.kind()),
                "Wrapper<T> should NOT be concrete");

            let fallback_body = drop_shim::resolve_drop_shim_body(tcx, generic_ty);
            dump_drop_shim_body(tcx, "Wrapper<T> (fallback - non-concrete)", generic_ty, fallback_body);

            // The fallback body should have Drop terminators for fields that need drop
            let has_drop = fallback_body.basic_blocks.iter().any(|bb| {
                matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::Drop { .. })
            });
            assert!(has_drop,
                "fallback body should have Drop terminators for droppable fields");

            // Now compare with the concrete (monomorphized) version: Wrapper<i32>
            let main = get_func(tcx, "main").unwrap();
            let concrete_ty = get_var_ty(tcx, main, "w");
            assert!(pincer::util::type_util::is_concrete(concrete_ty.kind()),
                "Wrapper<i32> should be concrete");

            let rustc_body = drop_shim::resolve_drop_shim_body(tcx, concrete_ty);
            dump_drop_shim_body(tcx, "Wrapper<i32> (rustc native shim)", concrete_ty, rustc_body);
        });
    }

    /// Generic enum types also use the fallback body.
    #[test]
    fn test_drop_shim_generic_enum_fallback() {
        let rust_code = r#"
            pub enum Either<L, R> {
                Left(L),
                Right(R),
            }
            pub fn consume<L, R>(e: Either<L, R>) {
                drop(e);
            }
            pub fn main() {
                let e: Either<String, Vec<i32>> = Either::Left(String::from("hi"));
                consume(e);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let consume = get_func(tcx, "consume").unwrap();
            let generic_ty = get_var_ty(tcx, consume, "e");

            assert!(!pincer::util::type_util::is_concrete(generic_ty.kind()),
                "Either<L, R> should NOT be concrete");

            let fallback_body = drop_shim::resolve_drop_shim_body(tcx, generic_ty);
            dump_drop_shim_body(tcx, "Either<L, R> (fallback)", generic_ty, fallback_body);

            // Compare with concrete version
            let main = get_func(tcx, "main").unwrap();
            let concrete_ty = get_var_ty(tcx, main, "e");
            let rustc_body = drop_shim::resolve_drop_shim_body(tcx, concrete_ty);
            dump_drop_shim_body(tcx, "Either<String, Vec<i32>> (rustc native)", concrete_ty, rustc_body);

            // Rustc's enum shim should have SwitchInt, fallback won't
            let rustc_has_switch = rustc_body.basic_blocks.iter().any(|bb| {
                matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::SwitchInt { .. })
            });
            assert!(rustc_has_switch,
                "rustc native enum shim should have SwitchInt");
        });
    }

    /// Types with Drop impl + generic params use the fallback body
    /// which includes both the Drop::drop call and field drops.
    #[test]
    fn test_drop_shim_generic_with_drop_impl_fallback() {
        let rust_code = r#"
            pub struct Guard<T> {
                data: Vec<T>,
            }
            impl<T> Drop for Guard<T> {
                fn drop(&mut self) {
                    // cleanup
                }
            }
            pub fn consume<T>(g: Guard<T>) {
                drop(g);
            }
            pub fn main() {
                let g = Guard { data: vec![1i32] };
                consume(g);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let consume = get_func(tcx, "consume").unwrap();
            let generic_ty = get_var_ty(tcx, consume, "g");

            let fallback_body = drop_shim::resolve_drop_shim_body(tcx, generic_ty);
            dump_drop_shim_body(tcx, "Guard<T> (fallback with Drop impl)", generic_ty, fallback_body);

            // Should have both a Call (for Drop::drop) and a Drop terminator (for fields)
            let has_call = fallback_body.basic_blocks.iter().any(|bb| {
                matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::Call { .. })
            });
            let has_drop = fallback_body.basic_blocks.iter().any(|bb| {
                matches!(bb.terminator().kind, rustc_middle::mir::TerminatorKind::Drop { .. })
            });
            assert!(has_call, "fallback with Drop impl should have a Call terminator");
            assert!(has_drop, "fallback should also drop fields");

            // Compare with concrete
            let main = get_func(tcx, "main").unwrap();
            let concrete_ty = get_var_ty(tcx, main, "g");
            let rustc_body = drop_shim::resolve_drop_shim_body(tcx, concrete_ty);
            dump_drop_shim_body(tcx, "Guard<i32> (rustc native)", concrete_ty, rustc_body);
        });
    }

    /// Try to resolve a drop shim via rustc directly (bypassing is_concrete check).
    /// Returns Ok(body) if rustc can generate it, Err(reason) if it panics/fails.
    fn try_rustc_shim<'tcx>(tcx: TyCtxt<'tcx>, ty: Ty<'tcx>) -> Result<&'tcx Body<'tcx>, String> {
        let def_id = tcx.require_lang_item(LangItem::DropInPlace, rustc_span::DUMMY_SP);
        std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let args = tcx.mk_args(&[ty.into()]);
            let typing_env = ty::TypingEnv::fully_monomorphized();
            match Instance::try_resolve(tcx, typing_env, def_id, args) {
                Ok(Some(instance)) => {
                    let body = tcx.instance_mir(instance.def);
                    Ok(body)
                }
                Ok(None) => Err("try_resolve returned None".to_string()),
                Err(e) => Err(format!("try_resolve error: {:?}", e)),
            }
        }))
        .unwrap_or_else(|e| Err(format!("ICE/panic: {:?}", e)))
    }

    /// Test whether is_concrete() is too strict.
    /// For types like Box<Vec<T>>, Vec<T>, String — check if rustc can actually
    /// generate a shim even when is_concrete() says no.
    #[test]
    fn test_is_concrete_strictness() {
        let rust_code = r#"
            use std::collections::HashMap;

            pub struct Wrapper<T> {
                boxed_vec: Box<Vec<T>>,
                vec: Vec<T>,
                string: String,
                raw: *mut T,
            }

            pub struct Nested<T> {
                inner: Vec<Vec<T>>,
            }

            pub fn consume<T>(w: Wrapper<T>, n: Nested<T>) {
                drop(w);
                drop(n);
            }

            pub fn main() {
                let w = Wrapper {
                    boxed_vec: Box::new(vec![1i32]),
                    vec: vec![2],
                    string: String::from("hi"),
                    raw: std::ptr::null_mut(),
                };
                let n = Nested { inner: vec![vec![1i32]] };
                consume(w, n);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let consume = get_func(tcx, "consume").unwrap();
            let body = tcx.optimized_mir(consume);

            // Collect all local types from the generic function
            println!("\n===== is_concrete() strictness analysis =====");
            for (local, decl) in body.local_decls.iter_enumerated() {
                let ty = decl.ty;
                let is_concrete = pincer::util::type_util::is_concrete(ty.kind());
                let rustc_result = try_rustc_shim(tcx, ty);
                let rustc_can = rustc_result.is_ok();

                // Only print interesting cases
                if !is_concrete || !rustc_can {
                    println!(
                        "  {:?}: {:?}\n    is_concrete={}, rustc_can_generate={}{}",
                        local, ty, is_concrete, rustc_can,
                        if !is_concrete && rustc_can { " <-- is_concrete too strict!" } else { "" }
                    );
                    if let Ok(shim_body) = &rustc_result {
                        dump_drop_shim_body(tcx, &format!("{:?} (rustc succeeded despite !is_concrete)", ty), ty, shim_body);
                    }
                    if let Err(ref reason) = rustc_result {
                        println!("    rustc failure reason: {}", reason);
                    }
                }
            }

            // Specifically test sub-types that appear inside Wrapper<T>
            let wrapper_ty = get_var_ty(tcx, consume, "w");
            println!("\n--- Testing field types of Wrapper<T> ---");

            // Get the ADT fields
            if let rustc_middle::ty::TyKind::Adt(adt_def, args) = wrapper_ty.kind() {
                for field in adt_def.all_fields() {
                    let field_ty = field.ty(tcx, args);
                    let is_concrete = pincer::util::type_util::is_concrete(field_ty.kind());
                    let rustc_result = try_rustc_shim(tcx, field_ty);
                    let rustc_can = rustc_result.is_ok();

                    println!(
                        "  {}: {:?}\n    is_concrete={}, rustc_can_generate={}{}",
                        field.name, field_ty, is_concrete, rustc_can,
                        if !is_concrete && rustc_can { " <-- TOO STRICT" } else { "" }
                    );
                    if let Ok(shim_body) = &rustc_result {
                        if !is_concrete {
                            dump_drop_shim_body(tcx, &format!("{} (rustc OK despite !is_concrete)", field.name), field_ty, shim_body);
                        }
                    }
                    if let Err(ref reason) = rustc_result {
                        println!("    failure: {}", reason);
                    }
                }
            }
            println!("===== End strictness analysis =====\n");
        });
    }

    /// Specifically test Box<Vec<T>>, Vec<T>, and their inner types
    /// to see where exactly rustc fails in the type hierarchy.
    #[test]
    fn test_shim_availability_type_hierarchy() {
        let rust_code = r#"
            pub fn consume<T>(
                boxed_vec: Box<Vec<T>>,
                vec: Vec<T>,
                boxed_str: Box<String>,
                option: Option<T>,
                tuple: (T, String),
            ) {
                drop(boxed_vec);
                drop(vec);
                drop(boxed_str);
                drop(option);
                drop(tuple);
            }
            pub fn main() {
                consume(
                    Box::new(vec![1i32]),
                    vec![2],
                    Box::new(String::from("hi")),
                    Some(3),
                    (4, String::from("x")),
                );
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let consume = get_func(tcx, "consume").unwrap();

            let types_to_test: Vec<(&str, Ty)> = vec![
                ("Box<Vec<T>>", get_var_ty(tcx, consume, "boxed_vec")),
                ("Vec<T>", get_var_ty(tcx, consume, "vec")),
                ("Box<String>", get_var_ty(tcx, consume, "boxed_str")),
                ("Option<T>", get_var_ty(tcx, consume, "option")),
                ("(T, String)", get_var_ty(tcx, consume, "tuple")),
            ];

            println!("\n===== Drop shim availability for partially-generic types =====");
            for (label, ty) in &types_to_test {
                let is_concrete = pincer::util::type_util::is_concrete(ty.kind());
                let rustc_result = try_rustc_shim(tcx, *ty);
                let status = match (&rustc_result, is_concrete) {
                    (Ok(_), true) => "OK (concrete, rustc works)",
                    (Ok(_), false) => "OVERLY STRICT (not concrete, but rustc works!)",
                    (Err(_), true) => "BUG (concrete, but rustc fails!)",
                    (Err(_), false) => "OK (not concrete, rustc fails as expected)",
                };
                println!("  {:<20} is_concrete={:<5} rustc={:<5} => {}",
                    label, is_concrete,
                    if rustc_result.is_ok() { "OK" } else { "FAIL" },
                    status
                );
                if let Ok(body) = rustc_result {
                    if !is_concrete {
                        dump_drop_shim_body(tcx, &format!("{} (rustc works despite !is_concrete)", label), *ty, body);
                    }
                }
                if let Err(ref reason) = rustc_result {
                    println!("    reason: {}", reason);
                }
            }
            println!("===== End availability test =====\n");
        });
    }

    /// Test that drop_shim_body correctly handles types with alias projections
    /// by using the fallback body, while using rustc's native shim for other
    /// non-concrete types (Param, Dynamic, etc.).
    #[test]
    fn test_alias_projection_uses_fallback() {
        let rust_code = r#"
            pub trait MyTrait {
                type Assoc;
            }

            pub struct WithAssoc<A: MyTrait> {
                data: Vec<A::Assoc>,
                raw: A,
            }

            pub struct NestedAssoc<A: MyTrait> {
                inner: Box<A::Assoc>,
            }

            pub struct Simple<T> {
                val: T,
            }

            impl MyTrait for String {
                type Assoc = i32;
            }

            pub fn with_assoc_type<A: MyTrait>(w: WithAssoc<A>, n: NestedAssoc<A>) {
                drop(w);
                drop(n);
            }

            pub fn with_param<T>(s: Simple<T>) {
                drop(s);
            }

            pub fn main() {
                let w = WithAssoc::<String> { data: vec![1i32], raw: String::from("hi") };
                let n = NestedAssoc::<String> { inner: Box::new(42) };
                with_assoc_type(w, n);
                let s = Simple { val: 42i32 };
                with_param(s);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            println!("\n===== Alias projection handling =====\n");

            // 1. Simple<T> — has Param but no Alias, should use rustc native shim
            let with_param = get_func(tcx, "with_param").unwrap();
            let simple_t = get_var_ty(tcx, with_param, "s");
            println!("Simple<T>: contains_alias=false (expected)");
            let body = drop_shim::resolve_drop_shim_body(tcx, simple_t);
            dump_drop_shim_body(tcx, "Simple<T> (rustc native)", simple_t, body);
            // Should not use fallback since there's no alias projection
            assert!(body.basic_blocks.len() > 0, "Simple<T> body should have blocks");

            // 2. WithAssoc<A> — contains Alias projection, should use fallback
            let with_assoc = get_func(tcx, "with_assoc_type").unwrap();
            let with_assoc_ty = get_var_ty(tcx, with_assoc, "w");
            println!("WithAssoc<A> has Alias in fields:");
            if let TyKind::Adt(adt_def, args) = with_assoc_ty.kind() {
                for field in adt_def.all_fields() {
                    let field_ty = field.ty(tcx, args);
                    println!("  field '{}': {:?}, is_alias={}", field.name, field_ty,
                        matches!(field_ty.kind(), TyKind::Alias(..)));
                }
            }
            let body = drop_shim::resolve_drop_shim_body(tcx, with_assoc_ty);
            dump_drop_shim_body(tcx, "WithAssoc<A> (fallback)", with_assoc_ty, body);
            // Fallback body has no cleanup blocks
            assert!(!body.basic_blocks.iter().any(|bb| bb.is_cleanup),
                "WithAssoc<A> should use fallback (no cleanup blocks)");

            // 3. NestedAssoc<A> — contains Alias via Box<A::Assoc>, should use fallback
            let nested_assoc_ty = get_var_ty(tcx, with_assoc, "n");
            let body = drop_shim::resolve_drop_shim_body(tcx, nested_assoc_ty);
            dump_drop_shim_body(tcx, "NestedAssoc<A> (fallback)", nested_assoc_ty, body);
            assert!(!body.basic_blocks.iter().any(|bb| bb.is_cleanup),
                "NestedAssoc<A> should use fallback (no cleanup blocks)");

            // 4. Concrete monomorphized version should use rustc native
            let main = get_func(tcx, "main").unwrap();
            let concrete_ty = get_var_ty(tcx, main, "w");
            let body = drop_shim::resolve_drop_shim_body(tcx, concrete_ty);
            dump_drop_shim_body(tcx, "WithAssoc<String> (rustc native)", concrete_ty, body);
            // Concrete type — no alias projection, gets rustc native shim
            assert!(body.basic_blocks.len() > 0,
                "WithAssoc<String> should get a valid body");

            println!("===== End alias projection handling =====\n");
        });
    }

    /// Test that non-concrete types WITHOUT alias projections now get
    /// rustc's native shim (with proper unwind/cleanup blocks).
    #[test]
    fn test_param_types_get_native_shim() {
        let rust_code = r#"
            pub fn consume<T>(
                vec: Vec<T>,
                boxed_vec: Box<Vec<T>>,
                option: Option<T>,
                tuple: (T, String),
            ) {
                drop(vec);
                drop(boxed_vec);
                drop(option);
                drop(tuple);
            }
            pub fn main() {
                consume(vec![1i32], Box::new(vec![2]), Some(3), (4, String::from("x")));
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            let consume = get_func(tcx, "consume").unwrap();

            println!("\n===== Param types now get native shims =====\n");
            for var_name in &["vec", "boxed_vec", "option", "tuple"] {
                let ty = get_var_ty(tcx, consume, var_name);
                let body = drop_shim::resolve_drop_shim_body(tcx, ty);
                dump_drop_shim_body(tcx, &format!("{} (should be native)", var_name), ty, body);

                // All these should get rustc native shims now (no alias projection)
                // Verify the body is valid and was produced without panic
                assert!(body.basic_blocks.len() > 0,
                    "{} should get a valid drop shim body", var_name);
                let has_cleanup = body.basic_blocks.iter().any(|bb| bb.is_cleanup);
                println!("  {} has_cleanup={} blocks={}", var_name, has_cleanup, body.basic_blocks.len());
            }
            println!("===== End param types test =====\n");
        });
    }

    /// Test dyn Trait types and other edge cases
    #[test]
    fn test_dyn_trait_drop_shim() {
        let rust_code = r#"
            pub trait Animal {
                fn speak(&self);
            }

            pub fn consume_boxed_dyn(b: Box<dyn Animal>) {
                drop(b);
            }

            pub fn consume_ref_dyn(r: &dyn Animal) {
                let _ = r;
            }

            struct Dog;
            impl Animal for Dog {
                fn speak(&self) {}
            }

            pub fn main() {
                let d = Dog;
                let b: Box<dyn Animal> = Box::new(d);
                consume_boxed_dyn(b);
            }
        "#;

        compile(rust_code.to_string(), |tcx| {
            println!("\n===== dyn Trait drop shim tests =====\n");

            let consume_boxed = get_func(tcx, "consume_boxed_dyn").unwrap();
            let boxed_dyn_ty = get_var_ty(tcx, consume_boxed, "b");
            println!("  Box<dyn Animal>: kind={:?}", boxed_dyn_ty.kind());
            println!("  is_concrete={}", pincer::util::type_util::is_concrete(boxed_dyn_ty.kind()));

            let result = try_rustc_shim(tcx, boxed_dyn_ty);
            println!("  rustc={}", if result.is_ok() { "OK" } else { "FAIL" });
            if let Err(ref e) = result { println!("    reason: {}", e); }
            if let Ok(body) = result {
                dump_drop_shim_body(tcx, "Box<dyn Animal>", boxed_dyn_ty, body);
            }

            // Also check the inner dyn Animal type
            if let TyKind::Adt(_, args) = boxed_dyn_ty.kind() {
                let inner_ty = args[0].expect_ty();
                println!("\n  dyn Animal: kind matches Dynamic={}", matches!(inner_ty.kind(), TyKind::Dynamic(..)));
                println!("  is_concrete={}", pincer::util::type_util::is_concrete(inner_ty.kind()));
                let result = try_rustc_shim(tcx, inner_ty);
                println!("  rustc={}", if result.is_ok() { "OK" } else { "FAIL" });
                if let Err(ref e) = result { println!("    reason: {}", e); }
            }

            println!("\n===== End dyn Trait tests =====\n");
        });
    }
}
