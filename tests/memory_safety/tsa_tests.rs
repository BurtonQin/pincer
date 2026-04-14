#[cfg(test)]
mod test {
    use rustc_hir::def_id::DefId;
    use rustc_middle::mir::{Location, Place, StatementKind, TerminatorKind};
    use rustc_middle::ty::TyCtxt;

    use pincer::infoflow::data::access_path::AccessPath;
    use pincer::mir::function::FuncDef;
    use pincer::mir::Unit;
    use pincer::tsa::analyses::memory_safety_analysis::MemorySafetyAnalysis;
    use pincer::util::test_util::{
        compile, get_func, get_place, initialize_analysis_context,
    };

    /// Returns the `Place` and the `Location` of the first write for a named variable.
    fn get_var_init<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str) -> (Place<'tcx>, Location) {
        let place = get_place(tcx, def_id, name)
            .unwrap_or_else(|| panic!("Variable '{}' not found in {:?}", name, def_id));
        let body = tcx.optimized_mir(def_id);
        let local = place.local;
        for (bb, block_data) in body.basic_blocks.iter_enumerated() {
            for (stmt_idx, stmt) in block_data.statements.iter().enumerate() {
                if let StatementKind::Assign(box (lplace, _)) = &stmt.kind {
                    if lplace.local == local {
                        return (place, Location { block: bb, statement_index: stmt_idx });
                    }
                }
            }
            if let TerminatorKind::Call { destination, .. } = &block_data.terminator().kind {
                if destination.local == local {
                    return (place, Location {
                        block: bb,
                        statement_index: block_data.statements.len(),
                    });
                }
            }
        }
        panic!("No write found for {:?} in {:?}", local, def_id);
    }

    fn check_tsa(rust_code: &str, var_name: &str, expect_errors: bool) {
        compile(rust_code.to_string(), |tcx| {
            let acx = initialize_analysis_context(tcx);
            let main_def_id = get_func(tcx, "main").unwrap();
            let main_def = FuncDef::new_func_def(main_def_id, tcx.mk_args(&[]));

            let (place, location) = get_var_init(tcx, main_def_id, var_name);
            let path = AccessPath::from_rustc_place(&acx, main_def, &place);
            let start_unit = Unit::new(main_def, location);

            let mut analysis = MemorySafetyAnalysis::new(&acx);
            analysis.start_analysis(path, start_unit, true);

            assert_eq!(
                !analysis.error_seeds().is_empty(),
                expect_errors,
                "expected error seeds to be {}",
                if expect_errors { "non-empty" } else { "empty" }
            );
        });
    }

    #[test]
    fn drop_box_test() {
        check_tsa(r#"
            pub fn main() {
                let data = Box::new(42);
                let data_ptr: *const Box<i32> = &data as *const Box<i32>;

                {
                    let data2 = data;
                }

                unsafe {
                    let _value: i32 = **data_ptr;
                }
            }
        "#, "data", true);
    }

    #[test]
    fn drop_in_place_test() {
        check_tsa(r#"
            fn drop_vec_ptr<T>(ptr: *mut Vec<T>) {
                unsafe {
                    std::ptr::drop_in_place(ptr);
                }
            }

            pub fn main() {
                let mut v = vec![1, 2];
                let raw_ptr = &mut v as *mut Vec<i32>;
                drop_vec_ptr(raw_ptr);
            }
        "#, "v", true);
    }

    #[test]
    fn switch_test() {
        check_tsa(r#"
            pub fn rand_cond() -> bool {
                true
            }

            pub fn main() {
                let s1 = String::from("a tmp string");
                let mut s2;
                if rand_cond() {
                    drop(s1);
                    s2 = String::from("another tmp string");
                } else {
                    s2 = s1;
                }
            }
        "#, "s1", false);
    }

    #[test]
    fn vec_push_test() {
        check_tsa(r#"
            pub fn main() {
                let mut v = vec![1, 2, 3];
                v.push(4);
            }
        "#, "v", false);
    }

    #[test]
    fn vec_elem_test() {
        check_tsa(r#"
            pub fn main() {
                let s = String::from("Hello World");
                let mut v = vec![s];
                let p = v.get_mut(0).unwrap();
                let q: *mut String = p;
                unsafe {
                    std::ptr::drop_in_place(q);
                }
            }
        "#, "s", true);
    }

    #[test]
    fn unknown_call_test() {
        check_tsa(r#"
            pub fn main<F>(foo: F) where F: Fn(&String) -> &String {
                let s = String::from("Hello World");
                let r = foo(&s);
                let mut v = vec![s];
                let p = v.get_mut(0).unwrap();
                let q: *mut String = p;
                unsafe {
                    std::ptr::drop_in_place(q);
                }
            }
        "#, "s", true);
    }
}
