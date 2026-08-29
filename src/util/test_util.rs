use std::sync::Arc;
use rustc_interface::interface;
use rustc_middle::ty::TyCtxt;
use rustc_span::source_map::FileLoader;
use std::path::Path;
use std::{fs, io, io::Write};

use rustc_hir::def_id::DefId;
use rustc_middle::mir::{self, BasicBlock, Location, Operand, Place, Rvalue, StatementKind, TerminatorKind, VarDebugInfoContents};
use rustc_middle::ty::{GenericArgsRef, TyKind};

use crate::analysis_context::AnalysisContext;
use crate::infoflow::aliasing;
use crate::infoflow::aliasing::query::Query;
use crate::infoflow::data::access_path::AccessPath;
use crate::mir::borrowck_facts;
use crate::mir::function::FuncDef;
use crate::mir::unit::Unit;
use crate::rta::RapidTypeAnalysis;
use crate::util::{find_sysroot, pretty_print_mir};
use crate::util::options::AnalysisOptions;

pub const DUMMY_FILE_NAME: &str = "dummy.rs";

pub struct StringLoader(pub String);
impl FileLoader for StringLoader {
    fn file_exists(&self, _: &Path) -> bool {
        true
    }

    fn read_file(&self, _: &Path) -> io::Result<String> {
        Ok(self.0.clone())
    }

    fn read_binary_file(&self, path: &Path) -> io::Result<Arc<[u8]>> {
        Ok(fs::read(path)?.into())
    }

    fn current_directory(&self) -> io::Result<std::path::PathBuf> {
        std::env::current_dir()
    }
}

/// Perform the compilation, providing access to it's intermediates state to
/// the provided closure
pub fn compile(rust_source: String, f: impl for<'tcx> FnOnce(TyCtxt) + Send) {
    let mut callbacks = TestCallbacks {
        rust_source: Some(rust_source),
        callback: Some(move |tcx: TyCtxt<'_>| f(tcx)),
    };
    let args = [
        "rustc",
        DUMMY_FILE_NAME,
        "--crate-type",
        "lib",
        "-Zidentify-regions",
        "-Zmir-opt-level=0",
        "-Zmaximal-hir-to-mir-coverage",
        "--allow",
        "warnings",
        "--sysroot",
        &find_sysroot(),
    ]
    .into_iter()
    .map(str::to_owned)
    .collect::<Box<_>>();

    rustc_driver::run_compiler(&args, &mut callbacks);
}

struct TestCallbacks<Cb> {
    rust_source: Option<String>,
    callback: Option<Cb>,
}

impl<Cb> rustc_driver::Callbacks for TestCallbacks<Cb>
where
    Cb: FnOnce(TyCtxt<'_>),
{
    fn config(&mut self, config: &mut rustc_interface::Config) {
        if let Some(rust_source) = self.rust_source.take() {
            config.file_loader = Some(Box::new(StringLoader(rust_source)));
        }
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        tcx: TyCtxt<'tcx>,
    ) -> rustc_driver::Compilation {
        compiler.sess.dcx().abort_if_errors();
        if let Some(callback) = self.callback.take() {
            callback(tcx);
        }
        rustc_driver::Compilation::Stop
    }
}

pub fn get_func(tcx: TyCtxt<'_>, fn_name: &str) -> Option<DefId> {
    for local_def_id in tcx.hir_crate_items(()).definitions() {
        let def_kind = tcx.def_kind(local_def_id);
        if def_kind == rustc_hir::def::DefKind::Fn || def_kind == rustc_hir::def::DefKind::AssocFn {
            let item_name = tcx.item_name(local_def_id.to_def_id());
            if item_name.to_string() == fn_name {
                return Some(local_def_id.to_def_id());
            }
        }
    }
    return None;
}

pub fn get_place<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, name: &str) -> Option<Place<'tcx>> {
    let body = tcx.optimized_mir(def_id);
    body.var_debug_info
        .iter()
        .filter_map(|info| match info.value {
            VarDebugInfoContents::Place(place) => {
                if info.name.to_string() == name {
                    Some(place)
                } else {
                    None
                }
            }
            _ => None,
        })
        .collect::<Vec<Place<'tcx>>>()
        .first()
        .copied()
}

/// Returns the `Location` of the `Return` terminator in the given function's MIR.
pub fn return_location(tcx: TyCtxt<'_>, def_id: DefId) -> Location {
    let body = tcx.optimized_mir(def_id);
    for (bb, block_data) in body.basic_blocks.iter_enumerated() {
        if let TerminatorKind::Return = block_data.terminator().kind {
            return Location {
                block: bb,
                statement_index: block_data.statements.len(),
            };
        }
    }
    panic!("No return terminator found in {:?}", def_id);
}

pub fn get_callee_generic_args<'tcx>(tcx: TyCtxt<'tcx>, caller: &str, callee: &str) -> Option<&'tcx GenericArgsRef<'tcx>> {
    let caller_def_id = get_func(tcx, caller).unwrap();
    let callee_def_id = get_func(tcx, callee).unwrap();
    let caller_mir = tcx.optimized_mir(caller_def_id);
    for bb in caller_mir.basic_blocks.indices() {
        let mir::BasicBlockData {
            ref terminator,
            ..
        } = &caller_mir[bb];
        if let Some(mir::Terminator {
            ref kind,
            ..
        }) = *terminator {
            if let mir::TerminatorKind::Call {
                ref func,
                ..
            } = *kind {
                if let mir::Operand::Constant(constant) = func {
                    match constant.ty().kind() {
                        TyKind::FnDef(def_id, gen_args) => {
                            if *def_id == callee_def_id {
                                return Some(gen_args);
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
        
    }
    None
}

pub fn init_logger() {
    let _ = env_logger::builder().is_test(true).try_init();
}

pub fn initialize_analysis_context<'tcx>(tcx: TyCtxt<'tcx>) -> AnalysisContext<'tcx> {
    let mut acx = AnalysisContext::new(tcx, AnalysisOptions::default()).unwrap();
    let mut rta = RapidTypeAnalysis::new(&mut acx);
    rta.analyze();
    let call_graph = rta.call_graph;
    acx.set_up(call_graph);
    acx
}

/// Whether an alias assertion expects aliasing or non-aliasing.
#[derive(Debug, Clone, Copy)]
pub enum AliasAssertionKind {
    MayAlias,
    NoAlias,
}

/// An alias assertion extracted from MIR marker function calls.
#[derive(Debug)]
pub struct AliasAssertion<'tcx> {
    pub kind: AliasAssertionKind,
    pub location: Location,
    pub place_a: Place<'tcx>,
    pub place_b: Place<'tcx>,
}

/// Given a call argument operand (Move/Copy of a temporary), trace back through
/// the block's statements to find the original place being referenced.
/// Expects the temporary to have been assigned via `_tmp = &original_place`.
fn extract_ref_place<'tcx>(
    body: &mir::Body<'tcx>,
    bb: BasicBlock,
    operand: &Operand<'tcx>,
) -> Place<'tcx> {
    let tmp_local = match operand {
        Operand::Move(place) | Operand::Copy(place) => place.local,
        _ => panic!("Expected Move or Copy operand, got {:?}", operand),
    };

    let block_data = &body[bb];
    for stmt in block_data.statements.iter().rev() {
        if let StatementKind::Assign(box (lplace, rvalue)) = &stmt.kind {
            if lplace.local == tmp_local {
                if let Rvalue::Ref(_, _, ref_place) = rvalue {
                    return *ref_place;
                }
                panic!(
                    "Expected Ref rvalue for {:?}, got {:?}",
                    tmp_local, rvalue
                );
            }
        }
    }

    panic!(
        "Could not find assignment to {:?} in block {:?}",
        tmp_local, bb
    );
}

/// Scan a function's MIR for calls to `may_alias` and `no_alias` marker functions.
/// Returns the extracted assertions with their locations and argument places.
pub fn find_alias_assertions<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Vec<AliasAssertion<'tcx>> {
    let body = tcx.optimized_mir(def_id);
    let mut assertions = Vec::new();

    for (bb, block_data) in body.basic_blocks.iter_enumerated() {
        let terminator = block_data.terminator();
        if let TerminatorKind::Call {
            ref func,
            ref args,
            ..
        } = terminator.kind
        {
            if let Operand::Constant(constant) = func {
                if let TyKind::FnDef(callee_def_id, _) = constant.ty().kind() {
                    let name = tcx.item_name(*callee_def_id).to_string();
                    let kind = match name.as_str() {
                        "may_alias" => AliasAssertionKind::MayAlias,
                        "no_alias" => AliasAssertionKind::NoAlias,
                        _ => continue,
                    };

                    assert_eq!(
                        args.len(),
                        2,
                        "{} expects exactly 2 arguments",
                        name
                    );

                    let place_a = extract_ref_place(body, bb, &args[0].node);
                    let place_b = extract_ref_place(body, bb, &args[1].node);

                    let location = Location {
                        block: bb,
                        statement_index: block_data.statements.len(),
                    };

                    assertions.push(AliasAssertion {
                        kind,
                        location,
                        place_a,
                        place_b,
                    });
                }
            }
        }
    }

    assertions
}

/// Run alias analysis and check all `may_alias`/`no_alias` assertions found in
/// the given function's MIR. Panics if any assertion fails.
pub fn check_alias_assertions(acx: &AnalysisContext<'_>, func_def_id: DefId) {
    let tcx = acx.tcx;
    let func_def = FuncDef::new_func_def(func_def_id, tcx.mk_args(&[]));
    let assertions = find_alias_assertions(tcx, func_def_id);

    assert!(
        !assertions.is_empty(),
        "No may_alias/no_alias assertions found in {:?}",
        func_def_id
    );

    for assertion in &assertions {
        let query = Query::new(
            AccessPath::from_rustc_place(acx, func_def, &assertion.place_a),
            Unit::new(func_def, assertion.location),
        );
        let aliases = aliasing::find_aliases(acx, query);
        let place_b_path = AccessPath::from_rustc_place(acx, func_def, &assertion.place_b);

        match assertion.kind {
            AliasAssertionKind::MayAlias => {
                assert!(
                    aliases.contains(&place_b_path),
                    "may_alias assertion failed at {:?}: expected {:?} to alias {:?}\n  aliases: {:?}",
                    assertion.location,
                    assertion.place_a,
                    assertion.place_b,
                    aliases,
                );
            }
            AliasAssertionKind::NoAlias => {
                assert!(
                    !aliases.contains(&place_b_path),
                    "no_alias assertion failed at {:?}: expected {:?} NOT to alias {:?}\n  aliases: {:?}",
                    assertion.location,
                    assertion.place_a,
                    assertion.place_b,
                    aliases,
                );
            }
        }
    }

    println!(
        "All {} alias assertions passed for {:?}",
        assertions.len(),
        func_def_id,
    );
}

pub fn print_reachable_functions(acx: &AnalysisContext) {
    for func in acx.call_graph.as_ref().unwrap().reachable_funcs_iter() {
        if acx.tcx.is_mir_available(func.def_id) {
            pretty_print_mir(acx.tcx, func.def_id);
        } else {
            let mut stdout = std::io::stdout();
            stdout.write_fmt(format_args!("{:?}\nMir is unavailable\n", func.def_id)).unwrap();
            let _ = stdout.flush();
        }
    }
}



#[test]
fn test_with_tcx() {
    use rustc_hir::def::DefKind;

    let rust_code = r#"
        fn foo() {}
        fn bar(x: i32) -> i32 { x + 1 }
        fn baz() {}
    "#;

    compile(rust_code.to_string(), |tcx| {
        // Use tcx for analysis here
        for local_def_id in tcx.hir_crate_items(()).definitions() {
            let def_kind = tcx.def_kind(local_def_id);
            if def_kind == DefKind::Fn || def_kind == DefKind::AssocFn {
                let item_name = tcx.item_name(local_def_id.to_def_id());
                println!("Function name: {}", item_name);
            }
        }
    });
}
