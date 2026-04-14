// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

//! The main routine of `pincer`.
//! 
//! Implemented as a stub that invokes the rust compiler with a call back to execute 
//! the analysis during rust compilation.

#![feature(rustc_private)]

extern crate rustc_driver;
extern crate rustc_interface;
extern crate rustc_middle;
extern crate rustc_session;

use log::*;
use std::env;

use rustc_driver::Compilation;
use rustc_interface::{interface, Queries};
use rustc_middle::ty::TyCtxt;

use pincer::analysis_context::AnalysisContext;
use pincer::rta::RapidTypeAnalysis;
use pincer::util::{self, options::{AnalysisOptions, AnalysisKind}, mem_watcher::MemoryWatcher, results_dumper};
use pincer::mir::borrowck_facts;
use pincer::tsa::analyses::memory_safety_analysis::{MemorySafetyAnalysis, vulnerable_pointer};

struct PincerCallbacks {
    /// Options provided to the analysis.
    options: AnalysisOptions,
}

impl PincerCallbacks {
    pub fn new(options: AnalysisOptions) -> PincerCallbacks {
        PincerCallbacks { options }
    }

    /// Runs Rapid Type Analysis to build the call graph.
    fn init_rta(acx: &mut AnalysisContext<'_>) {
        let mut rta = RapidTypeAnalysis::new(acx);
        rta.analyze();
        let call_graph = rta.call_graph;
        acx.set_up(call_graph);
    }

    fn run_memory_safety_analysis(acx: &mut AnalysisContext<'_>) {
        Self::init_rta(acx);
        let vulnerable_pointers = vulnerable_pointer::collect_vulnerable_pointers(acx);
        results_dumper::dump_call_graph(acx);
        results_dumper::dump_mir(acx);
        println!("Number of vulnerable pointers: {}", vulnerable_pointers.len());

        let mut analysis = MemorySafetyAnalysis::new(acx);
        for vp in &vulnerable_pointers {
            analysis.analyze_vulnerable_pointer(vp.clone());
        }

        analysis.report();
    }

    fn run_analysis(&mut self, _compiler: &interface::Compiler, tcx: TyCtxt<'_>) {
        let mut memory_watcher = MemoryWatcher::new();
        memory_watcher.start();
        let now = std::time::Instant::now();

        let Some(mut acx) = AnalysisContext::new(tcx, self.options.clone()) else {
            error!("AnalysisContext Initialization Failed");
            return;
        };

        match self.options.analysis_kind {
            AnalysisKind::RTA => {
                Self::init_rta(&mut acx);
                results_dumper::dump_call_graph(&acx);
                results_dumper::dump_mir(&acx);

                println!("Analysis time: {} seconds", now.elapsed().as_secs_f64());
                println!("Number of reachable functions: {}", acx.get_call_graph().func_to_node_id.len());
                memory_watcher.stop();
            }
            AnalysisKind::MemorySafety => {
                Self::run_memory_safety_analysis(&mut acx);
                println!("Analysis time: {} seconds", now.elapsed().as_secs_f64());
                memory_watcher.stop();
            }
        }
    }
}

impl rustc_driver::Callbacks for PincerCallbacks {
    /// Called before creating the compiler instance
    fn config(&mut self, config: &mut interface::Config) {
        let file_name = config.input.source_name().prefer_remapped_unconditionaly().to_string();
        debug!("Processing file: {}", file_name);
        config.override_queries = Some(borrowck_facts::override_queries);
    }

    /// Called after the compiler has completed all analysis passes and before it lowers MIR to LLVM IR.
    /// At this point the compiler is ready to tell us all it knows and we can proceed to do abstract
    /// interpretation of all of the functions that will end up in the compiler output.
    /// If this method returns false, the compilation will stop.
    fn after_analysis<'tcx>(
        &mut self,
        compiler: &interface::Compiler,
        queries: &'tcx Queries<'tcx>,
    ) -> Compilation {
        compiler.sess.dcx().abort_if_errors();
        queries
            .global_ctxt()
            .unwrap()
            .enter(|tcx| self.run_analysis(compiler, tcx));
        Compilation::Continue
    }
}

fn main() {
    let early_dcx =
        rustc_session::EarlyDiagCtxt::new(rustc_session::config::ErrorOutputType::default());

    // Initialize loggers.
    if env::var("RUSTC_LOG").is_ok() {
        rustc_driver::init_rustc_env_logger(&early_dcx);
    }
    if env::var("PINCER_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("PINCER_LOG")
            .write_style("PINCER_LOG_STYLE");
        env_logger::init_from_env(e);
    }

    // Get any options specified via the PINCER_FLAGS environment variable
    let mut options = AnalysisOptions::default();
    let pincer_flags = env::var("PINCER_FLAGS").unwrap_or_default();
    let pincer_args: Vec<String> = serde_json::from_str(&pincer_flags).unwrap_or_default();
    let rustc_args = options.parse_from_args(&pincer_args[..], true);

    // Let arguments supplied on the command line override the environment variable.
    let mut args = env::args_os()
        .enumerate()
        .map(|(i, arg)| {
            arg.into_string().unwrap_or_else(|arg| {
                early_dcx.early_fatal(format!("Argument {i} is not valid Unicode: {arg:?}"))
            })
        })
        .collect::<Vec<_>>();

    // Setting RUSTC_WRAPPER causes Cargo to pass 'rustc' as the first argument.
    // We're invoking the compiler programmatically, so we remove it if present.
    if args.len() > 1 && std::path::Path::new(&args[1]).file_stem() == Some("rustc".as_ref()) {
        args.remove(1);
    }

    let mut rustc_command_line_arguments = options.parse_from_args(&args[1..], false);
    info!("Pincer Options: {:?}", options);

    let result = rustc_driver::catch_fatal_errors(move || {
        // Add back the binary name
        rustc_command_line_arguments.insert(0, args[0].clone());

        // Add rustc arguments supplied via the PINCER_FLAGS environment variable
        rustc_command_line_arguments.extend(rustc_args);

        let sysroot: String = "--sysroot".into();
        if !rustc_command_line_arguments.iter().any(|arg| arg.starts_with(&sysroot)) {
            // Tell compiler where to find the std library and so on.
            // The compiler relies on the standard rustc driver to tell it, so we have to do likewise.
            rustc_command_line_arguments.push(sysroot);
            rustc_command_line_arguments.push(util::find_sysroot());
        }

        let always_encode_mir: String = "always-encode-mir".into();
        if !rustc_command_line_arguments.iter().any(|arg| arg.ends_with(&always_encode_mir))
        {
            // Tell compiler to emit MIR into crate for every function with a body.
            rustc_command_line_arguments.push("-Z".into());
            rustc_command_line_arguments.push(always_encode_mir);
        }
      
        let mut callbacks = PincerCallbacks::new(options);
        let compiler = rustc_driver::RunCompiler::new(&rustc_command_line_arguments, &mut callbacks);
        compiler.run()
    });

    let exit_code = match result {
        Ok(_) => rustc_driver::EXIT_SUCCESS,
        Err(_) => rustc_driver::EXIT_FAILURE,
    };

    std::process::exit(exit_code);
}
