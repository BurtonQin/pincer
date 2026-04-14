// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

//! Analysis options.

use std::fmt;
use std::path::PathBuf;
use std::str::FromStr;
use itertools::Itertools;
use clap::{Arg, Command};
use clap::error::ErrorKind;

/// The kind of analysis to perform.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum AnalysisKind {
    /// Rapid Type Analysis only — build call graph, dump it, and print stats.
    RTA,
    /// Full memory-safety pipeline (default).
    MemorySafety,
}

impl Default for AnalysisKind {
    fn default() -> Self {
        AnalysisKind::MemorySafety
    }
}

impl fmt::Display for AnalysisKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            AnalysisKind::RTA => write!(f, "rta"),
            AnalysisKind::MemorySafety => write!(f, "memory-safety"),
        }
    }
}

impl FromStr for AnalysisKind {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "rta" => Ok(AnalysisKind::RTA),
            "memory-safety" | "ms" => Ok(AnalysisKind::MemorySafety),
            other => Err(format!("unknown analysis kind: '{other}'")),
        }
    }
}

const PINCER_USAGE: &str = r#"pincer [OPTIONS] INPUT -- [RUSTC OPTIONS]"#;
const DEFAULT_DEREF_LIMIT: usize = 5;
const CALL_GRAPH_OUTPUT_SUFFIX: &str = "callgraph.dot";
const MIR_OUTPUT_SUFFIX: &str = "mir.txt";

/// The version information from Cargo.toml.
fn version() -> &'static str {
    let version_info = rustc_tools_util::get_version_info!();
    let version = format!("v{}.{}.{}", version_info.major, version_info.minor, version_info.patch);
    Box::leak(version.into_boxed_str())
}


/// Creates the clap::Command metadata for argument parsing.
fn make_options_parser() -> Command<'static> {
    let parser = Command::new("pincer")
        .no_binary_name(true)
        .override_usage(PINCER_USAGE)
        .version(version())
        .arg(Arg::new("entry-func")
            .long("entry-func")
            .takes_value(true) 
            .help("The name of entry function from which the analysis begins."))
        .arg(Arg::new("output-dir")
            .long("output-dir")
            .takes_value(true) 
            .help("The directory to store the output files."))
        .arg(Arg::new("deref-limit")
            .long("deref-limit")
            .takes_value(true)
            .value_parser(clap::value_parser!(usize))
            .help("The maximum number of dereferences in an access path."))
        .arg(Arg::new("analyze-rc-drop")
            .long("analyze-rc-drop")
            .takes_value(false)
            .help("Including the analyses of drops for reference counting pointers."))
        .arg(Arg::new("disable-strong-updates")
            .long("disable-strong-updates")
            .takes_value(false)
            .help("Do not apply strong updates for indirect kills."))
        .arg(Arg::new("disable-msa-axm")
            .long("disable-msa-axm")
            .takes_value(false)
            .help("Do not apply AXM check for safely termination."))
        .arg(Arg::new("dump-call-graph")
            .long("dump-call-graph")
            .takes_value(false)
            .help("Dump the call graph in DOT format."))
        .arg(Arg::new("dump-mir")
            .long("dump-mir")
            .takes_value(false)
            .help("Dump the mir of reachable functions."))
        .arg(Arg::new("skip-generics")
            .long("skip-generics")
            .takes_value(false)
            .help("Ignore generic functions when collecting the entry functions."))
        .arg(Arg::new("analysis")
            .long("analysis")
            .short('a')
            .takes_value(true)
            .possible_values(["rta", "memory-safety", "ms"])
            .default_value("memory-safety")
            .help("The analysis mode to run."))
        .arg(Arg::new("INPUT")
            .multiple(true)
            .help("The input file to be analyzed.")
        );
        parser
}

#[derive(Clone, Debug)]
pub struct AnalysisOptions {
    pub entry_func: Option<String>,
    pub crate_name: Option<String>,
    pub output_dir: PathBuf,
    pub analysis_kind: AnalysisKind,
    pub skip_generics: bool,
    pub access_path_deref_limit: usize,
    pub ignore_rc_drop: bool,
    pub msa_strong_updates: bool,
    pub msa_axm_check: bool,
    pub dump_mir: bool,
    pub dump_call_graph: bool,
}

impl Default for AnalysisOptions {
    fn default() -> Self {
        Self {
            entry_func: None,
            crate_name: None,
            output_dir: std::env::current_dir()
                .unwrap_or_else(|_| std::path::PathBuf::from(".")),
            analysis_kind: AnalysisKind::default(),
            skip_generics: false,
            access_path_deref_limit: DEFAULT_DEREF_LIMIT,
            ignore_rc_drop: true,
            msa_strong_updates: true,
            msa_axm_check: true,
            dump_mir: false,
            dump_call_graph: false,
        }
    }
}

impl AnalysisOptions {
    /// Parses options from a list of strings. Any content beyond the leftmost `--` token
    /// will be returned (excluding this token).
    pub fn parse_from_args(&mut self, args: &[String], from_env: bool) -> Vec<String> {
        if let Some(crate_name) = get_arg_flag_value(args, "--crate-name") {
            self.crate_name = Some(crate_name);
        }

        let mut pincer_args_end = args.len();
        let mut rustc_args_start = 0;
        if let Some((p, _)) = args.iter().find_position(|s| s.as_str() == "--") {
            pincer_args_end = p;
            rustc_args_start = p + 1;
        }
        let pincer_args = &args[0..pincer_args_end];
        let matches = if !from_env && rustc_args_start == 0 {
            // The arguments may not be intended for Pincer and may get here via some tool, so do not 
            // report errors here, but just assume that the arguments were not meant for Pincer.
            match make_options_parser().try_get_matches_from(pincer_args.iter())
            {
                Ok(matches) => {
                    // Looks like these are Pincer options after all and there are no rustc options.
                    rustc_args_start = args.len();
                    matches
                }
                Err(e) => match e.kind() {
                    ErrorKind::DisplayHelp => {
                        eprintln!("{e}");
                        return args.to_vec();
                    }
                    ErrorKind::UnknownArgument => {
                        // Just send all of the arguments to rustc.
                        // Note that this means that Pincer options and rustc options must always
                        // be separated by --. I.e. any Pincer options present in arguments list
                        // will stay unknown to Pincer and will make rustc unhappy.
                        return args.to_vec();
                    }
                    _ => {
                        e.exit();
                    }
                },
            }
        } else {
            // This will display error diagnostics for arguments that are not valid for Pincer.
            match make_options_parser().try_get_matches_from(pincer_args.iter()) {
                Ok(matches) => {
                    if rustc_args_start == 0 {
                        rustc_args_start = args.len();
                    }
                    matches
                }
                Err(e) => {
                    e.exit();
                }
            }
        };

        self.entry_func = matches.get_one::<String>("entry-func").cloned();
        if let Some(output_dir) = matches.get_one::<String>("output-dir") {
            self.output_dir = PathBuf::from(output_dir);
        }
        if let Some(analysis) = matches.get_one::<String>("analysis") {
            self.analysis_kind = analysis.parse::<AnalysisKind>().unwrap();
        }
        self.access_path_deref_limit = matches.get_one::<usize>("deref-limit").cloned().unwrap_or(DEFAULT_DEREF_LIMIT);
        self.ignore_rc_drop = !matches.contains_id("analyze-rc-drop");
        self.skip_generics = matches.contains_id("skip-generics");
        self.dump_mir = matches.contains_id("dump-mir");
        self.dump_call_graph = matches.contains_id("dump-call-graph");
        self.msa_strong_updates = !matches.contains_id("disable-strong-updates");
        self.msa_axm_check = !matches.contains_id("disable-msa-axm");

        // If the user provide the input source code file path before the `--` token,
        // add it to the rustc arguments.
        let mut rustc_args = args[rustc_args_start..].to_vec();
        if let Some(input) = matches.get_many::<String>("INPUT") {
            rustc_args.extend(input.cloned())
        } 
        
        rustc_args
    }

    pub fn call_graph_output_path(&self) -> PathBuf {
        let filename = if let Some(crate_name) = &self.crate_name {
            format!("{}_{}", crate_name, CALL_GRAPH_OUTPUT_SUFFIX)
        } else {
            CALL_GRAPH_OUTPUT_SUFFIX.to_string()
        };
        self.output_dir.join(filename)
    }

    pub fn mir_output_path(&self) -> PathBuf {
        let filename = if let Some(crate_name) = &self.crate_name {
            format!("{}_{}", crate_name, MIR_OUTPUT_SUFFIX)
        } else {
            MIR_OUTPUT_SUFFIX.to_string()
        };
        self.output_dir.join(filename)
    }
    
}

/// Gets the value of `name`.
/// `--name value` or `--name=value`
fn get_arg_flag_value(args: &[String], name: &str) -> Option<String> {
    let mut args = args.iter();
    loop {
        let arg = match args.next() {
            Some(arg) => arg.as_str(),
            None => return None,
        };
        if !arg.starts_with(name) {
            continue;
        }
        // Strip `name`.
        let suffix = &arg[name.len()..];
        if suffix.is_empty() {
            // This argument is `name` and the next one is the value.
            return args.next().cloned();
        } else if let Some(arg_value) = suffix.strip_prefix('=') {
            return Some(arg_value.to_string());
        }
    }
}