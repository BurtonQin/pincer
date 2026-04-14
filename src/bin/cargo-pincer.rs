// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

//! This provides an implementation for the "cargo pincer" subcommand.
//! 
//! The subcommand is the same as "cargo check" but with three differences:
//! 1) It implicitly adds the options "-Z always_encode_mir" to the rustc invocation.
//! 2) It calls `pincer` rather than `rustc` for all the targets of the current package.
//! 3) It runs `cargo test --no-run` for test targets.

use log::*;
use cargo_metadata::Package;
use std::ffi::OsString;
use std::ops::Index;
use std::path::Path;
use std::process::Command;

/// The help message for `cargo-pincer`
const CARGO_PINCER_HELP: &str = r#"Raw pointer analysis tool for Rust programs
Usage:
    cargo pincer [CARGO OPTIONS] [-- [PINCER OPTIONS]]

Pincer options (passed after --):
    -a, --analysis <MODE>   Analysis mode: rta, memory-safety (default), ms
"#;


pub fn main() {
    if std::env::args().take_while(|a| a != "--").any(|a| a == "--help" || a == "-h") {
        println!("{}", CARGO_PINCER_HELP);
        return;
    }

    if std::env::var("PINCER_LOG").is_ok() {
        let e = env_logger::Env::new()
            .filter("PINCER_LOG")
            .write_style("PINCER_LOG_STYLE");
        env_logger::init_from_env(e);
    }

    match std::env::args().nth(1).as_ref().map(AsRef::<str>::as_ref) {
        Some(s) if s.ends_with("pincer") => {
            // Get here for the top level cargo execution, i.e. "cargo pincer".
            call_cargo();
        }
        Some(s) if s.ends_with("rustc") => {
            // 'cargo rustc ..' redirects here because RUSTC_WRAPPER points to this binary.
            // execute rustc with PINCER applicable parameters for dependencies and call PINCER
            // to analyze targets in the current package.
            call_rustc_or_pincer();
        }
        Some(arg) => {
            eprintln!(
                "`cargo-pincer` called with invalid first argument: {arg}; please only invoke this binary through `cargo pincer`" 
            );
        }
        _ => {
            eprintln!("`cargo-pincer` called without first argument; please only invoke this binary through `cargo pincer`");
        }
    }
}

/// Read the toml associated with the current directory and
/// recursively execute cargo for each applicable package target/workspace member in the toml
fn call_cargo() {
    let manifest_path = get_arg_flag_value("--manifest-path").map(|m| Path::new(&m).canonicalize().unwrap());

    let mut cmd = cargo_metadata::MetadataCommand::new();
    if let Some(ref manifest_path) = manifest_path {
        cmd.manifest_path(manifest_path);
    }

    let metadata = if let Ok(metadata) = cmd.exec() {
        metadata
    } else {
        eprintln!("Could not obtain Cargo metadata; likely an ill-formed manifest");
        std::process::exit(1);
    };

    // If a binary is specified, analyze this binary only.
    if let Some(target) = get_arg_flag_value("--bin") {
        call_cargo_on_target(&target, "bin");
        return;
    }

    if let Some(root) = metadata.root_package() {
        call_cargo_on_each_package_target(root);
        return;
    }

    // There is no root, this must be a workspace, so call_cargo_on_each_package_target on each workspace member
    for package_id in &metadata.workspace_members {
        let package = metadata.index(package_id);
        call_cargo_on_each_package_target(package);
    }
}

fn call_cargo_on_each_package_target(package: &Package) {
    let lib_only = has_arg_flag("--lib");
    let include_test = has_arg_flag("--test");
    for target in &package.targets {
        let kind = target
            .kind
            .first()
            .expect("bad cargo metadata: target::kind")
            .as_str();
        if lib_only && !target.is_lib() {
            continue;
        }
        if target.is_test() && !include_test {
            continue;
        }
        call_cargo_on_target(&target.name, kind);
    }
}

fn call_cargo_on_target(target: &str, kind: &str) {
    info!("Call cargo on target: {:?}, kind: {:?}", target, kind);
    // Build a cargo command for target
    let mut cmd = Command::new(std::env::var_os("CARGO").unwrap_or_else(|| OsString::from("cargo")));
    match kind {
        "bin" => {
            cmd.arg("check");
            cmd.arg("--bin").arg(target);
        }
        _ if is_lib_target(kind) => {
            cmd.arg("check");
            cmd.arg("--lib");
        }
        "test" => {
            cmd.arg("test");
            cmd.arg("--test").arg(target);
            cmd.arg("--no-run");
        }
        _ => {
            return;
        }
    }
    cmd.arg("--verbose");

    let mut args = std::env::args().skip(2);
    // Add cargo args to cmd until first `--`.
    for arg in args.by_ref() {
        if arg == "--" {
            break;
        }
        if arg == "--lib" {
            continue;
        }
        cmd.arg(arg);
    }

    // Serialize the remaining args into an environment variable.
    let args_vec: Vec<String> = args.collect();
    if !args_vec.is_empty() {
        cmd.env(
            "PINCER_FLAGS",
            serde_json::to_string(&args_vec).expect("failed to serialize args"),
        );
    }

    // Force cargo to recompile all dependencies with PINCER friendly flags
    let mut rustflags = std::env::var("RUSTFLAGS").unwrap_or_default();
    rustflags.push_str(" -Z always-encode-mir -Zmir-opt-level=0");
    rustflags.push_str(&format!(" --cfg pincer_target=\"{}\"", target.replace('-', "_")));
    cmd.env("RUSTFLAGS", rustflags);
    
    // Communicate the name of the root crate to the calls to cargo-pincer that are invoked via
    // the RUSTC_WRAPPER setting.
    cmd.env("PINCER_CRATE", target.replace('-', "_"));

    // Replace the rustc executable through RUSTC_WRAPPER environment variable so that rustc
    // calls generated by cargo come back to cargo-pincer.
    let path = std::env::current_exe().expect("current executable path invalid");
    cmd.env("RUSTC_WRAPPER", path);

    // Communicate the target kind of the root crate to the calls to cargo-pincer that are invoked via
    // the RUSTC_WRAPPER setting.
    cmd.env("PINCER_TARGET_KIND", kind);

    // Set the tool chain to be compatible with pincer
    if let Some(toolchain) = option_env!("RUSTUP_TOOLCHAIN") {
        cmd.env("RUSTUP_TOOLCHAIN", toolchain);
    }

    // Execute cmd
    debug!("cmd: {:?}", cmd);
    let exit_status = cmd
        .spawn()
        .expect("could not run cargo")
        .wait()
        .expect("failed to wait for cargo");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

fn call_rustc_or_pincer() {
    if let Some(crate_name) = get_arg_flag_value("--crate-name") {
        if let Some(pincer_target) = get_arg_flag_value("pincer_target") {
            if crate_name.eq(&pincer_target) {
                if let Ok(kind) = std::env::var("PINCER_TARGET_KIND") {
                    if let Some(t) = get_arg_flag_value("--crate-type") {
                        if kind.eq(&t) {
                            call_pincer();
                            return;
                        }
                    } else if kind == "test" {
                        call_pincer();
                        return;
                    }
                }
            }
        }
    }
    call_rustc()
}

fn call_pincer() {
    let mut path = std::env::current_exe().expect("current executable path invalid");
    let extension = path.extension().map(|e| e.to_owned());
    path.pop(); // remove the cargo_pincer bit
    path.push("pincer");
    if let Some(ext) = extension {
        path.set_extension(ext);
    }
    let mut cmd = Command::new(path);
    cmd.args(std::env::args().skip(2));
    let exit_status = cmd
        .spawn()
        .expect("could not run pincer")
        .wait()
        .expect("failed to wait for pincer");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

fn call_rustc() {
    // todo: invoke the rust compiler for the appropriate tool chain?
    let mut cmd = Command::new(std::env::var_os("RUSTC").unwrap_or_else(|| OsString::from("rustc")));
    cmd.args(std::env::args().skip(2));
    let exit_status = cmd
        .spawn()
        .expect("could not run rustc")
        .wait()
        .expect("failed to wait for rustc");

    if !exit_status.success() {
        std::process::exit(exit_status.code().unwrap_or(-1))
    }
}

/// Determines whether a flag `name` is present before `--`.
/// For example, has_arg_flag("-v")
#[allow(unused)]
fn has_arg_flag(name: &str) -> bool {
    let mut args = std::env::args().take_while(|val| val != "--");
    args.any(|val| val == name)
}

/// Gets the value of `name`.
/// `--name value` or `--name=value`
fn get_arg_flag_value(name: &str) -> Option<String> {
    let mut args = std::env::args().take_while(|val| val != "--");
    loop {
        let arg = match args.next() {
            Some(arg) => arg,
            None => return None,
        };
        if !arg.starts_with(name) {
            continue;
        }
        // Strip `name`.
        let suffix = &arg[name.len()..];
        if suffix.is_empty() {
            // This argument is `name` and the next one is the value.
            return args.next();
        } else if let Some(arg_value) = suffix.strip_prefix('=') {
            return Some(strip_quotes(&arg_value.to_owned()).to_string());
        }
    }
}

fn strip_quotes(s: &str) -> &str {
    if s.starts_with('"') && s.ends_with('"') && s.len() >= 2 {
        &s[1..s.len()-1]
    } else {
        s
    }
}

fn is_lib_target(kind: &str) -> bool {
    ["lib", "dylib", "rlib", "staticlib", "cdylib"].contains(&kind)
}