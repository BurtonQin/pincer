# Pincer

A static analysis tool for detecting memory safety bugs in Rust programs. Pincer finds **use-after-free**, **double-free**, and **dangling pointer** vulnerabilities in unsafe Rust code by performing interprocedural pointer alias analysis on the compiler's MIR (Mid-level Intermediate Representation).

## How It Works

Pincer hooks into the Rust compiler as a `rustc` driver and runs after the standard compilation pipeline completes. Analysis proceeds in three stages:

1. **Rapid Type Analysis (RTA)** — builds a precise interprocedural call graph by resolving virtual dispatch and function pointers.
2. **IFDS Alias Analysis** — a bidirectional IFDS-based dataflow analysis that tracks raw pointer aliases across function boundaries. For each vulnerable pointer, a backward pass finds all flow origins (allocations, parameters), and a forward pass propagates aliases from each origin.
3. **Type-State Analysis (TSA)** — tracks the null/non-null type-state of each aliased pointer along all control flow paths (including drop/unwind edges) to detect use-after-free and double-free bugs.

## Prerequisites

Pincer requires a specific nightly Rust toolchain. Install it with:

```sh
rustup toolchain install nightly-2024-10-11 \
  --component rust-src rustc-dev llvm-tools-preview
```

The `rust-toolchain.toml` in this repository will select this toolchain automatically once it is installed.

## Building

```sh
git clone <repo-url>
cd pincer
cargo build --release
```

The build produces two binaries in `target/release/`:
- `pincer` — the compiler driver (invoked internally by cargo-pincer)
- `cargo-pincer` — the `cargo` subcommand wrapper

## Installation

Copy both binaries somewhere on your `PATH`, or install directly:

```sh
cargo install --path . --bins
```

## Usage

Run Pincer on a Rust project the same way you would run `cargo check`:

```sh
# In the root of any Cargo project
cargo pincer
```

Pincer will compile all library and binary targets, replacing `rustc` with itself for each target in the current package, and print a report of detected memory safety bugs.

### Targeting a specific binary

```sh
cargo pincer --bin my_binary
```

### Analysis modes

| Flag | Mode | Description |
|------|------|-------------|
| `-a rta` | RTA only | Build and dump the call graph, print reachable function count. |
| `-a memory-safety` | Memory safety (default) | Full analysis: alias tracking + type-state bug detection. |

```sh
# Run only RTA and dump the call graph
cargo pincer -- -a rta --dump-call-graph
```

### Logging

```sh
# Pincer-level logging
PINCER_LOG=debug cargo pincer

# Rustc-level logging
RUSTC_LOG=info cargo pincer
```

## Configuration

### Vulnerable pointer patterns

Pincer identifies *vulnerable pointers* — raw pointers that are seeds for alias tracking — via patterns defined in `config/vuln_ptrs.yaml`. The default patterns cover common sources such as `as_ptr`, `as_mut_ptr`, and FFI functions that return raw pointers.

You can extend or override these patterns by editing `config/vuln_ptrs.yaml` — note that changes require rebuilding Pincer to take effect, as the file is embedded at compile time.

## Citation

If you use Pincer in your research, please cite:

```bibtex
@article{pincer2026,
  author = {Li, Wei and Chen, Wenyao and Xue, Jingling},
  title = {From Raw Pointers to Memory Safety: A Modular Demand-Driven Typestate Analysis for Rust},
  year = {2026},
  issue_date = {April 2026},
  publisher = {Association for Computing Machinery},
  address = {New York, NY, USA},
  volume = {10},
  number = {OOPSLA1},
  url = {https://doi.org/10.1145/3798266},
  doi = {10.1145/3798266},
  journal = {Proc. ACM Program. Lang.},
  month = apr,
  articleno = {158},
  numpages = {29},
  keywords = {Memory Safety, Rust Analysis, Typestate Analysis}
}
```

## License

Licensed under the GNU General Public License — see [LICENSE](LICENSE) for details.
