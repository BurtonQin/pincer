#!/usr/bin/env bash
#
# Automatically runs pincer on each rustsec project and summarizes results.
#
# Usage:
#   ./run_all.sh                          # Run all projects (debug build)
#   ./run_all.sh gmath                    # Run a specific project
#   ./run_all.sh --release                # Use release build
#   ./run_all.sh --save-results           # Save detailed logs to results/
#   ./run_all.sh --release --save-results gmath

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PINCER_ROOT="$(cd "$SCRIPT_DIR/../.." && pwd)"
RESULTS_DIR="$SCRIPT_DIR/results"

# Colors for terminal output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
CYAN='\033[0;36m'
BOLD='\033[1m'
NC='\033[0m' # No Color

# Defaults
BUILD_PROFILE="debug"
SAVE_RESULTS=false

# Per-project cargo pincer extra arguments.
project_args() {
    case "$1" in
        RUSTSEC-2018-0010-openssl) echo "--manifest-path openssl/Cargo.toml --lib" ;;
        RUSTSEC-2025-0022-openssl) echo "--manifest-path openssl/Cargo.toml --lib" ;;
        RUSTSEC-2022-0078-bumpalo) echo "--lib" ;;
        *) echo "" ;;
    esac
}

# Per-project pincer-specific arguments (passed after --).
project_pincer_args() {
    case "$1" in
        RUSTSEC-2022-0078-bumpalo) echo "--entry-func main --deref-limit 3" ;;
        *) echo "" ;;
    esac
}

# Per-project extra RUSTFLAGS.
project_rustflags() {
    case "$1" in
        RUSTSEC-2025-0022-openssl) echo "--cfg ossl300" ;;
        RUSTSEC-2022-0070-secp256k1) echo "--cfg fuzzing" ;;
        *) echo "" ;;
    esac
}

PATCHES_DIR="$SCRIPT_DIR/patches"

apply_patches() {
    if [[ ! -d "$PATCHES_DIR" ]]; then
        return 0
    fi
    for patch_file in "$PATCHES_DIR"/*.patch; do
        [[ -f "$patch_file" ]] || continue
        local project_name
        project_name="$(basename "$patch_file" .patch)"
        local project_dir="$SCRIPT_DIR/$project_name"
        if [[ -d "$project_dir" ]]; then
            echo -e "${BOLD}Applying patch to: ${YELLOW}${project_name}${NC}"
            # Reset project to clean state before applying patch
            git -C "$project_dir" checkout -- . 2>/dev/null
            git -C "$project_dir" clean -fdx -e target 2>/dev/null
            git -C "$project_dir" apply --check "$patch_file" 2>/dev/null && \
                git -C "$project_dir" apply "$patch_file" || \
                echo -e "  ${YELLOW}Patch already applied or does not apply cleanly${NC}"
        fi
    done
    echo ""
}

resolve_pincer_binary() {
    local bin_dir="$PINCER_ROOT/target/$BUILD_PROFILE"
    CARGO_PINCER="$bin_dir/cargo-pincer"

    echo -e "${BOLD}Building pincer (${BUILD_PROFILE})...${NC}"
    if [[ "$BUILD_PROFILE" == "release" ]]; then
        cargo build --release --manifest-path "$PINCER_ROOT/Cargo.toml" 2>&1
    else
        cargo build --manifest-path "$PINCER_ROOT/Cargo.toml" 2>&1
    fi

    if [[ ! -x "$CARGO_PINCER" ]]; then
        echo -e "${RED}Failed to find cargo-pincer at ${CARGO_PINCER}${NC}"
        exit 1
    fi

    echo -e "${BOLD}Using pincer:${NC} ${CARGO_PINCER}"
}

run_pincer() {
    local project_dir="$1"
    local project_name
    project_name="$(basename "$project_dir")"

    # Skip non-directories
    [[ -d "$project_dir" ]] || return 0
    # Skip if no Cargo.toml (not a Rust project)
    [[ -f "$project_dir/Cargo.toml" ]] || return 0

    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"
    echo -e "${BOLD}Running pincer on: ${YELLOW}${project_name}${NC}"
    echo -e "${CYAN}━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━━${NC}"

    # Look up per-project config
    local extra_args
    extra_args="$(project_args "$project_name")"
    local extra_pincer_args
    extra_pincer_args="$(project_pincer_args "$project_name")"
    local extra_rustflags
    extra_rustflags="$(project_rustflags "$project_name")"

    # Force recompilation so pincer analysis always runs
    pushd "$project_dir" > /dev/null
    cargo clean 2>/dev/null || true

    # Build command using local binary
    local cmd=("$CARGO_PINCER" pincer $extra_args)
    if [[ -n "$extra_pincer_args" ]]; then
        cmd+=(-- $extra_pincer_args)
    fi

    # Display config
    local display_args="cargo pincer ${extra_args}"
    if [[ -n "$extra_pincer_args" ]]; then
        display_args="${display_args} -- ${extra_pincer_args}"
    fi
    if [[ -n "$extra_rustflags" ]]; then
        echo -e "  ${BOLD}Config:${NC} RUSTFLAGS=\"${extra_rustflags}\" ${display_args}"
    else
        echo -e "  ${BOLD}Config:${NC} ${display_args}"
    fi

    # Run pincer, capturing output to a temp file
    local tmp_log
    tmp_log=$(mktemp)
    local exit_code=0
    if [[ -n "$extra_rustflags" ]]; then
        RUSTFLAGS="$extra_rustflags" "${cmd[@]}" > "$tmp_log" 2>&1 || exit_code=$?
    else
        "${cmd[@]}" > "$tmp_log" 2>&1 || exit_code=$?
    fi
    popd > /dev/null

    # Optionally save log to results/
    if [[ "$SAVE_RESULTS" == true ]]; then
        mkdir -p "$RESULTS_DIR"
        cp "$tmp_log" "$RESULTS_DIR/${project_name}.log"
    fi

    # Parse results from log
    local bugs_line
    bugs_line=$(grep -m1 -E "^[0-9]+ Bug" "$tmp_log" 2>/dev/null || true)
    local no_bug_line
    no_bug_line=$(grep -m1 -E "^No bug detected" "$tmp_log" 2>/dev/null || true)
    local vuln_ptrs
    vuln_ptrs=$(grep -m1 "Number of vulnerable pointers:" "$tmp_log" 2>/dev/null | sed 's/.*: //' || echo "N/A")
    local analysis_time
    local raw_time
    raw_time=$(grep -m1 "Analysis time:" "$tmp_log" 2>/dev/null | sed 's/.*: //; s/[^0-9.].*//' || true)
    if [[ -n "$raw_time" ]]; then
        analysis_time=$(printf "%.2fs" "$raw_time")
    else
        analysis_time="N/A"
    fi
    local error_seeds
    error_seeds=$(grep -c "^Error seed" "$tmp_log" 2>/dev/null || true)
    error_seeds="${error_seeds:-0}"

    if [[ -n "$bugs_line" ]]; then
        local bug_count
        bug_count=$(echo "$bugs_line" | head -1 | sed 's/[^0-9].*//')
        echo -e "  ${RED}${BOLD}Result: ${bugs_line}${NC}"
        echo "${project_name}|${bug_count}|${vuln_ptrs}|${analysis_time}|BUGS_FOUND" >> "$SUMMARY_CSV"
    elif [[ -n "$no_bug_line" ]]; then
        echo -e "  ${GREEN}${BOLD}Result: No bug detected.${NC}"
        echo "${project_name}|0|${vuln_ptrs}|${analysis_time}|CLEAN" >> "$SUMMARY_CSV"
    elif [[ $exit_code -ne 0 ]]; then
        echo -e "  ${RED}${BOLD}Result: BUILD FAILED (exit code: ${exit_code})${NC}"
        if [[ "$SAVE_RESULTS" == true ]]; then
            echo -e "  ${YELLOW}See: ${RESULTS_DIR}/${project_name}.log${NC}"
        fi
        echo "${project_name}|N/A|N/A|N/A|BUILD_FAILED" >> "$SUMMARY_CSV"
    else
        echo -e "  ${YELLOW}${BOLD}Result: Unknown (check log)${NC}"
        echo "${project_name}|?|${vuln_ptrs}|${analysis_time}|UNKNOWN" >> "$SUMMARY_CSV"
    fi

    # Show error seed locations
    if [[ -n "$error_seeds" && "$error_seeds" -gt 0 ]] 2>/dev/null; then
        echo -e "  ${BOLD}Error seeds:${NC}"
        grep "^Error seed" "$tmp_log" | while IFS= read -r line; do
            echo -e "    ${RED}• ${line}${NC}"
        done
    fi

    rm -f "$tmp_log"
    echo ""
}

print_summary() {
    [[ -f "$SUMMARY_CSV" ]] || return 0

    # Column layout: space + 40 + 1 + 6 + 1 + 10 + 1 + 8 + 1 + 15 + 1 = 85
    local W=85
    local border
    border=$(printf '═%.0s' $(seq 1 $W))
    local FMT="%-40s %6s %10s %8s %15s "

    echo ""
    echo -e "${CYAN}╔${border}╗${NC}"
    local title
    title=$(printf "%*s" $(( (W + 7) / 2 )) "SUMMARY")
    printf "${CYAN}║${NC} ${BOLD}%-$((W - 1))s${NC}${CYAN}║${NC}\n" "$title"
    echo -e "${CYAN}╠${border}╣${NC}"
    printf "${CYAN}║${NC} ${BOLD}${FMT}${NC}${CYAN}║${NC}\n" \
        "Project" "Bugs" "VulnPtrs" "Time" "Status"
    echo -e "${CYAN}╠${border}╣${NC}"

    local total_bugs=0
    local total_projects=0
    local failed_projects=0

    while IFS='|' read -r name bugs vuln time status; do
        total_projects=$((total_projects + 1))
        local color="$GREEN"
        if [[ "$status" == "BUGS_FOUND" ]]; then
            color="$RED"
            total_bugs=$((total_bugs + bugs))
        elif [[ "$status" == "BUILD_FAILED" ]]; then
            color="$RED"
            failed_projects=$((failed_projects + 1))
        fi
        printf "${CYAN}║${NC} ${color}${FMT}${NC}${CYAN}║${NC}\n" \
            "$name" "$bugs" "$vuln" "$time" "$status"
    done < "$SUMMARY_CSV"

    local total_str
    total_str=$(printf "%d/%d projects" "$((total_projects - failed_projects))" "$total_projects")
    echo -e "${CYAN}╠${border}╣${NC}"
    printf "${CYAN}║${NC} ${BOLD}${FMT}${NC}${CYAN}║${NC}\n" \
        "TOTAL" "$total_bugs" "" "" "$total_str"
    echo -e "${CYAN}╚${border}╝${NC}"

    if [[ "$SAVE_RESULTS" == true ]]; then
        cp "$SUMMARY_CSV" "$RESULTS_DIR/summary.csv"
        echo ""
        echo -e "Detailed logs saved to: ${BOLD}${RESULTS_DIR}/${NC}"
    fi
}

# Main
main() {
    # Parse flags
    local projects=()
    while [[ $# -gt 0 ]]; do
        case "$1" in
            --release)
                BUILD_PROFILE="release"
                shift
                ;;
            --save-results)
                SAVE_RESULTS=true
                shift
                ;;
            -*)
                echo -e "${RED}Unknown option: $1${NC}"
                echo "Usage: $0 [--release] [--save-results] [project ...]"
                exit 1
                ;;
            *)
                projects+=("$1")
                shift
                ;;
        esac
    done

    echo -e "${BOLD}Pincer RustSec Benchmark Runner${NC}"
    echo -e "Working directory: ${SCRIPT_DIR}"
    echo ""

    resolve_pincer_binary
    apply_patches

    # Use a temp file for the summary CSV
    SUMMARY_CSV=$(mktemp)
    trap 'rm -f "$SUMMARY_CSV"' EXIT

    echo ""
    if [[ ${#projects[@]} -gt 0 ]]; then
        # Run specific project(s)
        for name in "${projects[@]}"; do
            local dir="$SCRIPT_DIR/$name"
            if [[ -d "$dir" ]]; then
                run_pincer "$dir"
            else
                echo -e "${RED}Project not found: ${name}${NC}"
            fi
        done
    else
        # Run all projects (sorted for consistent ordering)
        for dir in "$SCRIPT_DIR"/*/; do
            local dir_name
            dir_name="$(basename "$dir")"
            [[ "$dir_name" == "results" ]] && continue
            run_pincer "$dir"
        done
    fi

    print_summary
}

main "$@"
