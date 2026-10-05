// Copyright (c) 2024 <Wei Li>.
//
// This source code is licensed under the GNU license found in the
// LICENSE file in the root directory of this source tree.

//! SARIF 2.1.0 export for the memory-safety analysis
//! (`--format sarif`).
//!
//! The mapping mirrors the external dataset generator in the lockbud-stable
//! workspace so both exports stay interchangeable: one rule per error kind
//! (`pincer/double-free`, `pincer/use-after-free`,
//! `pincer/dangling-pointer`) with CWE tags, and one result per error-state
//! location with the containing function in the message and properties.
//! Unlike the plain-text report, findings carry real source spans resolved
//! from the MIR at the error locations.

use serde_json::{json, Value};

const SARIF_SCHEMA: &str = "https://docs.oasis-open.org/sarif/sarif/v2.1.0/errata01/os/schemas/sarif-schema-2.1.0.json";

/// One finding located at a MIR error-state location. Region values are
/// 1-based and INCLUSIVE (SARIF convention); `end_col` is omitted when the
/// span ends exactly at a line boundary (the region then extends to the
/// end of the line).
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SarifFinding {
    /// ErrorKind debug name: `DoubleFree`, `UseAfterFree`, `DanglingPointer`.
    pub kind: String,
    pub containing_function: String,
    pub uri: String,
    pub start_line: u32,
    pub start_col: u32,
    pub end_line: u32,
    pub end_col: Option<u32>,
}

fn rule_id(kind: &str) -> String {
    match kind {
        "DoubleFree" => "pincer/double-free".to_owned(),
        "UseAfterFree" => "pincer/use-after-free".to_owned(),
        "DanglingPointer" => "pincer/dangling-pointer".to_owned(),
        other => format!("pincer/{}", other),
    }
}

fn cwe_for(kind: &str) -> &'static str {
    match kind {
        "DoubleFree" => "CWE-415",
        "UseAfterFree" | "DanglingPointer" => "CWE-416",
        _ => "",
    }
}

/// The plain-text diagnostic pincer prints for this kind; kept as the
/// SARIF message so both formats report the same words.
pub fn message_for(kind: &str) -> String {
    let text = match kind {
        "DoubleFree" => "Double Free detected",
        "UseAfterFree" => "Use-After-Free detected",
        "DanglingPointer" => "Dangling pointer detected",
        other => return format!("{other} detected"),
    };
    text.to_owned()
}

fn rule_descriptor(kind: &str) -> Value {
    let mut rule = json!({
        "id": rule_id(kind),
        "name": kind,
        "shortDescription": { "text": message_for(kind) },
        "fullDescription": { "text": format!(
            "{} (pincer type-state analysis finding on a vulnerable raw pointer)",
            message_for(kind)
        )},
    });
    let cwe = cwe_for(kind);
    if !cwe.is_empty() {
        rule["properties"] = json!({ "cwe": [cwe] });
    }
    rule
}

/// Build one complete SARIF 2.1.0 log from the collected findings.
/// Findings are sorted and deduplicated for deterministic output
/// (the underlying error seeds live in hash sets).
pub fn build_sarif_log(crate_name: &str, findings: &[SarifFinding]) -> Value {
    let mut sorted: Vec<&SarifFinding> = findings.iter().collect();
    sorted.sort();
    sorted.dedup();

    let mut rules: Vec<Value> = Vec::new();
    let mut seen_rules: Vec<String> = Vec::new();
    let mut artifacts: Vec<Value> = Vec::new();
    let mut seen_uris: Vec<String> = Vec::new();
    let mut results: Vec<Value> = Vec::new();

    for finding in sorted {
        if !seen_rules.iter().any(|id| id == &finding.kind) {
            seen_rules.push(finding.kind.clone());
            rules.push(rule_descriptor(&finding.kind));
        }
        if !seen_uris.iter().any(|u| u == &finding.uri) {
            seen_uris.push(finding.uri.clone());
            artifacts.push(json!({ "location": { "uri": finding.uri } }));
        }
        let mut region = json!({
            "startLine": finding.start_line,
            "startColumn": finding.start_col,
        });
        if finding.end_line != finding.start_line {
            region["endLine"] = json!(finding.end_line);
        }
        if let Some(end_col) = finding.end_col {
            region["endColumn"] = json!(end_col);
        }
        results.push(json!({
            "ruleId": rule_id(&finding.kind),
            "level": "error",
            "message": { "text": format!(
                "{} (in {})",
                message_for(&finding.kind),
                finding.containing_function,
            )},
            "locations": [{ "physicalLocation": {
                "artifactLocation": { "uri": finding.uri },
                "region": region,
            }}],
            "properties": {
                "detector": "pincer",
                "bugKind": finding.kind,
                "containingFunction": finding.containing_function,
            },
        }));
    }

    json!({
        "$schema": SARIF_SCHEMA,
        "version": "2.1.0",
        "runs": [{
            "tool": { "driver": {
                "name": "pincer",
                "version": env!("CARGO_PKG_VERSION"),
                "informationUri": "https://github.com/rustanlys/pincer",
                "rules": rules,
            }},
            "results": results,
            "artifacts": artifacts,
            "automationDetails": { "id": format!("pincer-scan/{}", crate_name) },
            "invocations": [{ "executionSuccessful": true }],
            "properties": {
                "columnConvention": "1-based lines/columns; region endColumn is inclusive; a missing endColumn extends to the end of the line",
            },
        }],
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn finding(kind: &str, uri: &str, start_line: u32) -> SarifFinding {
        SarifFinding {
            kind: kind.to_owned(),
            containing_function: "trigger_uaf".to_owned(),
            uri: uri.to_owned(),
            start_line,
            start_col: 5,
            end_line: start_line,
            end_col: Some(22),
        }
    }

    #[test]
    fn test_build_sarif_log() {
        let log = build_sarif_log(
            "uaf_example",
            &[
                finding("UseAfterFree", "src/main.rs", 17),
                finding("DoubleFree", "src/main.rs", 12),
            ],
        );
        assert_eq!(log["version"], "2.1.0");
        let run = &log["runs"][0];
        assert_eq!(run["tool"]["driver"]["name"], "pincer");
        assert_eq!(run["automationDetails"]["id"], "pincer-scan/uaf_example");
        let results = run["results"].as_array().unwrap();
        assert_eq!(results.len(), 2);
        // deterministic order: DoubleFree sorts before UseAfterFree
        assert_eq!(results[0]["ruleId"], "pincer/double-free");
        assert_eq!(results[0]["level"], "error");
        assert_eq!(results[0]["message"]["text"], "Double Free detected (in trigger_uaf)");
        let region = &results[0]["locations"][0]["physicalLocation"]["region"];
        assert_eq!(region["startLine"], 12);
        assert_eq!(region["endColumn"], 22);
        // rules registered once per kind, with CWE tags
        let rules = run["tool"]["driver"]["rules"].as_array().unwrap();
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0]["properties"]["cwe"][0], "CWE-415");
        assert_eq!(rules[1]["properties"]["cwe"][0], "CWE-416");
        let uris: Vec<&str> = run["artifacts"]
            .as_array()
            .unwrap()
            .iter()
            .map(|a| a["location"]["uri"].as_str().unwrap())
            .collect();
        assert_eq!(uris, vec!["src/main.rs"]);
    }

    #[test]
    fn test_dedup_and_determinism() {
        let findings = vec![
            finding("UseAfterFree", "src/main.rs", 17),
            finding("UseAfterFree", "src/main.rs", 17),
        ];
        let log = build_sarif_log("c", &findings);
        assert_eq!(log["runs"][0]["results"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn test_missing_end_column_omitted() {
        let mut f = finding("UseAfterFree", "src/main.rs", 17);
        f.end_line = 18;
        f.end_col = None;
        let log = build_sarif_log("c", &[f]);
        let region = &log["runs"][0]["results"][0]["locations"][0]["physicalLocation"]["region"];
        assert_eq!(region["endLine"], 18);
        assert!(region.get("endColumn").is_none());
    }
}
