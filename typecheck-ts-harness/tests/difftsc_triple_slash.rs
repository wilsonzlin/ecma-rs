use assert_cmd::Command;
use serde_json::Value;
use std::path::Path;
use std::time::Duration;

const CLI_TIMEOUT: Duration = Duration::from_secs(30);

fn harness_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("typecheck-ts-harness")
}

fn run_difftsc() -> Value {
  let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");
  let manifest = suite.join("manifest.toml");

  let output = harness_cli()
    .timeout(CLI_TIMEOUT)
    .arg("difftsc")
    .arg("--suite")
    .arg(&suite)
    .arg("--manifest")
    .arg(&manifest)
    .arg("--use-baselines")
    .arg("--compare-rust")
    .arg("--allow-mismatches")
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  serde_json::from_slice(&output).expect("json output")
}

fn find_case<'a>(report: &'a Value, name: &str) -> &'a Value {
  report
    .get("results")
    .and_then(|r| r.as_array())
    .and_then(|arr| {
      arr
        .iter()
        .find(|case| case.get("name").and_then(|n| n.as_str()) == Some(name))
    })
    .unwrap_or_else(|| panic!("missing difftsc case {name}; report={report:?}"))
}

fn assert_matched(case: &Value, name: &str) {
  let status = case
    .get("status")
    .and_then(|s| s.as_str())
    .unwrap_or("<missing>");
  assert_eq!(
    status, "matched",
    "expected {name} difftsc case to match baseline; case={case:?}"
  );
}

#[test]
fn difftsc_selected_cases_match_baselines() {
  let report = run_difftsc();
  let summary = report
    .get("summary")
    .and_then(|s| s.as_object())
    .expect("summary object");
  assert_eq!(
    summary
      .get("unexpected_mismatches")
      .and_then(|v| v.as_u64()),
    Some(0),
    "expected difftsc to have no unexpected mismatches (manifest should cover all known failures); summary: {summary:?}"
  );

  for name in [
    "import_equals_require",
    "module_types",
    "multi",
    "triple_slash_references",
    "triple_slash_no_default_lib",
    "triple_slash_path_imported",
    "triple_slash_types_imported",
    "triple_slash_lib_imported",
  ] {
    let case = find_case(&report, name);
    assert_matched(case, name);
  }
}
