use assert_cmd::Command;
use serde_json::Value;
use std::path::Path;

#[test]
fn import_equals_require_matches_baseline() {
  let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");
  let manifest = suite.join("manifest.toml");

  #[allow(deprecated)]
  let output = Command::cargo_bin("typecheck-ts-harness")
    .expect("binary")
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

  let report: Value = serde_json::from_slice(&output).expect("json output");
  let results = report
    .get("results")
    .and_then(|r| r.as_array())
    .expect("results array");
  let case = results
    .iter()
    .find(|case| case.get("name").and_then(|n| n.as_str()) == Some("import_equals_require"))
    .expect("import_equals_require case present");
  let status = case
    .get("status")
    .and_then(|s| s.as_str())
    .unwrap_or("missing status");
  assert_eq!(
    status, "matched",
    "expected import_equals_require difftsc case to match baseline"
  );
}
