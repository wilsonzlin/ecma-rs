use assert_cmd::Command;
use serde_json::Value;
use std::path::Path;
use std::time::Duration;

const CLI_TIMEOUT: Duration = Duration::from_secs(30);

#[test]
fn this_param_dts_matches_baseline_type_facts() {
  let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");
  let manifest = suite.join("manifest.toml");

  #[allow(deprecated)]
  let output = Command::cargo_bin("typecheck-ts-harness")
    .expect("binary")
    .timeout(CLI_TIMEOUT)
    .arg("difftsc")
    .arg("--suite")
    .arg(&suite)
    .arg("--manifest")
    .arg(&manifest)
    // Run difftsc with limited parallelism to keep this integration test
    // comfortably below its wall-clock timeout under parallel `cargo test`.
    .arg("--jobs")
    .arg("1")
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
  let results = report
    .get("results")
    .and_then(|r| r.as_array())
    .expect("results array");

  fn assert_case_matched<'a>(results: &'a [Value], name: &str) -> &'a Value {
    let case = results
      .iter()
      .find(|case| case.get("name").and_then(|n| n.as_str()) == Some(name))
      .unwrap_or_else(|| panic!("{name} case present"));
    let status = case
      .get("status")
      .and_then(|s| s.as_str())
      .unwrap_or("missing status");
    assert_eq!(
      status, "matched",
      "expected {name} difftsc case to match baseline (type facts + markers)"
    );
    case
  }

  assert_case_matched(results, "overloads");

  let case = assert_case_matched(results, "this_param_dts");

  let actual_types = case.get("actual_types").expect("actual types present");
  let markers = actual_types
    .get("markers")
    .and_then(|v| v.as_array())
    .expect("markers array");
  assert_eq!(markers.len(), 1);
  assert_eq!(
    markers[0].get("type").and_then(|v| v.as_str()),
    Some("number")
  );
}
