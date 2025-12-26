use assert_cmd::Command;
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::Path;

#[test]
fn difftsc_uses_canonical_file_paths() {
  let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");

  #[allow(deprecated)]
  let output = Command::cargo_bin("typecheck-ts-harness")
    .expect("binary")
    .arg("difftsc")
    .arg("--suite")
    .arg(&suite)
    .arg("--use-baselines")
    .arg("--compare-rust")
    .arg("--allow-mismatches")
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("json output");
  let results = json
    .get("results")
    .and_then(|r| r.as_array())
    .expect("results array");
  let case = results
    .iter()
    .find(|case| case.get("name").and_then(|n| n.as_str()) == Some("win_paths"))
    .expect("win_paths case present");
  let expected = case
    .get("expected")
    .and_then(|d| d.as_array())
    .expect("expected diagnostics");
  let actual = case
    .get("actual")
    .and_then(|d| d.as_array())
    .expect("actual diagnostics");

  let expected_files: BTreeSet<_> = expected
    .iter()
    .filter_map(|d| d.get("file").and_then(|f| f.as_str()))
    .collect();
  let actual_files: BTreeSet<_> = actual
    .iter()
    .filter_map(|d| d.get("file").and_then(|f| f.as_str()))
    .collect();

  assert_eq!(
    expected_files, actual_files,
    "expected difftsc to normalize file paths consistently"
  );
}
