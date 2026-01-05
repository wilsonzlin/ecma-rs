use assert_cmd::Command;
use serde_json::Value;
use std::collections::BTreeSet;
use std::time::Duration;

mod common;

const CLI_TIMEOUT: Duration = Duration::from_secs(60);

fn harness_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("typecheck-ts-harness")
}

#[test]
fn difftsc_uses_canonical_file_paths() {
  let (_dir, suite) = common::temp_difftsc_suite(&["module_types", "win_paths"]);

  let output = harness_cli()
    .timeout(CLI_TIMEOUT)
    .arg("difftsc")
    .arg("--suite")
    .arg(&suite)
    // Keep the difftsc CLI lightweight so it stays within the test timeout even
    // when the cargo test harness runs multiple integration tests in parallel.
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

  let module_case = results
    .iter()
    .find(|case| case.get("name").and_then(|n| n.as_str()) == Some("module_types"))
    .expect("module_types case present");
  let rust_diags = module_case
    .get("actual")
    .and_then(|d| d.as_array())
    .cloned()
    .unwrap_or_default();
  assert!(
    rust_diags.is_empty(),
    "module_types should not produce Rust diagnostics: {:?}",
    rust_diags
  );
  if let Some(exports) = module_case
    .get("actual_types")
    .and_then(|t| t.get("exports"))
    .and_then(|e| e.as_array())
  {
    let foo_type = exports
      .iter()
      .find(|export| export.get("name").and_then(|n| n.as_str()) == Some("v"))
      .and_then(|export| export.get("type").and_then(|t| t.as_str()))
      .unwrap_or("unknown");
    assert_ne!(
      foo_type, "unknown",
      "module_types should resolve value export types; exports={:?}",
      exports
    );
  }
}
