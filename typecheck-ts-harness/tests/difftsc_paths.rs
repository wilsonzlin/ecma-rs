use assert_cmd::Command;
use serde_json::Value;
use std::collections::BTreeSet;
use std::path::Path;
use std::time::Duration;

const CLI_TIMEOUT: Duration = Duration::from_secs(30);

#[test]
fn difftsc_uses_canonical_file_paths() {
  let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");

  #[allow(deprecated)]
  let output = Command::cargo_bin("typecheck-ts-harness")
    .expect("binary")
    .timeout(CLI_TIMEOUT)
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
