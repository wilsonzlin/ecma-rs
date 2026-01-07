use assert_cmd::Command;
use serde_json::Value;
use std::time::Duration;

fn minify_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("minify-js-cli")
}

#[test]
fn json_success_contains_schema_version_and_output() {
  let assert = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--json")
    .arg("--mode")
    .arg("global")
    .write_stdin("let x = 1;")
    .assert()
    .success()
    .code(0);

  assert!(
    assert.get_output().stderr.is_empty(),
    "expected stderr to be empty, got: {}",
    String::from_utf8_lossy(&assert.get_output().stderr)
  );

  let stdout = String::from_utf8_lossy(&assert.get_output().stdout);
  let value: Value = serde_json::from_str(&stdout).expect("stdout to be valid JSON");
  assert_eq!(value["schema_version"], 1);
  assert_eq!(value["mode"], "global");
  assert_eq!(value["output"], "let x=1;");
}

#[test]
fn json_error_contains_diagnostics_array() {
  let assert = minify_js_cli()
    .timeout(Duration::from_secs(5))
    .arg("--json")
    .arg("--mode")
    .arg("global")
    .write_stdin("function {")
    .assert()
    .failure()
    .code(1);

  assert!(
    assert.get_output().stderr.is_empty(),
    "expected stderr to be empty, got: {}",
    String::from_utf8_lossy(&assert.get_output().stderr)
  );

  let stdout = String::from_utf8_lossy(&assert.get_output().stdout);
  let value: Value = serde_json::from_str(&stdout).expect("stdout to be valid JSON");
  assert_eq!(value["schema_version"], 1);
  assert_eq!(value["mode"], "global");

  let diagnostics = value
    .get("diagnostics")
    .and_then(|value| value.as_array())
    .expect("expected diagnostics array");
  assert!(
    !diagnostics.is_empty(),
    "expected diagnostics to be non-empty, got: {diagnostics:?}"
  );
}

