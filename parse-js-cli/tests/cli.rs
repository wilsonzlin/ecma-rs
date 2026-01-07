use assert_cmd::Command;
use serde_json::Value;
use std::time::Duration;
use tempfile::tempdir;

fn parse_js_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("parse-js-cli")
}

fn parse_stdout_json(stdout: &[u8]) -> Value {
  serde_json::from_slice(stdout).expect("stdout should be valid JSON")
}

#[test]
fn infers_dialect_from_tsx_extension_and_wraps_output() {
  let dir = tempdir().unwrap();
  let path = dir.path().join("example.tsx");
  std::fs::write(&path, "<foo>bar</foo>;").unwrap();

  let assert = parse_js_cli()
    .timeout(Duration::from_secs(5))
    .arg(&path)
    .assert()
    .success();

  let output = parse_stdout_json(&assert.get_output().stdout);
  assert_eq!(output["schema_version"], 1);
  assert_eq!(output["options"]["dialect"], "tsx");
  assert_eq!(output["options"]["source_type"], "module");

  assert_eq!(output["ast"]["body"][0]["$t"], "Expr");
  assert_eq!(output["ast"]["body"][0]["expr"]["$t"], "JsxElem");
}

#[test]
fn infers_dialect_from_dts_extension() {
  let dir = tempdir().unwrap();
  let path = dir.path().join("types.d.ts");
  std::fs::write(&path, "declare const x: string;").unwrap();

  let assert = parse_js_cli()
    .timeout(Duration::from_secs(5))
    .arg(&path)
    .assert()
    .success();

  let output = parse_stdout_json(&assert.get_output().stdout);
  assert_eq!(output["options"]["dialect"], "dts");
}

#[test]
fn source_type_script_changes_parsing_and_json_errors_emit_diagnostics() {
  let dir = tempdir().unwrap();
  let path = dir.path().join("module.js");
  std::fs::write(&path, "export const x = 1;").unwrap();

  // Default source type is module, so `export` should parse.
  let assert = parse_js_cli()
    .timeout(Duration::from_secs(5))
    .arg(&path)
    .assert()
    .success();
  let output = parse_stdout_json(&assert.get_output().stdout);
  assert_eq!(output["options"]["dialect"], "js");
  assert_eq!(output["options"]["source_type"], "module");

  // In script mode, `export` is rejected; ensure JSON errors are emitted to stdout.
  let assert = parse_js_cli()
    .timeout(Duration::from_secs(5))
    .arg(&path)
    .arg("--source-type")
    .arg("script")
    .arg("--json-errors")
    .assert()
    .failure()
    .code(1);

  assert!(
    assert.get_output().stderr.is_empty(),
    "expected stderr to be empty in --json-errors mode, got: {}",
    String::from_utf8_lossy(&assert.get_output().stderr)
  );

  let output = parse_stdout_json(&assert.get_output().stdout);
  assert_eq!(output["schema_version"], 1);
  let diagnostics = output["diagnostics"].as_array().unwrap();
  assert!(!diagnostics.is_empty());
  let message = diagnostics[0]["message"].as_str().unwrap();
  assert!(
    message.contains("export not allowed in scripts"),
    "expected message to mention script export restriction, got: {message}"
  );
}

