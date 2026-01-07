mod common;

use assert_cmd::Command;
use serde_json::Value;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;
use tempfile::tempdir;

const CLI_TIMEOUT: Duration = Duration::from_secs(60);

fn harness_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("typecheck-ts-harness")
}

#[test]
fn verify_snapshots_succeeds_for_conformance_mini() {
  let node_path = match common::node_path_or_skip("verify-snapshots conformance-mini") {
    Some(path) => path,
    None => return,
  };

  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("verify-snapshots")
    .arg("--root")
    .arg(&root)
    .arg("--node")
    .arg(node_path)
    .arg("--jobs")
    .arg("2")
    .arg("--timeout-secs")
    .arg("20")
    .arg("--json");

  let output = cmd.assert().success().get_output().stdout.clone();
  let report: Value = serde_json::from_slice(&output).expect("valid json");

  assert_eq!(report["suite_name"], "conformance-mini");
  assert_eq!(report["summary"]["total"], 6);
  assert_eq!(report["summary"]["ok"], 6);
  assert_eq!(report["summary"]["missing_snapshot"], 0);
  assert_eq!(report["summary"]["drift"], 0);
  assert_eq!(report["summary"]["tsc_crashed"], 0);
  assert_eq!(report["summary"]["timeout"], 0);

  let cases = report["cases"].as_array().expect("cases array");
  assert_eq!(cases.len(), 6);
  assert!(
    cases.iter().all(|case| case["status"] == "ok"),
    "expected all cases to be ok"
  );
}

#[test]
fn verify_snapshots_fails_when_snapshot_is_missing() {
  let node_path = match common::node_path_or_skip("verify-snapshots missing snapshot") {
    Some(path) => path,
    None => return,
  };

  let dir = tempdir().expect("tempdir");
  let root = dir.path().join("conformance-mini");
  fs::create_dir_all(&root).expect("create suite root");
  fs::write(
    root.join("missing.ts"),
    "// @noLib: true\nconst value = 1;\n",
  )
  .expect("write fixture");

  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("verify-snapshots")
    .arg("--root")
    .arg(&root)
    .arg("--filter")
    .arg("missing.ts")
    .arg("--node")
    .arg(node_path)
    .arg("--jobs")
    .arg("1")
    .arg("--timeout-secs")
    .arg("20")
    .arg("--json");

  let output = cmd.assert().failure().get_output().stdout.clone();
  let report: Value = serde_json::from_slice(&output).expect("valid json");

  assert_eq!(report["suite_name"], "conformance-mini");
  assert_eq!(report["summary"]["total"], 1);
  assert_eq!(report["summary"]["missing_snapshot"], 1);

  let cases = report["cases"].as_array().expect("cases array");
  assert_eq!(cases.len(), 1);
  assert_eq!(cases[0]["id"], "missing.ts");
  assert_eq!(cases[0]["status"], "missing_snapshot");
  let detail = cases[0]["detail"].as_str().expect("detail string");
  assert!(
    detail.contains("snapshot not found"),
    "expected missing snapshot detail, got {detail:?}"
  );
}
