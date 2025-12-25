use assert_cmd::Command;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;
use tempfile::tempdir;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::FailOn;
use typecheck_ts_harness::JsonReport;
use typecheck_ts_harness::TestOutcome;

fn write_fixtures() -> (tempfile::TempDir, PathBuf) {
  let dir = tempdir().expect("tempdir");
  let root = dir.path().to_path_buf();

  fs::create_dir_all(root.join("ok")).unwrap();
  fs::create_dir_all(root.join("err")).unwrap();
  fs::create_dir_all(root.join("multi")).unwrap();

  fs::write(root.join("ok/basic.ts"), "const x = 1;\n").unwrap();
  fs::write(root.join("err/parse_error.ts"), "const = ;\n").unwrap();

  let multi = "// @filename: a.ts\nexport const a = 1;\n// @filename: b.ts\nexport const b = a;\n";
  fs::write(root.join("multi/multi.ts"), multi).unwrap();

  (dir, root)
}

#[test]
fn smoke_runs_on_small_fixtures() {
  let (_dir, root) = write_fixtures();

  let options = ConformanceOptions {
    root: root.clone(),
    filter: build_filter(None).unwrap(),
    filter_pattern: None,
    shard: None,
    json: false,
    update_snapshots: false,
    compare: CompareMode::None,
    node_path: "node".into(),
    span_tolerance: 0,
    timeout: Duration::from_secs(2),
    trace: false,
    profile: false,
    manifest: None,
    fail_on: FailOn::New,
    allow_mismatches: true,
    extensions: typecheck_ts_harness::DEFAULT_EXTENSIONS
      .iter()
      .map(|s| s.to_string())
      .collect(),
    allow_empty: false,
    profile_out: typecheck_ts_harness::DEFAULT_PROFILE_OUT.into(),
    jobs: 1,
  };

  let report = run_conformance(options).expect("run_conformance");
  assert_eq!(report.summary.total, 3);
  assert!(report
    .results
    .iter()
    .any(|r| !r.rust.diagnostics.is_empty()));
}

#[test]
fn cli_runs_with_filter_and_json() {
  let (_dir, root) = write_fixtures();

  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd
    .arg("conformance")
    .arg("--root")
    .arg(root)
    .arg("--filter")
    .arg("*basic*")
    .arg("--compare")
    .arg("none")
    .arg("--json")
    .arg("--timeout-secs")
    .arg("5");

  let output = cmd.assert().success().get_output().stdout.clone();
  let stdout = String::from_utf8_lossy(&output);

  let start = stdout.find('{').expect("json output");
  let json_blob = stdout[start..].trim();

  let report: JsonReport = serde_json::from_str(json_blob).expect("valid json");
  assert_eq!(report.summary.total, 1);
  assert!(matches!(
    report.results.first().map(|r| r.outcome),
    Some(TestOutcome::Match)
  ));
}

#[test]
fn fail_on_new_ignores_manifested_expectations() {
  let (_dir, root) = write_fixtures();
  fs::write(root.join("err/type_error.ts"), "const = ;").unwrap();

  let manifest =
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/conformance_manifest.toml");

  let options = ConformanceOptions {
    root: root.clone(),
    filter: build_filter(None).unwrap(),
    filter_pattern: None,
    shard: None,
    json: false,
    update_snapshots: false,
    compare: CompareMode::None,
    node_path: "node".into(),
    span_tolerance: 0,
    timeout: Duration::from_secs(2),
    trace: false,
    profile: false,
    manifest: Some(manifest),
    fail_on: FailOn::New,
    allow_mismatches: true,
    extensions: typecheck_ts_harness::DEFAULT_EXTENSIONS
      .iter()
      .map(|s| s.to_string())
      .collect(),
    allow_empty: false,
    profile_out: typecheck_ts_harness::DEFAULT_PROFILE_OUT.into(),
    jobs: 1,
  };

  let report = run_conformance(options).expect("run_conformance");
  let parse_expectation = report
    .results
    .iter()
    .find(|r| r.path.ends_with("err/type_error.ts"))
    .and_then(|r| r.expectation.as_ref());
  assert!(parse_expectation.is_some());
}
