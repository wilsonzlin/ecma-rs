use assert_cmd::Command;
use std::fs;
use std::path::PathBuf;
use std::time::Duration;
use tempfile::tempdir;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::HarnessError;
use typecheck_ts_harness::JsonReport;
use typecheck_ts_harness::TestStatus;
use typecheck_ts_harness::DEFAULT_EXTENSIONS;

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
    shard: None,
    json: false,
    update_snapshots: false,
    timeout: Duration::from_secs(2),
    trace: false,
    profile: false,
    extensions: DEFAULT_EXTENSIONS
      .iter()
      .map(|ext| ext.to_string())
      .collect(),
    allow_empty: false,
  };

  let report = run_conformance(options).expect("run_conformance");
  assert_eq!(report.summary.total, 3);
  assert!(report
    .results
    .iter()
    .any(|r| r.id.ends_with("ok/basic.ts") && r.status == TestStatus::Passed));
  assert!(report
    .results
    .iter()
    .any(|r| r.id.ends_with("err/parse_error.ts") && r.status == TestStatus::ParseError));
  assert!(report
    .results
    .iter()
    .any(|r| r.id.ends_with("multi/multi.ts")));
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
    .arg("**/*basic*")
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
    report.results.first().map(|r| &r.status),
    Some(TestStatus::Passed)
  ));
}

#[test]
fn errors_on_missing_root_unless_allowed() {
  let missing_root = PathBuf::from("nonexistent/test/root");
  let base_options = ConformanceOptions {
    root: missing_root.clone(),
    filter: build_filter(None).unwrap(),
    shard: None,
    json: false,
    update_snapshots: false,
    timeout: Duration::from_millis(10),
    trace: false,
    profile: false,
    extensions: DEFAULT_EXTENSIONS
      .iter()
      .map(|ext| ext.to_string())
      .collect(),
    allow_empty: false,
  };

  let err = run_conformance(base_options.clone()).expect_err("missing root should error");
  assert!(matches!(err, HarnessError::EmptySuite { .. }));

  let report = run_conformance(ConformanceOptions {
    allow_empty: true,
    ..base_options
  })
  .expect("allow_empty should permit empty suites");
  assert_eq!(report.summary.total, 0);
}
