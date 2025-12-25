use assert_cmd::Command;
use serde_json::to_string;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;
use tempfile::tempdir;
use typecheck_ts_harness::build_filter;
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::FailOn;
use typecheck_ts_harness::JsonReport;
use typecheck_ts_harness::TestOutcome;
use typecheck_ts_harness::DEFAULT_EXTENSIONS;

const HARNESS_SLEEP_ENV: &str = "HARNESS_SLEEP_MS_PER_TEST";

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

struct EnvGuard {
  key: &'static str,
  previous: Option<String>,
}

impl EnvGuard {
  fn set(key: &'static str, value: &str) -> Self {
    let previous = std::env::var(key).ok();
    std::env::set_var(key, value);
    EnvGuard { key, previous }
  }
}

impl Drop for EnvGuard {
  fn drop(&mut self) {
    if let Some(prev) = self.previous.take() {
      std::env::set_var(self.key, prev);
    } else {
      std::env::remove_var(self.key);
    }
  }
}

fn run_cli_json_report(root: &Path) -> JsonReport {
  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd
    .arg("conformance")
    .arg("--root")
    .arg(root)
    .arg("--compare")
    .arg("none")
    .arg("--json")
    .arg("--timeout-secs")
    .arg("5")
    .arg("--allow-mismatches");

  let output = cmd.assert().success().get_output().stdout.clone();
  let stdout = String::from_utf8_lossy(&output);

  let start = stdout.find('{').expect("json output");
  let json_blob = stdout[start..].trim();

  serde_json::from_str(json_blob).expect("valid json")
}

fn normalize_report(report: &mut JsonReport) {
  report.results.sort_by(|a, b| a.id.cmp(&b.id));
  for result in report.results.iter_mut() {
    result.duration_ms = 0;
  }
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
    extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
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
fn repeated_runs_produce_identical_reports() {
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

  let mut first = run_conformance(options.clone()).expect("run_conformance");
  let mut second = run_conformance(options).expect("run_conformance");

  for report in [&mut first, &mut second] {
    for result in report.results.iter_mut() {
      result.duration_ms = 0;
    }
  }

  assert_eq!(
    to_string(&first).expect("serialize first"),
    to_string(&second).expect("serialize second")
  );
}

#[test]
fn cli_json_output_is_deterministic() {
  let (_dir, root) = write_fixtures();
  let mut first = run_cli_json_report(&root);
  let mut second = run_cli_json_report(&root);

  let is_sorted = |report: &JsonReport| report.results.windows(2).all(|w| w[0].id <= w[1].id);

  assert!(is_sorted(&first));
  assert!(is_sorted(&second));

  normalize_report(&mut first);
  normalize_report(&mut second);

  assert_eq!(
    serde_json::to_string(&first).expect("serialize first"),
    serde_json::to_string(&second).expect("serialize second")
  );
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
    extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
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

#[test]
fn conformance_enforces_timeouts_per_test() {
  let dir = tempdir().expect("tempdir");
  let root = dir.path().to_path_buf();

  fs::write(root.join("fast.ts"), "const fast = 1;\n").unwrap();
  fs::write(root.join("slow.ts"), "const slow = 1;\n").unwrap();

  #[allow(deprecated)]
  let mut cmd = Command::cargo_bin("typecheck-ts-harness").expect("binary");
  cmd
    .arg("conformance")
    .arg("--root")
    .arg(&root)
    .arg("--compare")
    .arg("none")
    .arg("--json")
    .arg("--timeout-secs")
    .arg("1")
    .arg("--allow-mismatches")
    .env("HARNESS_SLEEP_MS_PER_TEST", "slow=1500");

  let output = cmd.assert().success().get_output().stdout.clone();
  let stdout = String::from_utf8_lossy(&output);

  let start = stdout.find('{').expect("json output");
  let json_blob = stdout[start..].trim();

  let report: JsonReport = serde_json::from_str(json_blob).expect("valid json");
  assert_eq!(report.summary.total, 2);
  assert_eq!(report.summary.outcomes.timeout, 1);
  assert!(report
    .results
    .iter()
    .any(|r| r.id.ends_with("fast.ts") && r.outcome == TestOutcome::Match));
  assert!(report
    .results
    .iter()
    .any(|r| r.id.ends_with("slow.ts") && r.outcome == TestOutcome::Timeout));
}

#[test]
fn json_results_are_stably_ordered_with_parallel_execution() {
  let (_dir, root) = write_fixtures();
  let _guard = EnvGuard::set(HARNESS_SLEEP_ENV, "parse_error=50,multi=25");

  let jobs = std::cmp::max(2, num_cpus::get());
  let options = ConformanceOptions {
    root: root.clone(),
    filter: build_filter(None).unwrap(),
    filter_pattern: None,
    shard: None,
    json: true,
    update_snapshots: false,
    compare: CompareMode::None,
    node_path: "node".into(),
    span_tolerance: 0,
    timeout: Duration::from_secs(5),
    trace: false,
    profile: false,
    manifest: None,
    fail_on: FailOn::New,
    allow_mismatches: true,
    extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
    allow_empty: false,
    profile_out: typecheck_ts_harness::DEFAULT_PROFILE_OUT.into(),
    jobs,
  };

  let first = run_conformance(options.clone()).expect("run_conformance first");
  let second = run_conformance(options).expect("run_conformance second");

  let ids: Vec<_> = first.results.iter().map(|r| r.id.clone()).collect();
  let mut sorted_ids = ids.clone();
  sorted_ids.sort();
  assert_eq!(ids, sorted_ids);

  let ids_second: Vec<_> = second.results.iter().map(|r| r.id.clone()).collect();
  assert_eq!(ids, ids_second);
}
