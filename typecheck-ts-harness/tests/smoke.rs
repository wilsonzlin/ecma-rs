use assert_cmd::Command;
use serde_json::{to_string, Value};
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use tempfile::tempdir;
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;
use typecheck_ts_harness::JsonReport;
use typecheck_ts_harness::TestOutcome;

const HARNESS_SLEEP_ENV: &str = "HARNESS_SLEEP_MS_PER_TEST";
const CLI_TIMEOUT: Duration = Duration::from_secs(30);

fn harness_cli() -> Command {
  assert_cmd::cargo::cargo_bin_cmd!("typecheck-ts-harness")
}

fn conformance_options(root: PathBuf) -> ConformanceOptions {
  let mut options = ConformanceOptions::new(root);
  options.compare = CompareMode::None;
  options.timeout = Duration::from_secs(2);
  options.allow_mismatches = true;
  options
}

fn write_fixtures() -> (tempfile::TempDir, PathBuf) {
  let dir = tempdir().expect("tempdir");
  let root = dir.path().to_path_buf();

  fs::create_dir_all(root.join("ok")).unwrap();
  fs::create_dir_all(root.join("err")).unwrap();
  fs::create_dir_all(root.join("multi")).unwrap();

  let header = "// @noLib: true\n";
  fs::write(root.join("ok/basic.ts"), format!("{header}const x = 1;\n")).unwrap();
  fs::write(
    root.join("err/parse_error.ts"),
    format!("{header}const = ;\n"),
  )
  .unwrap();

  let multi = format!(
    "{header}// @filename: a.ts\nexport const a = 1;\n// @filename: b.ts\nexport const b = a;\n"
  );
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
  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
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
  serde_json::from_slice(&output).expect("valid json")
}

fn normalize_report(report: &mut JsonReport) {
  report.results.sort_by(|a, b| a.id.cmp(&b.id));
  for result in report.results.iter_mut() {
    result.duration_ms = 0;
    result.rust_ms = None;
    result.tsc_ms = None;
    result.diff_ms = None;
  }
}

#[test]
fn smoke_runs_on_small_fixtures() {
  let (_dir, root) = write_fixtures();

  let options = conformance_options(root);

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

  let options = conformance_options(root);

  let mut first = run_conformance(options.clone()).expect("run_conformance");
  let mut second = run_conformance(options).expect("run_conformance");

  for report in [&mut first, &mut second] {
    for result in report.results.iter_mut() {
      result.duration_ms = 0;
      result.rust_ms = None;
      result.tsc_ms = None;
      result.diff_ms = None;
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
fn cli_requires_suite_unless_allowed_to_be_empty() {
  let dir = tempdir().expect("tempdir");

  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("conformance")
    .arg("--root")
    .arg(dir.path())
    .arg("--compare")
    .arg("none")
    .arg("--timeout-secs")
    .arg("1");

  let assert = cmd.assert().failure();
  let stderr = String::from_utf8_lossy(&assert.get_output().stderr);
  assert!(
    stderr.contains("git submodule update --init --recursive parse-js/tests/TypeScript"),
    "stderr should hint at initializing the TypeScript submodule: {stderr}"
  );
  assert!(
    stderr.contains("--root"),
    "stderr should mention overriding the root: {stderr}"
  );

  let mut allow_cmd = harness_cli();
  allow_cmd.timeout(CLI_TIMEOUT);
  allow_cmd
    .arg("conformance")
    .arg("--root")
    .arg(dir.path())
    .arg("--compare")
    .arg("none")
    .arg("--timeout-secs")
    .arg("1")
    .arg("--allow-empty");

  allow_cmd.assert().success();
}

#[test]
fn cli_runs_with_filter_and_json() {
  let (_dir, root) = write_fixtures();

  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
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
  let report: JsonReport = serde_json::from_slice(&output).expect("valid json");
  assert_eq!(report.summary.total, 1);
  assert!(matches!(
    report.results.first().map(|r| r.outcome),
    Some(TestOutcome::Match)
  ));
}

#[test]
fn cli_json_report_is_machine_readable_with_trace_enabled() {
  let (_dir, root) = write_fixtures();

  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
  cmd
    .arg("conformance")
    .arg("--root")
    .arg(&root)
    .arg("--compare")
    .arg("none")
    .arg("--json")
    .arg("--trace")
    .arg("--allow-mismatches")
    .arg("--timeout-secs")
    .arg("5");

  let assert = cmd.assert().success();
  let output = assert.get_output();

  let report: JsonReport = serde_json::from_slice(&output.stdout).expect("valid json report");
  assert_eq!(report.summary.total, 3);
  assert!(
    !output.stderr.is_empty(),
    "expected trace output on stderr when --trace is enabled"
  );
}

#[test]
fn fail_on_new_ignores_manifested_expectations() {
  let (_dir, root) = write_fixtures();
  fs::write(root.join("err/type_error.ts"), "// @noLib: true\nconst = ;").unwrap();

  let manifest =
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/conformance_manifest.toml");

  let mut options = conformance_options(root);
  options.manifest = Some(manifest);

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

  let header = "// @noLib: true\n";
  fs::write(root.join("fast.ts"), format!("{header}const fast = 1;\n")).unwrap();
  fs::write(root.join("slow.ts"), format!("{header}const slow = 1;\n")).unwrap();

  let mut cmd = harness_cli();
  cmd.timeout(CLI_TIMEOUT);
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
    // Simulate a slow case that must be cancelled when the per-test deadline
    // fires (the harness should not wait for this sleep to fully elapse).
    .env("HARNESS_SLEEP_MS_PER_TEST", "slow=5000");

  let start = Instant::now();
  let assert = cmd.assert().success();
  let elapsed = start.elapsed();
  assert!(
    elapsed < Duration::from_secs(3),
    "expected the conformance command to return shortly after the 1s timeout; got {elapsed:?}"
  );

  let output = assert.get_output().stdout.clone();
  let report: JsonReport = serde_json::from_slice(&output).expect("valid json");
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

  let slow_ms = report
    .results
    .iter()
    .find(|r| r.id.ends_with("slow.ts"))
    .map(|r| r.duration_ms)
    .unwrap_or_default();
  assert!(
    slow_ms <= 1500,
    "expected timed-out case duration_ms to be near the 1s timeout, got {slow_ms}"
  );
}

#[test]
fn json_results_are_stably_ordered_with_parallel_execution() {
  let (_dir, root) = write_fixtures();
  let _guard = EnvGuard::set(HARNESS_SLEEP_ENV, "parse_error=50,multi=25");

  let jobs = std::cmp::max(
    2,
    std::thread::available_parallelism()
      .map(|count| count.get())
      .unwrap_or(1),
  );
  let mut options = conformance_options(root);
  options.json = true;
  options.timeout = Duration::from_secs(5);
  options.jobs = jobs;

  let first = run_conformance(options.clone()).expect("run_conformance first");
  let second = run_conformance(options).expect("run_conformance second");

  let ids: Vec<_> = first.results.iter().map(|r| r.id.clone()).collect();
  let mut sorted_ids = ids.clone();
  sorted_ids.sort();
  assert_eq!(ids, sorted_ids);

  let ids_second: Vec<_> = second.results.iter().map(|r| r.id.clone()).collect();
  assert_eq!(ids, ids_second);
}

#[test]
fn difftsc_results_are_sorted_with_parallel_execution() {
  let dir = tempdir().expect("tempdir");
  let suite = dir.path().join("difftsc");
  fs::create_dir_all(&suite).expect("create suite directory");
  // Use a tiny suite so this ordering test runs quickly in debug builds. We
  // intentionally *do not* provide baselines for these cases; difftsc should
  // still return JSON output in a deterministic order when `--allow-mismatches`
  // is set.
  fs::write(suite.join("a.ts"), "// @noLib: true\nconst a = 1;\n").unwrap();
  fs::write(suite.join("b.ts"), "// @noLib: true\nconst b = 1;\n").unwrap();

  let run = || -> Value {
    let mut cmd = harness_cli();
    cmd.timeout(CLI_TIMEOUT);
    cmd
      .arg("difftsc")
      .arg("--suite")
      .arg(&suite)
      .arg("--compare-rust")
      .arg("--use-baselines")
      .arg("--json")
      .arg("--jobs")
      .arg("2")
      .arg("--allow-mismatches");

    let output = cmd.assert().success().get_output().stdout.clone();
    serde_json::from_slice(&output).expect("json output")
  };

  let first = run();
  let second = run();

  let extract_ids = |report: &Value| -> Vec<String> {
    let results = report["results"]
      .as_array()
      .map(|arr| arr.as_slice())
      .unwrap_or(&[]);
    results
      .iter()
      .filter_map(|case| {
        case
          .get("name")
          .and_then(|n| n.as_str())
          .map(|s| s.to_string())
      })
      .collect()
  };

  let ids = extract_ids(&first);
  let mut sorted = ids.clone();
  sorted.sort();

  assert!(!ids.is_empty());
  assert_eq!(ids, sorted);
  assert_eq!(ids, extract_ids(&second));
}
