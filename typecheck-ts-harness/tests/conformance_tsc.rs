use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness::diagnostic_norm::sort_diagnostics;
use typecheck_ts_harness::runner::EngineStatus;
use typecheck_ts_harness::tsc::{node_available, typescript_available};
use typecheck_ts_harness::{
  build_filter, run_conformance, CompareMode, ConformanceOptions, FailOn, DEFAULT_EXTENSIONS,
  DEFAULT_PROFILE_OUT,
};

#[test]
fn conformance_tsc_engine_is_ok_and_sorted() {
  let node_path = PathBuf::from("node");
  if !node_available(&node_path) {
    eprintln!("skipping conformance tsc test: node not available");
    return;
  }
  if !typescript_available(&node_path) {
    eprintln!("skipping conformance tsc test: typescript not available (run `cd typecheck-ts-harness && npm ci`)");
    return;
  }

  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let report = run_conformance(ConformanceOptions {
    root,
    filter: build_filter(None).unwrap(),
    filter_pattern: None,
    shard: None,
    json: false,
    update_snapshots: false,
    timeout: Duration::from_secs(5),
    trace: false,
    profile: false,
    profile_out: DEFAULT_PROFILE_OUT.into(),
    extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
    allow_empty: false,
    compare: CompareMode::Tsc,
    node_path,
    span_tolerance: 0,
    allow_mismatches: true,
    jobs: 2,
    manifest: None,
    fail_on: FailOn::New,
  })
  .expect("run conformance");

  assert_eq!(report.summary.total, 5);

  for result in &report.results {
    assert_eq!(
      result.tsc.status,
      EngineStatus::Ok,
      "expected tsc to run successfully for {}",
      result.id
    );

    let mut sorted = result.tsc.diagnostics.clone();
    sort_diagnostics(&mut sorted);
    assert_eq!(
      result.tsc.diagnostics, sorted,
      "tsc diagnostics were not sorted for {}",
      result.id
    );
  }
}

