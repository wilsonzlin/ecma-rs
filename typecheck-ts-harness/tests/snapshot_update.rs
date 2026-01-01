use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness::{
  build_filter, run_conformance, CompareMode, ConformanceOptions, FailOn, HarnessError,
  DEFAULT_EXTENSIONS, DEFAULT_PROFILE_OUT,
};

#[test]
fn updating_snapshots_requires_tsc() {
  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let options = ConformanceOptions {
    root,
    filter: build_filter(None).unwrap(),
    filter_pattern: None,
    shard: None,
    json: false,
    update_snapshots: true,
    timeout: Duration::from_secs(1),
    trace: false,
    profile: false,
    profile_out: DEFAULT_PROFILE_OUT.into(),
    extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
    allow_empty: false,
    compare: CompareMode::Snapshot,
    // Force `tsc` to be unavailable regardless of the environment.
    node_path: PathBuf::from("__typecheck_ts_harness_missing_node__"),
    span_tolerance: 0,
    allow_mismatches: true,
    jobs: 1,
    manifest: None,
    fail_on: FailOn::New,
  };

  let err = run_conformance(options).expect_err("expected snapshot update to require tsc");
  match err {
    HarnessError::Typecheck(msg) => assert!(
      msg.contains("cannot update snapshots") && msg.contains("tsc unavailable"),
      "unexpected error message: {msg}"
    ),
    other => panic!("unexpected error: {other:?}"),
  }
}
