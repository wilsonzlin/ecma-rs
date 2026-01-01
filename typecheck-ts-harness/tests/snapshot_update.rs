use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness::{run_conformance, CompareMode, ConformanceOptions, HarnessError};

#[test]
fn updating_snapshots_requires_tsc() {
  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let mut options = ConformanceOptions::new(root);
  options.update_snapshots = true;
  options.timeout = Duration::from_secs(1);
  options.compare = CompareMode::Snapshot;
  // Force `tsc` to be unavailable regardless of the environment.
  options.node_path = PathBuf::from("__typecheck_ts_harness_missing_node__");
  options.allow_mismatches = true;

  let err = run_conformance(options).expect_err("expected snapshot update to require tsc");
  match err {
    HarnessError::Typecheck(msg) => assert!(
      msg.contains("cannot update snapshots") && msg.contains("tsc unavailable"),
      "unexpected error message: {msg}"
    ),
    other => panic!("unexpected error: {other:?}"),
  }
}
