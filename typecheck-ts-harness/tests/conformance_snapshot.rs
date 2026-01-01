use globset::{Glob, GlobSetBuilder};
use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness::runner::EngineStatus;
use typecheck_ts_harness::{
  run_conformance, CompareMode, ConformanceOptions, FailOn, Filter, DEFAULT_EXTENSIONS,
  DEFAULT_PROFILE_OUT,
};

#[test]
fn conformance_snapshot_mode_loads_stored_baselines() {
  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  // The bundled `conformance-mini` suite only ships snapshots for a couple of
  // tests; restrict to those so this test doesn't depend on having `tsc`
  // installed.
  let mut builder = GlobSetBuilder::new();
  builder.add(Glob::new("match/basic.ts").unwrap());
  builder.add(Glob::new("mismatch/type_error.ts").unwrap());
  let filter = Filter::Glob(builder.build().unwrap());

  let report = run_conformance(ConformanceOptions {
    root,
    filter,
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
    compare: CompareMode::Snapshot,
    // Force `tsc` to be unavailable regardless of environment; snapshot mode
    // should still work when not updating snapshots.
    node_path: PathBuf::from("__typecheck_ts_harness_missing_node__"),
    span_tolerance: 0,
    allow_mismatches: true,
    jobs: 1,
    manifest: None,
    fail_on: FailOn::New,
  })
  .expect("run conformance with stored snapshots");

  assert_eq!(report.summary.total, 2);

  for result in &report.results {
    assert_eq!(
      result.tsc.status,
      EngineStatus::Ok,
      "expected snapshot load to succeed for {}",
      result.id
    );
  }
}
