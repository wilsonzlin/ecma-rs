use std::path::PathBuf;
use std::time::Duration;

use typecheck_ts_harness::runner::EngineStatus;
use typecheck_ts_harness::{
  build_filter, run_conformance, CompareMode, ConformanceOptions, FailOn, DEFAULT_EXTENSIONS,
  DEFAULT_PROFILE_OUT,
};

#[test]
fn strict_null_checks_directive_reaches_tsc() {
  #[cfg(not(feature = "with-node"))]
  {
    eprintln!("skipping strict null checks test: built without node");
    return;
  }

  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let options = ConformanceOptions {
    root,
    filter: build_filter(None).unwrap(),
    filter_pattern: None,
    shard: None,
    json: false,
    update_snapshots: false,
    compare: CompareMode::Tsc,
    node_path: "node".into(),
    span_tolerance: 0,
    timeout: Duration::from_secs(5),
    trace: false,
    profile: false,
    profile_out: DEFAULT_PROFILE_OUT.into(),
    extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
    allow_empty: false,
    allow_mismatches: true,
    jobs: 1,
    manifest: None,
    fail_on: FailOn::New,
  };

  let report = run_conformance(options).expect("run conformance");
  let enabled = report
    .results
    .iter()
    .find(|r| r.id.ends_with("strict_null_checks_enabled.ts"))
    .expect("enabled strictNullChecks fixture");
  let disabled = report
    .results
    .iter()
    .find(|r| r.id.ends_with("strict_null_checks_disabled.ts"))
    .expect("disabled strictNullChecks fixture");

  if enabled.tsc.status != EngineStatus::Ok || disabled.tsc.status != EngineStatus::Ok {
    eprintln!("skipping strict null checks test: tsc unavailable");
    return;
  }

  assert!(
    !enabled.tsc.diagnostics.is_empty(),
    "expected diagnostics when strictNullChecks is enabled"
  );
  assert!(
    disabled.tsc.diagnostics.is_empty(),
    "expected no diagnostics when strictNullChecks is disabled"
  );
}
