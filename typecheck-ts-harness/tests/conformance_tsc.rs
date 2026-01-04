mod common;

use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness::diagnostic_norm::sort_diagnostics;
use typecheck_ts_harness::runner::EngineStatus;
use typecheck_ts_harness::{run_conformance, CompareMode, ConformanceOptions};

#[test]
fn conformance_tsc_engine_is_ok_and_sorted() {
  let node_path = match common::node_path_or_skip("conformance tsc test") {
    Some(path) => path,
    None => return,
  };

  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let mut options = ConformanceOptions::new(root);
  options.compare = CompareMode::Tsc;
  options.node_path = node_path;
  options.timeout = Duration::from_secs(5);
  options.allow_mismatches = true;
  options.jobs = 2;

  let report = run_conformance(options).expect("run conformance");

  assert_eq!(report.summary.total, 6);

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
