use globset::{Glob, GlobSetBuilder};
use std::path::PathBuf;
use std::time::Duration;
use typecheck_ts_harness::runner::EngineStatus;
use typecheck_ts_harness::{run_conformance, CompareMode, ConformanceOptions, Filter};

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

  let mut options = ConformanceOptions::new(root);
  options.filter = filter;
  // The Rust checker may spend several seconds parsing and binding the bundled
  // standard library in debug builds. Keep the harness timeout generous so this
  // test focuses on snapshot plumbing instead of perf.
  options.timeout = Duration::from_secs(15);
  options.compare = CompareMode::Snapshot;
  // Force `tsc` to be unavailable regardless of environment; snapshot mode
  // should still work when not updating snapshots.
  options.node_path = PathBuf::from("__typecheck_ts_harness_missing_node__");
  options.allow_mismatches = true;

  let report = run_conformance(options).expect("run conformance with stored snapshots");

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

#[cfg(unix)]
#[test]
fn conformance_snapshot_mode_does_not_probe_node() {
  use std::fs;
  use std::os::unix::fs::PermissionsExt;
  use tempfile::tempdir;

  let tmp = tempdir().expect("tempdir");
  let fake_node = tmp.path().join("fake-node");
  let marker = tmp.path().join("node-invoked");
  fs::write(
    &fake_node,
    format!(
      "#!/bin/sh\nprintf '%s' invoked > '{}'\nexit 0\n",
      marker.display()
    ),
  )
  .expect("write fake node");
  let mut perms = fs::metadata(&fake_node).expect("metadata").permissions();
  perms.set_mode(0o755);
  fs::set_permissions(&fake_node, perms).expect("chmod fake node");

  let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("conformance-mini");

  let mut builder = GlobSetBuilder::new();
  builder.add(Glob::new("match/basic.ts").unwrap());
  builder.add(Glob::new("mismatch/type_error.ts").unwrap());
  let filter = Filter::Glob(builder.build().unwrap());

  let mut options = ConformanceOptions::new(root);
  options.filter = filter;
  options.timeout = Duration::from_secs(15);
  options.compare = CompareMode::Snapshot;
  options.node_path = fake_node;
  options.allow_mismatches = true;
  options.jobs = 1;

  let report = run_conformance(options).expect("run conformance");
  assert!(
    !marker.exists(),
    "snapshot mode should not invoke the node binary"
  );

  assert_eq!(report.summary.total, 2);
}
