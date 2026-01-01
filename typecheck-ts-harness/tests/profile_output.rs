use serde_json::Value;
use std::path::PathBuf;
use std::time::Duration;
use tempfile::tempdir;
use typecheck_ts_harness::run_conformance;
use typecheck_ts_harness::CompareMode;
use typecheck_ts_harness::ConformanceOptions;

#[test]
fn conformance_profile_emits_actionable_json() {
  let suite = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("fixtures/conformance-mini");
  let dir = tempdir().expect("tempdir");
  let profile_out = dir.path().join("profile.json");

  let mut options = ConformanceOptions::new(suite);
  options.compare = CompareMode::None;
  options.timeout = Duration::from_secs(5);
  options.profile = true;
  options.profile_out = profile_out.clone();

  run_conformance(options).expect("run_conformance");

  assert!(profile_out.exists(), "profile output should be created");
  let raw = std::fs::read_to_string(&profile_out).expect("read profile output");
  let parsed: Value = serde_json::from_str(&raw).expect("profile JSON should parse");

  assert_eq!(
    parsed
      .get("schema_version")
      .and_then(|v| v.as_u64())
      .map(|v| v as u32),
    Some(1),
    "profile should include schema_version=1"
  );

  let tests = parsed
    .get("tests")
    .and_then(|v| v.as_array())
    .expect("tests array");
  assert!(!tests.is_empty(), "profile should contain test entries");

  let ids: Vec<_> = tests
    .iter()
    .filter_map(|entry| {
      entry
        .get("id")
        .and_then(|v| v.as_str())
        .map(|s| s.to_string())
    })
    .collect();
  assert!(!ids.is_empty(), "test entries should have ids");

  let mut sorted = ids.clone();
  sorted.sort();
  assert_eq!(ids, sorted, "profile tests should be sorted by id");

  for entry in tests {
    let durations = entry.get("durations").expect("durations object");
    assert!(
      durations.get("total_ms").and_then(|v| v.as_u64()).is_some(),
      "durations.total_ms should be present"
    );
    assert!(
      durations.get("rust_ms").and_then(|v| v.as_u64()).is_some(),
      "durations.rust_ms should be present for each test"
    );
  }
}
