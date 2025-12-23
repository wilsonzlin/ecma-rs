use std::fs;
use tempfile::tempdir;
use typecheck_ts_harness_trace23::run_conformance;
use typecheck_ts_harness_trace23::HarnessConfig;
use typecheck_ts_trace23::Profile;

#[test]
fn profile_flag_writes_json() {
  let temp = tempdir().unwrap();
  let path = temp.path().join("profile.json");

  let config = HarnessConfig {
    trace: false,
    profile: Some(path.clone()),
    filter: Some("tiny".to_string()),
  };

  let profile = run_conformance(config)
    .expect("run succeeded")
    .expect("profile produced");

  let data = fs::read_to_string(&path).expect("profile file exists");
  let parsed: Profile = serde_json::from_str(&data).expect("valid json");
  assert!(!parsed.events.is_empty());
  assert_eq!(parsed.events.len(), profile.events.len());
}
