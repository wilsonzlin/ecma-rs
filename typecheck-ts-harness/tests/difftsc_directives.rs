use assert_cmd::Command;
use serde_json::Value;
use std::path::Path;

#[test]
fn difftsc_honors_fixture_directives_for_rust_runs() {
  let suite = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("difftsc");
  let baseline = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("baselines")
    .join("difftsc")
    .join("this_param_call.json");

  #[allow(deprecated)]
  let output = Command::cargo_bin("typecheck-ts-harness")
    .expect("binary")
    .arg("difftsc")
    .arg("--suite")
    .arg(&suite)
    .arg("--use-baselines")
    .arg("--compare-rust")
    .arg("--allow-mismatches")
    .arg("--json")
    .assert()
    .success()
    .get_output()
    .stdout
    .clone();

  let json: Value = serde_json::from_slice(&output).expect("json output");
  let results = json
    .get("results")
    .and_then(|r| r.as_array())
    .expect("results array");
  let case = results
    .iter()
    .find(|case| case.get("name").and_then(|n| n.as_str()) == Some("this_param_call"))
    .expect("this_param_call case present");

  let baseline_json: Value =
    serde_json::from_str(&std::fs::read_to_string(&baseline).expect("read baseline"))
      .expect("parse baseline json");
  let baseline_opts = baseline_json
    .get("metadata")
    .and_then(|m| m.get("options"))
    .and_then(|o| o.as_object())
    .expect("baseline metadata options");

  let harness = case
    .get("harness_options")
    .and_then(|o| o.as_object())
    .expect("harness_options present");
  assert_eq!(
    harness.get("strict").and_then(|v| v.as_bool()),
    Some(true),
    "expected strict=true in computed harness options; case: {case:?}"
  );

  let tsc = case
    .get("tsc_options")
    .and_then(|o| o.as_object())
    .expect("tsc_options present");
  assert_eq!(
    tsc.get("strict").and_then(|v| v.as_bool()),
    Some(true),
    "expected strict=true in computed tsc options; case: {case:?}"
  );
  assert_eq!(
    tsc.get("noImplicitAny").and_then(|v| v.as_bool()),
    Some(true),
    "expected noImplicitAny=true in computed tsc options; case: {case:?}"
  );

  assert_eq!(
    baseline_opts.get("strict").and_then(|v| v.as_bool()),
    Some(true),
    "expected strict=true in baseline metadata; baseline: {baseline_json:?}"
  );
  assert_eq!(
    baseline_opts.get("noImplicitAny").and_then(|v| v.as_bool()),
    Some(true),
    "expected noImplicitAny=true in baseline metadata; baseline: {baseline_json:?}"
  );
}
