use conformance_harness::{Expectations, TimeoutManager};
use std::collections::HashMap;
use std::fs;
use std::time::Duration;
use tempfile::tempdir;
use test262_semantic::discover::discover_tests;
use test262_semantic::executor::default_executor;
use test262_semantic::report::TestOutcome;
use test262_semantic::runner::{expand_cases, Filter};

#[test]
fn vm_js_executor_smoke_pass_and_timeout() {
  let temp = tempdir().unwrap();

  // Minimal fake test262 checkout: harness + test directories.
  fs::create_dir_all(temp.path().join("harness")).unwrap();
  fs::write(temp.path().join("harness/assert.js"), "").unwrap();
  fs::write(temp.path().join("harness/sta.js"), "").unwrap();

  let test_dir = temp.path().join("test");
  fs::create_dir_all(&test_dir).unwrap();

  // A tiny script that should execute successfully in both strict and non-strict modes.
  fs::write(
    test_dir.join("pass.js"),
    "/*---\nflags: []\n---*/\nvar x = 1;\n",
  )
  .unwrap();

  // A tight loop that should cooperatively time out via the shared interrupt flag.
  fs::write(
    test_dir.join("timeout.js"),
    "/*---\nflags: [onlyStrict]\n---*/\nwhile (true) {}\n",
  )
  .unwrap();

  let discovered = discover_tests(temp.path()).unwrap();
  let cases = expand_cases(&discovered, &Filter::All).unwrap();

  let expectations = Expectations::empty();
  let executor = default_executor();
  let timeout_manager = TimeoutManager::new();

  let results = test262_semantic::runner::run_cases(
    temp.path(),
    &cases,
    &expectations,
    executor.as_ref(),
    Duration::from_millis(100),
    &timeout_manager,
  );

  let mut by_id: HashMap<(&str, test262_semantic::report::Variant), &test262_semantic::report::TestResult> =
    HashMap::new();
  for result in &results {
    by_id.insert((result.id.as_str(), result.variant), result);
  }

  // pass.js generates both strict and non-strict variants.
  assert_eq!(
    by_id[&("pass.js", test262_semantic::report::Variant::NonStrict)].outcome,
    TestOutcome::Passed
  );
  assert_eq!(
    by_id[&("pass.js", test262_semantic::report::Variant::Strict)].outcome,
    TestOutcome::Passed
  );

  // timeout.js is onlyStrict and should deterministically time out.
  assert_eq!(
    by_id[&("timeout.js", test262_semantic::report::Variant::Strict)].outcome,
    TestOutcome::TimedOut
  );
}
