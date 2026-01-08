use crate::discover::{read_utf8_file, DiscoveredTest};
use crate::executor::{ExecError, Executor, JsError};
use crate::frontmatter::{parse_test_source, Frontmatter};
use crate::harness::{assemble_source_with_mode, HarnessMode};
use crate::report::{
  ExpectationOutcome, ExpectedOutcome, MismatchSummary, Summary, TestOutcome, TestResult, Variant,
};
use anyhow::{anyhow, bail, Context, Result};
use conformance_harness::{
  AppliedExpectation, ExpectationKind, Expectations, Shard, TimeoutManager,
};
use globset::{Glob, GlobSet, GlobSetBuilder};
use regex::Regex;
use std::path::{Path, PathBuf};
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::{Duration, Instant};

#[derive(Debug, Clone)]
pub struct TestCase {
  pub id: String,
  pub path: PathBuf,
  pub variant: Variant,
  pub expected: ExpectedOutcome,
  pub metadata: Frontmatter,
  pub body: String,
}

#[derive(Debug, Clone)]
pub enum Filter {
  All,
  Glob(GlobSet),
  Regex(Regex),
}

pub fn build_filter(pattern: Option<&str>) -> Result<Filter> {
  match pattern {
    None => Ok(Filter::All),
    Some(raw) => {
      if let Ok(glob) = Glob::new(raw) {
        let mut builder = GlobSetBuilder::new();
        builder.add(glob);
        let set = builder
          .build()
          .map_err(|err| anyhow!("invalid glob: {err}"))?;
        return Ok(Filter::Glob(set));
      }

      let regex = Regex::new(raw).map_err(|err| anyhow!("invalid regex: {err}"))?;
      Ok(Filter::Regex(regex))
    }
  }
}

impl Filter {
  pub fn matches(&self, id: &str) -> bool {
    match self {
      Filter::All => true,
      Filter::Glob(set) => set.is_match(id),
      Filter::Regex(re) => re.is_match(id),
    }
  }
}

pub fn expand_cases(selected: &[DiscoveredTest], filter: &Filter) -> Result<Vec<TestCase>> {
  let mut cases = Vec::new();
  for test in selected {
    if !filter.matches(&test.id) {
      continue;
    }
    let raw = read_utf8_file(&test.path)?;
    let parsed = parse_test_source(&raw).with_context(|| format!("parse {}", test.id))?;
    let metadata = parsed.frontmatter.unwrap_or_default();
    let expected = expected_outcome(&metadata);

    for variant in variants_for(&metadata) {
      cases.push(TestCase {
        id: test.id.clone(),
        path: test.path.clone(),
        variant,
        expected: expected.clone(),
        metadata: metadata.clone(),
        body: parsed.body.clone(),
      });
    }
  }

  if cases.is_empty() {
    bail!("no test cases selected");
  }

  cases.sort_by(|a, b| a.id.cmp(&b.id).then_with(|| a.variant.cmp(&b.variant)));
  Ok(cases)
}

fn expected_outcome(metadata: &Frontmatter) -> ExpectedOutcome {
  match &metadata.negative {
    Some(negative) => ExpectedOutcome::Negative {
      phase: negative.phase.clone(),
      typ: negative.typ.clone(),
    },
    None => ExpectedOutcome::Pass,
  }
}

fn variants_for(metadata: &Frontmatter) -> Vec<Variant> {
  let flags: std::collections::HashSet<&str> = metadata.flags.iter().map(|s| s.as_str()).collect();

  if flags.contains("module") {
    return vec![Variant::Module];
  }

  if flags.contains("onlyStrict") {
    return vec![Variant::Strict];
  }
  if flags.contains("noStrict") {
    return vec![Variant::NonStrict];
  }

  vec![Variant::NonStrict, Variant::Strict]
}

pub fn apply_shard(cases: Vec<TestCase>, shard: Option<Shard>) -> Result<Vec<TestCase>> {
  let Some(shard) = shard else {
    return Ok(cases);
  };

  let total = cases.len();
  let filtered = conformance_harness::apply_shard(cases, shard);

  if filtered.is_empty() {
    bail!(
      "shard {}/{} matched no tests out of {total}",
      shard.index + 1,
      shard.total
    );
  }

  Ok(filtered)
}

pub fn run_cases(
  test262_dir: &Path,
  harness_mode: HarnessMode,
  cases: &[TestCase],
  expectations: &Expectations,
  executor: &dyn Executor,
  timeout: Duration,
  timeout_manager: &TimeoutManager,
) -> Vec<TestResult> {
  cases
    .iter()
    .map(|case| {
      let expectation = expectations.lookup(&case.id);
      run_single_case(
        test262_dir,
        harness_mode,
        case,
        expectation,
        executor,
        timeout,
        timeout_manager,
      )
    })
    .collect()
}

fn run_single_case(
  test262_dir: &Path,
  harness_mode: HarnessMode,
  case: &TestCase,
  expectation: AppliedExpectation,
  executor: &dyn Executor,
  timeout: Duration,
  timeout_manager: &TimeoutManager,
) -> TestResult {
  if expectation.expectation.kind == ExpectationKind::Skip {
    return TestResult {
      id: case.id.clone(),
      path: format!("test/{}", case.id),
      variant: case.variant,
      expected: case.expected.clone(),
      outcome: TestOutcome::Skipped,
      error: None,
      skip_reason: expectation.expectation.reason.clone(),
      expectation: expectation_outcome(expectation, false),
      metadata: case.metadata.clone(),
      mismatched: false,
      expected_mismatch: false,
      flaky: false,
    };
  }

  let source = match assemble_source_with_mode(
    test262_dir,
    &case.metadata,
    case.variant,
    &case.body,
    harness_mode,
  ) {
    Ok(src) => src,
    Err(err) => {
      let mismatched = true;
      let expectation_out = expectation_outcome(expectation.clone(), mismatched);
      return TestResult {
        id: case.id.clone(),
        path: format!("test/{}", case.id),
        variant: case.variant,
        expected: case.expected.clone(),
        outcome: TestOutcome::Failed,
        error: Some(err.to_string()),
        skip_reason: None,
        expectation: expectation_out.clone(),
        metadata: case.metadata.clone(),
        mismatched,
        expected_mismatch: mismatched && expectation_out.expectation == ExpectationKind::Xfail,
        flaky: mismatched && expectation_out.expectation == ExpectationKind::Flaky,
      };
    }
  };

  let cancel = Arc::new(AtomicBool::new(false));
  let deadline = Instant::now() + timeout;
  let _timeout_guard = timeout_manager.register(deadline, Arc::clone(&cancel));

  let executed = executor.execute(case, &source, &cancel);

  let (outcome, mut error, skip_reason, js_error) = match executed {
    Ok(()) => (TestOutcome::Passed, None, None, None),
    Err(ExecError::Cancelled) => (
      TestOutcome::TimedOut,
      Some(format!("timeout after {} seconds", timeout.as_secs())),
      None,
      None,
    ),
    Err(ExecError::Skipped(reason)) => (TestOutcome::Skipped, None, Some(reason), None),
    Err(ExecError::Js(err)) => (
      TestOutcome::Failed,
      Some(err.to_report_string()),
      None,
      Some(err),
    ),
  };

  let (mismatched, mismatch_error) = mismatched(
    &case.expected,
    outcome,
    js_error.as_ref(),
    expectation.expectation.kind,
  );
  if let Some(mismatch_error) = mismatch_error {
    error = Some(match error {
      Some(original) => format!("{mismatch_error}\n\n{original}"),
      None => mismatch_error,
    });
  }
  let expectation_out = expectation_outcome(expectation.clone(), mismatched);

  TestResult {
    id: case.id.clone(),
    path: format!("test/{}", case.id),
    variant: case.variant,
    expected: case.expected.clone(),
    outcome,
    error,
    skip_reason,
    expectation: expectation_out.clone(),
    metadata: case.metadata.clone(),
    mismatched,
    expected_mismatch: mismatched && expectation_out.expectation == ExpectationKind::Xfail,
    flaky: mismatched && expectation_out.expectation == ExpectationKind::Flaky,
  }
}

fn mismatched(
  expected: &ExpectedOutcome,
  actual: TestOutcome,
  js_error: Option<&JsError>,
  expectation: ExpectationKind,
) -> (bool, Option<String>) {
  if expectation == ExpectationKind::Skip && actual == TestOutcome::Skipped {
    return (false, None);
  }

  match expected {
    ExpectedOutcome::Pass => (actual != TestOutcome::Passed, None),
    ExpectedOutcome::Negative {
      phase: expected_phase,
      typ: expected_typ,
    } => {
      // A negative test is only considered matched when it fails (not times out) with the expected
      // phase and error type. Treat unknown error types as mismatches to avoid masking
      // misclassifications in the executor/engine.
      if actual != TestOutcome::Failed {
        return (
          true,
          Some(format!(
            "negative expectation mismatch: expected {expected_phase} {expected_typ}, got {actual}"
          )),
        );
      }

      let Some(js_error) = js_error else {
        return (
          true,
          Some(format!(
            "negative expectation mismatch: expected {expected_phase} {expected_typ}, got non-JS failure"
          )),
        );
      };

      if !expected_phase.eq_ignore_ascii_case(js_error.phase.as_str()) {
        return (
          true,
          Some(format!(
            "negative expectation mismatch: expected {expected_phase} {expected_typ}, got {} {}",
            js_error.phase,
            js_error.typ.as_deref().unwrap_or("<unknown error type>"),
          )),
        );
      }

      let Some(actual_typ) = js_error.typ.as_deref() else {
        return (
          true,
          Some(format!(
            "negative expectation mismatch: expected {expected_phase} {expected_typ}, got {} <unknown error type>",
            js_error.phase
          )),
        );
      };

      if actual_typ != expected_typ {
        return (
          true,
          Some(format!(
            "negative expectation mismatch: expected {expected_phase} {expected_typ}, got {} {actual_typ}",
            js_error.phase
          )),
        );
      }

      (false, None)
    }
  }
}

pub fn summarize(results: &[TestResult]) -> Summary {
  let mut summary = Summary::default();
  let mut mismatches = MismatchSummary::default();

  for result in results {
    summary.total += 1;
    match result.outcome {
      TestOutcome::Passed => summary.passed += 1,
      TestOutcome::Failed => summary.failed += 1,
      TestOutcome::TimedOut => summary.timed_out += 1,
      TestOutcome::Skipped => summary.skipped += 1,
    }

    if result.mismatched {
      if result.flaky {
        mismatches.flaky += 1;
      } else if result.expected_mismatch {
        mismatches.expected += 1;
      } else {
        mismatches.unexpected += 1;
      }
    }
  }

  if mismatches.total() > 0 {
    summary.mismatches = Some(mismatches);
  }

  summary
}

fn expectation_outcome(expectation: AppliedExpectation, mismatched: bool) -> ExpectationOutcome {
  ExpectationOutcome {
    expected: expectation.matches(mismatched),
    expectation: expectation.expectation.kind,
    from_manifest: expectation.from_manifest,
    reason: expectation.expectation.reason,
    tracking_issue: expectation.expectation.tracking_issue,
  }
}

pub fn select_all(discovered: &[DiscoveredTest]) -> Vec<DiscoveredTest> {
  let mut out = discovered.to_vec();
  out.sort_by(|a, b| a.id.cmp(&b.id));
  out
}

pub fn select_by_ids(discovered: &[DiscoveredTest], ids: &[String]) -> Result<Vec<DiscoveredTest>> {
  let mut map: std::collections::HashMap<&str, &DiscoveredTest> = std::collections::HashMap::new();
  for test in discovered {
    map.insert(test.id.as_str(), test);
  }

  let mut out = Vec::new();
  for id in ids {
    let found = map
      .get(id.as_str())
      .ok_or_else(|| anyhow!("selected id `{id}` was not discovered"))?;
    out.push((*found).clone());
  }
  out.sort_by(|a, b| a.id.cmp(&b.id));
  Ok(out)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::executor::ExecPhase;
  use conformance_harness::{Expectations, TimeoutManager};
  use serde_json::Value;
  use std::fs;
  use std::sync::atomic::Ordering;
  use std::sync::Arc;
  use tempfile::tempdir;

  #[test]
  fn manifest_prefers_exact_then_glob_then_regex() {
    let manifest = r#"
[[expectations]]
glob = "a/**"
status = "xfail"

[[expectations]]
regex = "a/.*"
status = "flaky"

[[expectations]]
id = "a/b/c.js"
status = "skip"
    "#;

    let expectations = Expectations::from_str(manifest).expect("manifest parsed");
    let applied = expectations.lookup("a/b/c.js");
    assert_eq!(applied.expectation.kind, ExpectationKind::Skip);
  }

  #[test]
  fn report_serializes_stably() {
    let result = TestResult {
      id: "language/example.js".to_string(),
      path: "test/language/example.js".to_string(),
      variant: Variant::NonStrict,
      expected: ExpectedOutcome::Pass,
      outcome: TestOutcome::Passed,
      error: None,
      skip_reason: None,
      expectation: ExpectationOutcome {
        expectation: ExpectationKind::Pass,
        expected: true,
        from_manifest: false,
        reason: None,
        tracking_issue: None,
      },
      metadata: Frontmatter::default(),
      mismatched: false,
      expected_mismatch: false,
      flaky: false,
    };

    let summary = summarize(std::slice::from_ref(&result));
    let report = crate::report::Report {
      schema_version: crate::REPORT_SCHEMA_VERSION,
      summary,
      results: vec![result],
    };
    let json = serde_json::to_string(&report).unwrap();
    let parsed: Value = serde_json::from_str(&json).unwrap();
    assert_eq!(parsed["schema_version"], crate::REPORT_SCHEMA_VERSION);
    assert_eq!(parsed["results"][0]["id"], "language/example.js");
  }

  #[test]
  fn expand_generates_strict_and_non_strict_variants() {
    let temp = tempdir().unwrap();
    fs::create_dir_all(temp.path().join("harness")).unwrap();
    fs::write(temp.path().join("harness/assert.js"), "").unwrap();
    fs::write(temp.path().join("harness/sta.js"), "").unwrap();
    let test_dir = temp.path().join("test");
    fs::create_dir_all(&test_dir).unwrap();
    fs::write(
      test_dir.join("a.js"),
      "/*---\nflags: []\n---*/\nlet x = 1;\n",
    )
    .unwrap();

    let discovered = vec![DiscoveredTest {
      id: "a.js".to_string(),
      path: test_dir.join("a.js"),
    }];

    let cases = expand_cases(&discovered, &Filter::All).unwrap();
    let variants: Vec<_> = cases.iter().map(|c| c.variant).collect();
    assert_eq!(variants, vec![Variant::NonStrict, Variant::Strict]);
  }

  #[derive(Debug, Clone)]
  struct DummyExecutor {
    result: crate::executor::ExecResult,
  }

  impl Executor for DummyExecutor {
    fn execute(
      &self,
      _case: &TestCase,
      _source: &str,
      cancel: &Arc<std::sync::atomic::AtomicBool>,
    ) -> crate::executor::ExecResult {
      if cancel.load(Ordering::Relaxed) {
        return Err(ExecError::Cancelled);
      }
      self.result.clone()
    }
  }

  fn test262_fixture() -> tempfile::TempDir {
    let temp = tempdir().unwrap();
    fs::create_dir_all(temp.path().join("harness")).unwrap();
    fs::write(temp.path().join("harness/assert.js"), "").unwrap();
    fs::write(temp.path().join("harness/sta.js"), "").unwrap();
    temp
  }

  fn run_negative_case(js_error: JsError, expected_phase: &str, expected_type: &str) -> TestResult {
    let temp = test262_fixture();
    let case = TestCase {
      id: "language/negative.js".to_string(),
      path: temp.path().join("test/language/negative.js"),
      variant: Variant::NonStrict,
      expected: ExpectedOutcome::Negative {
        phase: expected_phase.to_string(),
        typ: expected_type.to_string(),
      },
      metadata: Frontmatter::default(),
      body: "/* body unused in dummy executor */\n".to_string(),
    };

    let executor = DummyExecutor {
      result: Err(ExecError::Js(js_error)),
    };
    let expectations = Expectations::empty();
    let expectation = expectations.lookup(&case.id);

    let timeout_manager = TimeoutManager::new();
    run_single_case(
      temp.path(),
      &case,
      expectation,
      &executor,
      Duration::from_secs(1),
      &timeout_manager,
    )
  }

  #[test]
  fn negative_parse_expectation_matches_parse_error() {
    let result = run_negative_case(
      JsError::new(
        ExecPhase::Parse,
        Some("SyntaxError".to_string()),
        "unexpected token",
      ),
      "parse",
      "SyntaxError",
    );
    assert_eq!(result.outcome, TestOutcome::Failed);
    assert!(
      !result.mismatched,
      "expected matched negative, got {result:#?}"
    );
  }

  #[test]
  fn negative_parse_expectation_mismatches_runtime_error() {
    let result = run_negative_case(
      JsError::new(ExecPhase::Runtime, Some("TypeError".to_string()), "boom"),
      "parse",
      "SyntaxError",
    );
    assert_eq!(result.outcome, TestOutcome::Failed);
    assert!(result.mismatched);
    assert!(
      result
        .error
        .as_deref()
        .unwrap_or_default()
        .contains("expected parse SyntaxError, got runtime TypeError"),
      "error message should explain mismatch, got: {:#?}",
      result.error
    );
  }

  #[test]
  fn negative_runtime_typeerror_expectation_mismatches_rangeerror() {
    let result = run_negative_case(
      JsError::new(
        ExecPhase::Runtime,
        Some("RangeError".to_string()),
        "out of range",
      ),
      "runtime",
      "TypeError",
    );
    assert_eq!(result.outcome, TestOutcome::Failed);
    assert!(result.mismatched);
    assert!(
      result
        .error
        .as_deref()
        .unwrap_or_default()
        .contains("expected runtime TypeError, got runtime RangeError"),
      "error message should explain mismatch, got: {:#?}",
      result.error
    );
  }

  #[test]
  fn negative_runtime_typeerror_expectation_mismatches_unknown_error_type() {
    let result = run_negative_case(
      JsError::new(ExecPhase::Runtime, None, "unknown error"),
      "runtime",
      "TypeError",
    );
    assert_eq!(result.outcome, TestOutcome::Failed);
    assert!(result.mismatched);
    assert!(
      result
        .error
        .as_deref()
        .unwrap_or_default()
        .contains("unknown error type"),
      "error message should mention unknown type, got: {:#?}",
      result.error
    );
  }
}
