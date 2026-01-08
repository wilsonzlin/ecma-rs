use anyhow::{bail, Context, Result};
use clap::Args;
use serde::{Deserialize, Serialize};
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

#[derive(Args, Debug)]
pub struct CompareArgs {
  /// Path to the baseline JSON report.
  #[arg(long, value_name = "PATH")]
  pub baseline: PathBuf,

  /// Path to the current JSON report.
  #[arg(long, value_name = "PATH")]
  pub current: PathBuf,

  /// Exit with a non-zero code when regressions are detected.
  #[arg(long)]
  pub fail_on_regression: bool,
}

pub const REPORT_SCHEMA_VERSION: u32 = 1;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Report {
  pub schema_version: u32,
  pub summary: Summary,
  pub results: Vec<TestResult>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
pub struct Summary {
  pub total: usize,
  pub passed: usize,
  pub failed: usize,
  pub timed_out: usize,
  pub skipped: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TestResult {
  pub id: String,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub variant: Option<String>,
  pub outcome: TestOutcome,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TestOutcome {
  Passed,
  Failed,
  TimedOut,
  Skipped,
}

impl TestOutcome {
  fn is_fail_like(self) -> bool {
    matches!(self, Self::Failed | Self::TimedOut)
  }
}

impl fmt::Display for TestOutcome {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let value = match self {
      TestOutcome::Passed => "passed",
      TestOutcome::Failed => "failed",
      TestOutcome::TimedOut => "timed_out",
      TestOutcome::Skipped => "skipped",
    };
    f.write_str(value)
  }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct ResultKey {
  pub id: String,
  pub variant: Option<String>,
}

impl ResultKey {
  fn from_result(result: &TestResult) -> Self {
    Self {
      id: result.id.clone(),
      variant: result.variant.clone(),
    }
  }
}

impl fmt::Display for ResultKey {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.variant {
      Some(variant) => write!(f, "{}#{variant}", self.id),
      None => f.write_str(&self.id),
    }
  }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OutcomeChange {
  pub key: ResultKey,
  pub baseline: TestOutcome,
  pub current: TestOutcome,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct Comparison {
  pub regressions: Vec<OutcomeChange>,
  pub improvements: Vec<OutcomeChange>,
  pub new_tests: Vec<ResultKey>,
  pub removed_tests: Vec<ResultKey>,
}

pub fn compare_reports(baseline: &Report, current: &Report) -> Result<Comparison> {
  if baseline.schema_version != current.schema_version {
    bail!(
      "report schema_version mismatch: baseline={} current={}",
      baseline.schema_version,
      current.schema_version
    );
  }

  let baseline_results = index_results("baseline", &baseline.results)?;
  let current_results = index_results("current", &current.results)?;

  let mut all_keys: BTreeSet<ResultKey> = baseline_results.keys().cloned().collect();
  all_keys.extend(current_results.keys().cloned());

  let mut comparison = Comparison::default();

  for key in all_keys {
    match (baseline_results.get(&key), current_results.get(&key)) {
      (Some(&baseline_outcome), Some(&current_outcome)) => {
        if matches!(baseline_outcome, TestOutcome::Passed)
          && current_outcome.is_fail_like()
        {
          comparison.regressions.push(OutcomeChange {
            key,
            baseline: baseline_outcome,
            current: current_outcome,
          });
        } else if baseline_outcome.is_fail_like() && matches!(current_outcome, TestOutcome::Passed)
        {
          comparison.improvements.push(OutcomeChange {
            key,
            baseline: baseline_outcome,
            current: current_outcome,
          });
        }
      }
      (None, Some(_)) => comparison.new_tests.push(key),
      (Some(_), None) => comparison.removed_tests.push(key),
      (None, None) => unreachable!("key came from either baseline or current"),
    }
  }

  Ok(comparison)
}

fn index_results(label: &str, results: &[TestResult]) -> Result<BTreeMap<ResultKey, TestOutcome>> {
  let mut map = BTreeMap::new();
  for result in results {
    let key = ResultKey::from_result(result);
    let previous = map.insert(key.clone(), result.outcome);
    if previous.is_some() {
      bail!("{label} report contains duplicate result key `{key}`");
    }
  }
  Ok(map)
}

pub fn run_cli(args: CompareArgs) -> Result<ExitCode> {
  let baseline = read_report(&args.baseline)
    .with_context(|| format!("load baseline report {}", args.baseline.display()))?;
  let current = read_report(&args.current)
    .with_context(|| format!("load current report {}", args.current.display()))?;

  let comparison = compare_reports(&baseline, &current)?;

  print_summary(&comparison);
  print_details(&comparison);

  Ok(if args.fail_on_regression && !comparison.regressions.is_empty() {
    ExitCode::FAILURE
  } else {
    ExitCode::SUCCESS
  })
}

fn read_report(path: &Path) -> Result<Report> {
  let raw = fs::read_to_string(path)?;
  let report: Report =
    serde_json::from_str(&raw).with_context(|| format!("parse report JSON {}", path.display()))?;
  if report.schema_version != REPORT_SCHEMA_VERSION {
    bail!(
      "unsupported report schema_version {} (expected {})",
      report.schema_version,
      REPORT_SCHEMA_VERSION
    );
  }
  Ok(report)
}

fn print_summary(comparison: &Comparison) {
  println!("test262 semantic report comparison:");
  println!("  regressions: {}", comparison.regressions.len());
  println!("  improvements: {}", comparison.improvements.len());
  println!("  new tests: {}", comparison.new_tests.len());
  println!("  removed tests: {}", comparison.removed_tests.len());
}

fn print_details(comparison: &Comparison) {
  if !comparison.new_tests.is_empty() {
    println!();
    println!("New tests:");
    for key in &comparison.new_tests {
      println!("  {key}");
    }
  }

  if !comparison.improvements.is_empty() {
    println!();
    println!("Improvements:");
    for change in &comparison.improvements {
      println!(
        "  {}: {} -> {}",
        change.key, change.baseline, change.current
      );
    }
  }

  if !comparison.removed_tests.is_empty() {
    println!();
    println!("Removed tests:");
    for key in &comparison.removed_tests {
      println!("  {key}");
    }
  }

  if !comparison.regressions.is_empty() {
    eprintln!();
    eprintln!("Regressions:");
    for change in &comparison.regressions {
      eprintln!(
        "  {}: {} -> {}",
        change.key, change.baseline, change.current
      );
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn compare_reports_classifies_deltas_and_sorts() {
    let baseline = Report {
      schema_version: REPORT_SCHEMA_VERSION,
      summary: Summary::default(),
      results: vec![
        TestResult {
          id: "e".into(),
          variant: None,
          outcome: TestOutcome::Passed,
        },
        TestResult {
          id: "b".into(),
          variant: None,
          outcome: TestOutcome::Failed,
        },
        TestResult {
          id: "c".into(),
          variant: Some("strict".into()),
          outcome: TestOutcome::Passed,
        },
        TestResult {
          id: "a".into(),
          variant: None,
          outcome: TestOutcome::Passed,
        },
        TestResult {
          id: "c".into(),
          variant: Some("nonstrict".into()),
          outcome: TestOutcome::Passed,
        },
      ],
    };

    let current = Report {
      schema_version: REPORT_SCHEMA_VERSION,
      summary: Summary::default(),
      results: vec![
        TestResult {
          id: "c".into(),
          variant: Some("nonstrict".into()),
          outcome: TestOutcome::Failed,
        },
        TestResult {
          id: "d".into(),
          variant: None,
          outcome: TestOutcome::Passed,
        },
        TestResult {
          id: "a".into(),
          variant: None,
          outcome: TestOutcome::Failed,
        },
        TestResult {
          id: "b".into(),
          variant: None,
          outcome: TestOutcome::Passed,
        },
        TestResult {
          id: "c".into(),
          variant: Some("strict".into()),
          outcome: TestOutcome::Passed,
        },
      ],
    };

    let comparison = compare_reports(&baseline, &current).unwrap();

    assert_eq!(
      comparison.regressions,
      vec![
        OutcomeChange {
          key: ResultKey {
            id: "a".into(),
            variant: None
          },
          baseline: TestOutcome::Passed,
          current: TestOutcome::Failed,
        },
        OutcomeChange {
          key: ResultKey {
            id: "c".into(),
            variant: Some("nonstrict".into())
          },
          baseline: TestOutcome::Passed,
          current: TestOutcome::Failed,
        }
      ]
    );

    assert_eq!(
      comparison.improvements,
      vec![OutcomeChange {
        key: ResultKey {
          id: "b".into(),
          variant: None
        },
        baseline: TestOutcome::Failed,
        current: TestOutcome::Passed,
      }]
    );

    assert_eq!(
      comparison.new_tests,
      vec![ResultKey {
        id: "d".into(),
        variant: None
      }]
    );

    assert_eq!(
      comparison.removed_tests,
      vec![ResultKey {
        id: "e".into(),
        variant: None
      }]
    );
  }

  #[test]
  fn compare_reports_rejects_schema_mismatch() {
    let baseline = Report {
      schema_version: 1,
      summary: Summary::default(),
      results: vec![],
    };
    let current = Report {
      schema_version: 2,
      summary: Summary::default(),
      results: vec![],
    };

    let err = compare_reports(&baseline, &current).unwrap_err();
    assert!(err.to_string().contains("report schema_version mismatch"));
  }
}
