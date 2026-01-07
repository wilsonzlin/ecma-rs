use crate::diagnostic_norm::DiagnosticCode;
use crate::diagnostic_norm::NormalizedDiagnostic;
use crate::expectations::ExpectationKind;
use crate::runner::EngineDiagnostics;
use crate::runner::MismatchDetail;
use crate::runner::TestOutcome;
use anyhow::anyhow;
use anyhow::Context;
use anyhow::Result;
use serde::Deserialize;
use serde::Serialize;
use serde_json::Value;
use std::collections::BTreeMap;
use std::io::Write;
use std::path::Path;
use std::{fs, io};

/// Maximum number of groups/cases to include in the triage report output.
///
/// This can be overridden via the CLI `--top` flag.
pub const DEFAULT_TOP: usize = 25;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum ReportKind {
  Conformance,
  Difftsc,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct CountGroup {
  pub key: String,
  pub count: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct Regression {
  pub id: String,
  pub outcome: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub code: Option<String>,
  pub prefix: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct SuggestedManifestEntry {
  #[serde(skip_serializing_if = "Option::is_none")]
  pub id: Option<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub glob: Option<String>,
  pub status: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub reason: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct BaselineDiff {
  pub baseline_total: usize,
  pub baseline_mismatches: usize,
  pub new_cases: usize,
  pub missing_cases: usize,
  pub regressed: usize,
  pub fixed: usize,
  pub regressions: Vec<Regression>,
  pub fixes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct TriageReport {
  pub kind: ReportKind,
  pub top: usize,
  pub total: usize,
  pub mismatches: usize,
  #[serde(default)]
  pub xpass: usize,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub unexpected_mismatches: Option<usize>,
  pub mismatches_without_code: usize,
  pub top_outcomes: Vec<CountGroup>,
  pub top_codes: Vec<CountGroup>,
  pub top_prefixes: Vec<CountGroup>,
  pub regressions: Vec<Regression>,
  pub suggestions: Vec<SuggestedManifestEntry>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub baseline: Option<BaselineDiff>,
}

#[derive(Debug, Deserialize)]
struct ConformanceReportInput {
  results: Vec<ConformanceCaseInput>,
}

#[derive(Debug, Deserialize)]
struct ConformanceCaseInput {
  id: String,
  outcome: TestOutcome,
  #[serde(default)]
  detail: Option<MismatchDetail>,
  rust: EngineDiagnostics,
  tsc: EngineDiagnostics,
  #[serde(default)]
  expectation: Option<ExpectationInput>,
}

#[derive(Debug, Deserialize)]
struct ExpectationInput {
  #[serde(default)]
  expectation: ExpectationKind,
  #[serde(default)]
  expected: bool,
  #[serde(default)]
  from_manifest: bool,
}

#[derive(Debug, Deserialize)]
struct DifftscReportInput {
  #[serde(default)]
  suite: Option<String>,
  results: Vec<DifftscCaseInput>,
}

#[derive(Debug, Deserialize)]
struct DifftscCaseInput {
  name: String,
  status: DifftscCaseStatus,
  #[serde(default)]
  expectation: Option<ExpectationInput>,
  #[serde(default)]
  diff: Option<DifftscMismatchReport>,
  #[serde(default)]
  type_diff: Option<DifftscTypeMismatchReport>,
  #[serde(default)]
  expected: Option<Vec<NormalizedDiagnostic>>,
  #[serde(default)]
  actual: Option<Vec<NormalizedDiagnostic>>,
}

#[derive(Debug, Clone, Copy, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum DifftscCaseStatus {
  Matched,
  Mismatch,
  BaselineUpdated,
  BaselineMissing,
  TscFailed,
  RustFailed,
  Timeout,
  Skipped,
}

impl DifftscCaseStatus {
  fn is_mismatch(self) -> bool {
    matches!(
      self,
      DifftscCaseStatus::Mismatch
        | DifftscCaseStatus::BaselineMissing
        | DifftscCaseStatus::TscFailed
        | DifftscCaseStatus::RustFailed
        | DifftscCaseStatus::Timeout
    )
  }

  fn as_key(self) -> &'static str {
    match self {
      DifftscCaseStatus::Matched => "match",
      DifftscCaseStatus::Mismatch => "mismatch",
      DifftscCaseStatus::BaselineUpdated => "baseline_updated",
      DifftscCaseStatus::BaselineMissing => "baseline_missing",
      DifftscCaseStatus::TscFailed => "tsc_failed",
      DifftscCaseStatus::RustFailed => "rust_failed",
      DifftscCaseStatus::Timeout => "timeout",
      DifftscCaseStatus::Skipped => "skipped",
    }
  }
}

#[derive(Debug, Clone, Deserialize, Default)]
struct DifftscMismatchReport {
  #[serde(default)]
  missing: Vec<NormalizedDiagnostic>,
  #[serde(default)]
  unexpected: Vec<NormalizedDiagnostic>,
  #[serde(default)]
  code: Vec<DifftscMismatchPair>,
  #[serde(default)]
  span: Vec<DifftscMismatchPair>,
}

#[derive(Debug, Clone, Deserialize)]
struct DifftscMismatchPair {
  expected: NormalizedDiagnostic,
  actual: NormalizedDiagnostic,
}

#[derive(Debug, Clone, Deserialize, Default)]
struct DifftscTypeMismatchReport {
  #[serde(default)]
  missing_exports: Vec<Value>,
  #[serde(default)]
  unexpected_exports: Vec<Value>,
  #[serde(default)]
  mismatched_exports: Vec<Value>,
  #[serde(default)]
  missing_markers: Vec<Value>,
  #[serde(default)]
  unexpected_markers: Vec<Value>,
  #[serde(default)]
  mismatched_markers: Vec<Value>,
}

impl DifftscTypeMismatchReport {
  fn is_empty(&self) -> bool {
    self.missing_exports.is_empty()
      && self.unexpected_exports.is_empty()
      && self.mismatched_exports.is_empty()
      && self.missing_markers.is_empty()
      && self.unexpected_markers.is_empty()
      && self.mismatched_markers.is_empty()
  }
}

pub fn analyze_report_json_str(input: &str, top: usize) -> Result<TriageReport> {
  analyze_report_json_strs(input, None, top)
}

pub fn analyze_report_json_strs(
  input: &str,
  baseline: Option<&str>,
  top: usize,
) -> Result<TriageReport> {
  let value: Value = serde_json::from_str(input).context("parse JSON report")?;
  let baseline_value = match baseline {
    Some(raw) => Some(serde_json::from_str(raw).context("parse baseline JSON report")?),
    None => None,
  };
  analyze_report_value_with_baseline(value, baseline_value, top)
}

pub fn analyze_report_path(path: &Path, top: usize) -> Result<TriageReport> {
  analyze_report_paths(path, None, top)
}

pub fn analyze_report_paths(
  path: &Path,
  baseline: Option<&Path>,
  top: usize,
) -> Result<TriageReport> {
  let content =
    fs::read_to_string(path).with_context(|| format!("read report {}", path.display()))?;
  let value: Value = serde_json::from_str(&content).context("parse JSON report")?;

  let baseline_value = match baseline {
    Some(path) => {
      let content = fs::read_to_string(path)
        .with_context(|| format!("read baseline report {}", path.display()))?;
      Some(serde_json::from_str(&content).context("parse baseline JSON report")?)
    }
    None => None,
  };

  analyze_report_value_with_baseline(value, baseline_value, top)
}

pub fn print_human_summary(report: &TriageReport, out: &mut impl Write) -> io::Result<()> {
  writeln!(
    out,
    "triage: kind={:?} total={} mismatches={} xpass={}",
    report.kind, report.total, report.mismatches, report.xpass
  )?;

  if let Some(unexpected) = report.unexpected_mismatches {
    writeln!(out, "  unexpected mismatches: {unexpected}")?;
  }
  if report.mismatches_without_code > 0 {
    writeln!(
      out,
      "  mismatches without diagnostic code: {}",
      report.mismatches_without_code
    )?;
  }

  write_top(out, "top mismatch outcomes", &report.top_outcomes)?;
  write_top(out, "top diagnostic codes", &report.top_codes)?;
  write_top(out, "top fixture prefixes", &report.top_prefixes)?;

  if !report.regressions.is_empty() {
    writeln!(out, "regressions (top {}):", report.regressions.len())?;
    for case in &report.regressions {
      if let Some(code) = &case.code {
        writeln!(out, "  {}: {} ({})", case.id, case.outcome, code)?;
      } else {
        writeln!(out, "  {}: {}", case.id, case.outcome)?;
      }
    }
  }

  if !report.suggestions.is_empty() {
    writeln!(
      out,
      "suggested manifest entries (top {}):",
      report.suggestions.len()
    )?;
    for entry in &report.suggestions {
      let matcher = if let Some(id) = entry.id.as_ref() {
        format!("id=\"{id}\"")
      } else if let Some(glob) = entry.glob.as_ref() {
        format!("glob=\"{glob}\"")
      } else {
        "<missing matcher>".to_string()
      };
      if let Some(reason) = entry.reason.as_ref() {
        writeln!(
          out,
          "  - {matcher} status=\"{}\" reason=\"{reason}\"",
          entry.status
        )?;
      } else {
        writeln!(out, "  - {matcher} status=\"{}\"", entry.status)?;
      }
    }
  }

  if let Some(baseline) = report.baseline.as_ref() {
    writeln!(
      out,
      "baseline diff: baseline_total={} baseline_mismatches={} regressed={} fixed={} new_cases={} missing_cases={}",
      baseline.baseline_total,
      baseline.baseline_mismatches,
      baseline.regressed,
      baseline.fixed,
      baseline.new_cases,
      baseline.missing_cases
    )?;
    if !baseline.regressions.is_empty() {
      writeln!(
        out,
        "baseline regressions (top {}):",
        baseline.regressions.len()
      )?;
      for case in &baseline.regressions {
        if let Some(code) = &case.code {
          writeln!(out, "  {}: {} ({})", case.id, case.outcome, code)?;
        } else {
          writeln!(out, "  {}: {}", case.id, case.outcome)?;
        }
      }
    }
    if !baseline.fixes.is_empty() {
      writeln!(out, "baseline fixes (top {}):", baseline.fixes.len())?;
      for id in &baseline.fixes {
        writeln!(out, "  {id}")?;
      }
    }
  }

  Ok(())
}

fn write_top(out: &mut impl Write, title: &str, groups: &[CountGroup]) -> io::Result<()> {
  writeln!(out, "{title}:")?;
  if groups.is_empty() {
    writeln!(out, "  (none)")?;
    return Ok(());
  }
  for group in groups {
    writeln!(out, "  {}: {}", group.key, group.count)?;
  }
  Ok(())
}

fn analyze_report_value_with_baseline(
  value: Value,
  baseline: Option<Value>,
  top: usize,
) -> Result<TriageReport> {
  let kind = detect_kind(&value)?;
  if let Some(baseline) = baseline.as_ref() {
    let baseline_kind = detect_kind(baseline)?;
    if baseline_kind != kind {
      return Err(anyhow!(
        "baseline report kind mismatch (input={kind:?}, baseline={baseline_kind:?})"
      ));
    }
  }

  match kind {
    ReportKind::Conformance => {
      let input: ConformanceReportInput =
        serde_json::from_value(value).context("deserialize conformance report")?;
      let summaries = conformance_case_summaries(&input);
      let baseline_diff = match baseline {
        Some(value) => {
          let baseline_input: ConformanceReportInput =
            serde_json::from_value(value).context("deserialize baseline conformance report")?;
          let baseline_summaries = conformance_case_summaries(&baseline_input);
          Some(compute_baseline_diff(&summaries, &baseline_summaries, top))
        }
        None => None,
      };
      let mut report = analyze_conformance(input, top)?;
      report.baseline = baseline_diff;
      Ok(report)
    }
    ReportKind::Difftsc => {
      let input: DifftscReportInput =
        serde_json::from_value(value).context("deserialize difftsc report")?;
      let summaries = difftsc_case_summaries(&input);
      let baseline_diff = match baseline {
        Some(value) => {
          let baseline_input: DifftscReportInput =
            serde_json::from_value(value).context("deserialize baseline difftsc report")?;
          let baseline_summaries = difftsc_case_summaries(&baseline_input);
          Some(compute_baseline_diff(&summaries, &baseline_summaries, top))
        }
        None => None,
      };
      let mut report = analyze_difftsc(input, top)?;
      report.baseline = baseline_diff;
      Ok(report)
    }
  }
}

fn detect_kind(value: &Value) -> Result<ReportKind> {
  if value.get("compare_mode").is_some() {
    return Ok(ReportKind::Conformance);
  }

  if let Some(results) = value.get("results").and_then(|v| v.as_array()) {
    if let Some(first) = results.first() {
      if first.get("outcome").is_some() {
        return Ok(ReportKind::Conformance);
      }
      if first.get("status").is_some() {
        return Ok(ReportKind::Difftsc);
      }
    }
  }

  if value
    .get("summary")
    .and_then(|s| s.get("outcomes"))
    .is_some()
  {
    return Ok(ReportKind::Conformance);
  }
  if value
    .get("summary")
    .and_then(|s| s.get("matched"))
    .is_some()
  {
    return Ok(ReportKind::Difftsc);
  }

  Err(anyhow!(
    "unable to determine report kind (expected conformance or difftsc JSON)"
  ))
}

#[derive(Debug, Clone)]
struct CaseSummary {
  mismatched: bool,
  outcome: String,
  code: Option<String>,
  prefix: String,
}

fn conformance_case_summaries(input: &ConformanceReportInput) -> BTreeMap<String, CaseSummary> {
  let mut summaries = BTreeMap::new();
  for case in &input.results {
    let mismatched = case.outcome != TestOutcome::Match;
    let outcome = outcome_key(case.outcome).to_string();
    let prefix = fixture_prefix(&case.id);
    let code = mismatched
      .then(|| primary_code_from_detail_or_diags(&case.detail, &case.rust, &case.tsc))
      .flatten();
    summaries.insert(
      case.id.clone(),
      CaseSummary {
        mismatched,
        outcome,
        code,
        prefix,
      },
    );
  }
  summaries
}

fn difftsc_case_summaries(input: &DifftscReportInput) -> BTreeMap<String, CaseSummary> {
  let mut summaries = BTreeMap::new();
  for case in &input.results {
    let mismatched = case.status.is_mismatch();
    let outcome = case.status.as_key().to_string();
    let prefix = fixture_prefix(&case.name);
    let code = if case.status == DifftscCaseStatus::Mismatch {
      difftsc_case_outcomes_and_code(case).1
    } else {
      None
    };
    summaries.insert(
      case.name.clone(),
      CaseSummary {
        mismatched,
        outcome,
        code,
        prefix,
      },
    );
  }
  summaries
}

fn compute_baseline_diff(
  current: &BTreeMap<String, CaseSummary>,
  baseline: &BTreeMap<String, CaseSummary>,
  top: usize,
) -> BaselineDiff {
  let baseline_total = baseline.len();
  let baseline_mismatches = baseline.values().filter(|case| case.mismatched).count();

  let new_cases = current
    .keys()
    .filter(|id| !baseline.contains_key(*id))
    .count();
  let missing_cases = baseline
    .keys()
    .filter(|id| !current.contains_key(*id))
    .count();

  let mut regressions = Vec::new();
  let mut regressed = 0usize;
  for (id, case) in current {
    if !case.mismatched {
      continue;
    }
    let baseline_mismatched = baseline
      .get(id)
      .map(|case| case.mismatched)
      .unwrap_or(false);
    if baseline_mismatched {
      continue;
    }
    regressed += 1;
    regressions.push(Regression {
      id: id.clone(),
      outcome: case.outcome.clone(),
      code: case.code.clone(),
      prefix: case.prefix.clone(),
    });
  }

  let mut fixes = Vec::new();
  let mut fixed = 0usize;
  for (id, case) in baseline {
    if !case.mismatched {
      continue;
    }
    match current.get(id) {
      Some(current_case) if !current_case.mismatched => {
        fixed += 1;
        fixes.push(id.clone());
      }
      _ => {}
    }
  }

  regressions.sort_by(|a, b| a.id.cmp(&b.id));
  fixes.sort();

  BaselineDiff {
    baseline_total,
    baseline_mismatches,
    new_cases,
    missing_cases,
    regressed,
    fixed,
    regressions: regressions.into_iter().take(top).collect(),
    fixes: fixes.into_iter().take(top).collect(),
  }
}

fn analyze_conformance(input: ConformanceReportInput, top: usize) -> Result<TriageReport> {
  let mut outcome_counts: BTreeMap<String, usize> = BTreeMap::new();
  let mut code_counts: BTreeMap<String, usize> = BTreeMap::new();
  let mut prefix_counts: BTreeMap<String, usize> = BTreeMap::new();

  let mut mismatches = 0usize;
  let mut xpass = 0usize;
  let mut unexpected_mismatches = 0usize;
  let mut mismatches_without_code = 0usize;

  let mut regressions = Vec::new();
  let mut xpasses = Vec::new();

  for case in &input.results {
    if case.outcome == TestOutcome::Match {
      if case
        .expectation
        .as_ref()
        .is_some_and(|e| {
          e.from_manifest && matches!(e.expectation, ExpectationKind::Xfail | ExpectationKind::Flaky)
        })
      {
        xpass += 1;
        xpasses.push(case.id.clone());
      }
      continue;
    }
    mismatches += 1;

    let outcome_key = outcome_key(case.outcome).to_string();
    *outcome_counts.entry(outcome_key.clone()).or_insert(0) += 1;

    let prefix = fixture_prefix(&case.id);
    *prefix_counts.entry(prefix.clone()).or_insert(0) += 1;

    let code = primary_code_from_detail_or_diags(&case.detail, &case.rust, &case.tsc);
    if let Some(code_key) = code.as_ref().cloned() {
      *code_counts.entry(code_key).or_insert(0) += 1;
    } else {
      mismatches_without_code += 1;
    }

    let unexpected = case
      .expectation
      .as_ref()
      .map(|e| !e.expected)
      .unwrap_or(true);

    if unexpected {
      unexpected_mismatches += 1;
      regressions.push(Regression {
        id: case.id.clone(),
        outcome: outcome_key,
        code,
        prefix,
      });
    }
  }

  regressions.sort_by(|a, b| a.id.cmp(&b.id));
  xpasses.sort();

  let regressions_top: Vec<_> = regressions.into_iter().take(top).collect();
  let mut suggestions = suggest_manifest_entries_for_regressions(&regressions_top, None);
  suggestions.extend(suggest_manifest_entries_for_xpasses(
    &xpasses.into_iter().take(top).collect::<Vec<_>>(),
    None,
  ));

  Ok(TriageReport {
    kind: ReportKind::Conformance,
    top,
    total: input.results.len(),
    mismatches,
    xpass,
    unexpected_mismatches: Some(unexpected_mismatches),
    mismatches_without_code,
    top_outcomes: top_groups(outcome_counts, top),
    top_codes: top_groups(code_counts, top),
    top_prefixes: top_groups(prefix_counts, top),
    regressions: regressions_top,
    suggestions: sort_suggestions(suggestions),
    baseline: None,
  })
}

fn analyze_difftsc(input: DifftscReportInput, top: usize) -> Result<TriageReport> {
  let mut outcome_counts: BTreeMap<String, usize> = BTreeMap::new();
  let mut code_counts: BTreeMap<String, usize> = BTreeMap::new();
  let mut prefix_counts: BTreeMap<String, usize> = BTreeMap::new();

  let mut mismatches = 0usize;
  let mut xpass = 0usize;
  let mut mismatches_without_code = 0usize;

  let mut regressions = Vec::new();
  let mut xpasses = Vec::new();

  for case in &input.results {
    if case.status == DifftscCaseStatus::Matched {
      if case
        .expectation
        .as_ref()
        .is_some_and(|e| matches!(e.expectation, ExpectationKind::Xfail | ExpectationKind::Flaky))
      {
        xpass += 1;
        xpasses.push(case.name.clone());
      }
    }

    if !case.status.is_mismatch() {
      continue;
    }
    mismatches += 1;

    let prefix = fixture_prefix(&case.name);
    *prefix_counts.entry(prefix.clone()).or_insert(0) += 1;

    let (outcome_keys, primary_code) = difftsc_case_outcomes_and_code(case);
    if outcome_keys.is_empty() {
      *outcome_counts
        .entry(case.status.as_key().to_string())
        .or_insert(0) += 1;
    } else {
      for key in outcome_keys {
        *outcome_counts.entry(key).or_insert(0) += 1;
      }
    }

    if let Some(code) = primary_code.as_ref().cloned() {
      *code_counts.entry(code).or_insert(0) += 1;
    } else {
      mismatches_without_code += 1;
    }

    // Difftsc expectation data is optional; treat any mismatch as a regression.
    let regression_outcome = if case.status == DifftscCaseStatus::Mismatch {
      "mismatch".to_string()
    } else {
      case.status.as_key().to_string()
    };

    regressions.push(Regression {
      id: case.name.clone(),
      outcome: regression_outcome,
      code: primary_code,
      prefix,
    });
  }

  regressions.sort_by(|a, b| a.id.cmp(&b.id));
  xpasses.sort();
  let regressions_top: Vec<_> = regressions.into_iter().take(top).collect();
  let mut suggestions =
    suggest_manifest_entries_for_regressions(&regressions_top, input.suite.as_deref());
  suggestions.extend(suggest_manifest_entries_for_xpasses(
    &xpasses.into_iter().take(top).collect::<Vec<_>>(),
    input.suite.as_deref(),
  ));

  Ok(TriageReport {
    kind: ReportKind::Difftsc,
    top,
    total: input.results.len(),
    mismatches,
    xpass,
    unexpected_mismatches: None,
    mismatches_without_code,
    top_outcomes: top_groups(outcome_counts, top),
    top_codes: top_groups(code_counts, top),
    top_prefixes: top_groups(prefix_counts, top),
    regressions: regressions_top,
    suggestions: sort_suggestions(suggestions),
    baseline: None,
  })
}

fn difftsc_case_outcomes_and_code(case: &DifftscCaseInput) -> (Vec<String>, Option<String>) {
  if case.status != DifftscCaseStatus::Mismatch {
    return (Vec::new(), None);
  }

  let mut outcomes = Vec::new();
  let mut primary = None;

  if let Some(diff) = case.diff.as_ref() {
    if !diff.unexpected.is_empty() {
      outcomes.push("rust_extra_diagnostics".to_string());
      primary = primary.or_else(|| diag_code_from_list(&diff.unexpected));
    }
    if !diff.missing.is_empty() {
      outcomes.push("rust_missing_diagnostics".to_string());
      primary = primary.or_else(|| diag_code_from_list(&diff.missing));
    }
    if !diff.code.is_empty() {
      outcomes.push("code_mismatch".to_string());
      if primary.is_none() {
        primary = diag_code_from_pair_list(&diff.code);
      }
    }
    if !diff.span.is_empty() {
      outcomes.push("span_mismatch".to_string());
      if primary.is_none() {
        primary = diag_code_from_pair_list(&diff.span);
      }
    }
  }

  if outcomes.is_empty() {
    if let Some(type_diff) = case.type_diff.as_ref() {
      if !type_diff.is_empty() {
        outcomes.push("type_mismatch".to_string());
      }
    }
  }

  if primary.is_none() {
    primary = case
      .expected
      .as_ref()
      .and_then(|diags| diag_code_from_list(diags))
      .or_else(|| {
        case
          .actual
          .as_ref()
          .and_then(|diags| diag_code_from_list(diags))
      });
  }

  (outcomes, primary)
}

fn suggest_manifest_entries_for_regressions(
  regressions: &[Regression],
  suite: Option<&str>,
) -> Vec<SuggestedManifestEntry> {
  let mut suggestions = Vec::new();
  for reg in regressions {
    let status = match reg.outcome.as_str() {
      "timeout" | "tsc_crashed" | "tsc_failed" | "baseline_missing" => "skip",
      _ => "xfail",
    };

    let reason = match &reg.code {
      Some(code) => Some(format!("triage: {} {code}", reg.outcome)),
      None => Some(format!("triage: {}", reg.outcome)),
    };

    let id = match suite {
      Some(suite) => format!("{suite}/{}", reg.id),
      None => reg.id.clone(),
    };

    suggestions.push(SuggestedManifestEntry {
      id: Some(id),
      glob: None,
      status: status.to_string(),
      reason,
    });
  }

  sort_suggestions(suggestions)
}

fn suggest_manifest_entries_for_xpasses(
  xpasses: &[String],
  suite: Option<&str>,
) -> Vec<SuggestedManifestEntry> {
  let mut suggestions = Vec::new();
  for id in xpasses {
    let id = match suite {
      Some(suite) => format!("{suite}/{id}"),
      None => id.clone(),
    };
    suggestions.push(SuggestedManifestEntry {
      id: Some(id),
      glob: None,
      status: "pass".to_string(),
      reason: Some("triage: xpass".to_string()),
    });
  }
  sort_suggestions(suggestions)
}

fn sort_suggestions(mut suggestions: Vec<SuggestedManifestEntry>) -> Vec<SuggestedManifestEntry> {
  // Deterministic ordering (tie-breaker on id, though ids are already sorted).
  suggestions.sort_by(|a, b| match (&a.status, &b.status) {
    (a_status, b_status) => a_status.cmp(b_status).then_with(|| a.id.cmp(&b.id)),
  });
  suggestions
}

fn top_groups(counts: BTreeMap<String, usize>, top: usize) -> Vec<CountGroup> {
  let mut groups: Vec<(String, usize)> = counts.into_iter().collect();
  groups.sort_by(|(a_key, a_count), (b_key, b_count)| {
    b_count.cmp(a_count).then_with(|| a_key.cmp(b_key))
  });
  groups.truncate(top);
  groups
    .into_iter()
    .map(|(key, count)| CountGroup { key, count })
    .collect()
}

fn outcome_key(outcome: TestOutcome) -> &'static str {
  match outcome {
    TestOutcome::Match => "match",
    TestOutcome::RustExtraDiagnostics => "rust_extra_diagnostics",
    TestOutcome::RustMissingDiagnostics => "rust_missing_diagnostics",
    TestOutcome::SpanMismatch => "span_mismatch",
    TestOutcome::CodeMismatch => "code_mismatch",
    TestOutcome::RustIce => "rust_ice",
    TestOutcome::TscCrashed => "tsc_crashed",
    TestOutcome::Timeout => "timeout",
  }
}

fn fixture_prefix(id: &str) -> String {
  let normalized = id.replace('\\', "/");
  normalized
    .split('/')
    .find(|seg| !seg.is_empty())
    .unwrap_or("<unknown>")
    .to_string()
}

fn primary_code_from_detail_or_diags(
  detail: &Option<MismatchDetail>,
  rust: &EngineDiagnostics,
  tsc: &EngineDiagnostics,
) -> Option<String> {
  if let Some(detail) = detail.as_ref() {
    if let Some(tsc_diag) = detail.tsc.as_ref() {
      if let Some(code) = tsc_diag.code.as_ref() {
        return Some(canonicalize_code(code));
      }
    }
    if let Some(rust_diag) = detail.rust.as_ref() {
      if let Some(code) = rust_diag.code.as_ref() {
        return Some(canonicalize_code(code));
      }
    }
  }

  diag_code_from_list(&tsc.diagnostics).or_else(|| diag_code_from_list(&rust.diagnostics))
}

fn diag_code_from_list(diags: &[NormalizedDiagnostic]) -> Option<String> {
  for diag in diags {
    if let Some(code) = diag.code.as_ref() {
      return Some(canonicalize_code(code));
    }
  }
  None
}

fn diag_code_from_pair_list(pairs: &[DifftscMismatchPair]) -> Option<String> {
  for pair in pairs {
    if let Some(code) = pair.expected.code.as_ref() {
      return Some(canonicalize_code(code));
    }
    if let Some(code) = pair.actual.code.as_ref() {
      return Some(canonicalize_code(code));
    }
  }
  None
}

fn canonicalize_code(code: &DiagnosticCode) -> String {
  match code {
    DiagnosticCode::Tsc(num) => format!("TS{num}"),
    DiagnosticCode::Rust(raw) => numeric_code(raw)
      .map(|n| format!("TS{n}"))
      .unwrap_or_else(|| raw.clone()),
  }
}

fn numeric_code(raw: &str) -> Option<u32> {
  let trimmed = raw
    .trim_start_matches(|c| c == 't' || c == 'T')
    .trim_start_matches('S');
  trimmed.parse().ok()
}
