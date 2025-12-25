#![cfg_attr(not(feature = "with-node"), allow(dead_code, unused_imports))]

use crate::diagnostic_norm::{
  diagnostic_code_display, normalize_path_for_compare, normalize_tsc_diagnostics_with_options,
  sort_diagnostics, NormalizationOptions, NormalizedDiagnostic,
};
use crate::directives::HarnessOptions;
use crate::expectations::{ExpectationKind, Expectations};
use crate::multifile::normalize_name;
use crate::runner::{run_rust, EngineStatus, HarnessFileSet};
use crate::tsc::{
  node_available, TscDiagnostics, TscRequest, TscRunner, TSC_BASELINE_SCHEMA_VERSION,
};
use crate::{FailOn, VirtualFile};
use anyhow::{anyhow, Context, Result};
use clap::Args;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::HashMap;
use std::fmt::Write as FmtWrite;
use std::fs;
use std::path::{Path, PathBuf};
use walkdir::WalkDir;

#[derive(Debug, Clone, Args)]
pub struct DifftscArgs {
  /// Path to the suite containing fixture tests.
  #[arg(long)]
  pub suite: PathBuf,

  /// Whether to regenerate baselines from tsc output.
  #[arg(long)]
  pub update_baselines: bool,

  /// Compare Rust checker diagnostics against tsc for each test.
  #[arg(long, alias = "differential")]
  pub compare_rust: bool,

  /// Use stored baselines instead of running tsc (useful when Node is unavailable).
  #[arg(long)]
  pub use_baselines: bool,

  /// Allow mismatches without failing the command.
  #[arg(long)]
  pub allow_mismatches: bool,

  /// Emit JSON output in addition to the human summary.
  #[arg(long)]
  pub json: bool,

  /// Print the raw tsc response for mismatched cases.
  #[arg(long)]
  pub print_tsc: bool,

  /// Path to the Node.js executable.
  #[arg(long, default_value = "node")]
  pub node: PathBuf,

  /// Allowed byte tolerance when comparing spans.
  #[arg(long, default_value_t = 0)]
  pub span_tolerance: u32,

  /// Path to a manifest describing expected failures.
  #[arg(long)]
  pub manifest: Option<PathBuf>,

  /// When to fail the run on mismatches.
  #[arg(long, value_enum, default_value_t = FailOn::New)]
  pub fail_on: FailOn,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommandStatus {
  Success,
  Skipped,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum CaseStatus {
  Matched,
  Mismatch,
  BaselineUpdated,
  BaselineMissing,
  TscFailed,
  RustFailed,
  Skipped,
}

impl CaseStatus {
  fn is_error(&self) -> bool {
    matches!(
      self,
      CaseStatus::BaselineMissing | CaseStatus::TscFailed | CaseStatus::RustFailed
    )
  }

  fn as_str(&self) -> &'static str {
    match self {
      CaseStatus::Matched => "matched",
      CaseStatus::Mismatch => "mismatch",
      CaseStatus::BaselineUpdated => "baseline_updated",
      CaseStatus::BaselineMissing => "baseline_missing",
      CaseStatus::TscFailed => "tsc_failed",
      CaseStatus::RustFailed => "rust_failed",
      CaseStatus::Skipped => "skipped",
    }
  }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum MismatchReason {
  Code,
  Severity,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct MismatchPair {
  expected: NormalizedDiagnostic,
  actual: NormalizedDiagnostic,
  #[serde(skip_serializing_if = "Option::is_none")]
  reason: Option<MismatchReason>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct MismatchReport {
  missing: Vec<NormalizedDiagnostic>,
  unexpected: Vec<NormalizedDiagnostic>,
  code: Vec<MismatchPair>,
  span: Vec<MismatchPair>,
}

impl MismatchReport {
  fn is_empty(&self) -> bool {
    self.missing.is_empty()
      && self.unexpected.is_empty()
      && self.code.is_empty()
      && self.span.is_empty()
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CaseReport {
  name: String,
  status: CaseStatus,
  #[serde(skip_serializing_if = "Option::is_none")]
  expected: Option<Vec<NormalizedDiagnostic>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  actual: Option<Vec<NormalizedDiagnostic>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  diff: Option<MismatchReport>,
  #[serde(skip_serializing_if = "Option::is_none")]
  report: Option<String>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  notes: Vec<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct Summary {
  total: usize,
  matched: usize,
  mismatched: usize,
  updated: usize,
  skipped: usize,
  errors: usize,
  expected_mismatches: usize,
  unexpected_mismatches: usize,
  flaky_mismatches: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct JsonReport {
  summary: Summary,
  results: Vec<CaseReport>,
}

#[derive(Debug, Clone)]
struct TestCase {
  name: String,
  files: Vec<VirtualFile>,
}

pub fn run(args: DifftscArgs) -> Result<CommandStatus> {
  #[cfg(not(feature = "with-node"))]
  {
    let _ = args;
    eprintln!("difftsc skipped: built without `with-node` feature");
    return Ok(CommandStatus::Skipped);
  }

  #[cfg(feature = "with-node")]
  {
    run_with_node(args)
  }
}

#[cfg(feature = "with-node")]
fn run_with_node(args: DifftscArgs) -> Result<CommandStatus> {
  let suite_path = resolve_suite_path(&args.suite)?;
  if !suite_path.exists() {
    return Err(anyhow!(
      "suite path does not exist: {}",
      suite_path.display()
    ));
  }

  let suite_name = suite_path
    .file_name()
    .context("suite path missing final component")?
    .to_string_lossy()
    .to_string();

  let baselines_root = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("baselines")
    .join(&suite_name);

  let expectations = match &args.manifest {
    Some(path) => Expectations::from_path(path).map_err(|err| anyhow!(err.to_string()))?,
    None => Expectations::empty(),
  };

  if args.update_baselines {
    fs::create_dir_all(&baselines_root)
      .with_context(|| format!("create baselines directory at {}", baselines_root.display()))?;
  }

  let tests = collect_tests(&suite_path)?;
  if tests.is_empty() {
    return Err(anyhow!("suite `{}` contains no tests", suite_name));
  }

  let mut runner = if needs_live_tsc(&args) {
    if !node_available(&args.node) {
      eprintln!(
        "difftsc skipped: Node.js not available at {}",
        args.node.display()
      );
      return Ok(CommandStatus::Skipped);
    }
    Some(TscRunner::new(args.node.clone())?)
  } else {
    None
  };

  let mut results = Vec::new();
  let mut expected_mismatches = 0usize;
  let mut unexpected_mismatches = 0usize;
  let mut flaky_mismatches = 0usize;
  let normalization = NormalizationOptions::with_span_tolerance(args.span_tolerance);
  for test in tests {
    let test_id = format!("{suite_name}/{}", test.name);
    let expectation = expectations.lookup(&test_id);
    if expectation.expectation.kind == ExpectationKind::Skip {
      results.push(CaseReport {
        name: test.name.clone(),
        status: CaseStatus::Skipped,
        expected: None,
        actual: None,
        diff: None,
        report: None,
        notes: vec!["skipped by manifest".to_string()],
      });
      continue;
    }

    let report = run_single_test(
      &test,
      &args,
      runner.as_mut(),
      &baselines_root,
      &normalization,
    );
    if matches!(report.status, CaseStatus::Mismatch) {
      if expectation.expectation.kind == ExpectationKind::Flaky {
        flaky_mismatches += 1;
      } else if expectation.covers_mismatch() {
        expected_mismatches += 1;
      } else {
        unexpected_mismatches += 1;
      }
    }
    results.push(report);
  }

  let summary = summarize(&results);
  let mismatch_total = summary.mismatched + summary.errors;
  let summary = Summary {
    expected_mismatches,
    unexpected_mismatches,
    flaky_mismatches,
    ..summary
  };

  if args.update_baselines && !args.json {
    println!("updated baselines under {}", baselines_root.display());
  }

  if args.json {
    let json = serde_json::to_string_pretty(&JsonReport {
      summary: summary.clone(),
      results: results.clone(),
    })
    .context("serialize JSON output")?;
    println!("{json}");
  } else {
    print_human_summary(&suite_name, &summary, &results);
  }

  if !args.allow_mismatches
    && args
      .fail_on
      .should_fail(unexpected_mismatches, mismatch_total)
  {
    return Err(anyhow!(
      "{} difftsc mismatches ({} unexpected, {} expected, {} flaky, {} error(s))",
      mismatch_total,
      unexpected_mismatches,
      expected_mismatches,
      flaky_mismatches,
      summary.errors
    ));
  }

  Ok(CommandStatus::Success)
}

#[cfg(feature = "with-node")]
fn summarize(results: &[CaseReport]) -> Summary {
  let mut summary = Summary::default();
  summary.total = results.len();
  for case in results {
    match case.status {
      CaseStatus::Matched => summary.matched += 1,
      CaseStatus::Mismatch => summary.mismatched += 1,
      CaseStatus::BaselineUpdated => summary.updated += 1,
      CaseStatus::Skipped => summary.skipped += 1,
      CaseStatus::BaselineMissing | CaseStatus::TscFailed | CaseStatus::RustFailed => {
        summary.errors += 1
      }
    }
  }
  summary
}

#[cfg(feature = "with-node")]
fn print_human_summary(suite: &str, summary: &Summary, results: &[CaseReport]) {
  println!(
    "difftsc: suite `{suite}` — total={}, matched={}, mismatched={}, updated={}, errors={}, skipped={}",
    summary.total, summary.matched, summary.mismatched, summary.updated, summary.errors, summary.skipped
  );

  if summary.mismatched == 0 && summary.errors == 0 {
    return;
  }

  for case in results.iter().filter(|c| c.status.is_error()) {
    let note = if case.notes.is_empty() {
      String::new()
    } else {
      format!(" ({})", case.notes.join("; "))
    };
    eprintln!("  {}: {}{}", case.name, case.status.as_str(), note);
  }

  for case in results
    .iter()
    .filter(|c| matches!(c.status, CaseStatus::Mismatch))
  {
    let detail = case
      .diff
      .as_ref()
      .map(|d| {
        format!(
          "missing={}, unexpected={}, code_mismatch={}, span_mismatch={}",
          d.missing.len(),
          d.unexpected.len(),
          d.code.len(),
          d.span.len()
        )
      })
      .unwrap_or_else(|| "differences detected".to_string());
    eprintln!("  {}: {}", case.name, detail);
    if let Some(report) = &case.report {
      eprintln!("{report}");
    }
  }
}

#[cfg(feature = "with-node")]
fn run_single_test(
  test: &TestCase,
  args: &DifftscArgs,
  runner: Option<&mut TscRunner>,
  baselines_root: &Path,
  normalization: &NormalizationOptions,
) -> CaseReport {
  let baseline_path = baselines_root.join(format!("{}.json", test.name));
  let notes = Vec::new();

  let live_tsc = if needs_live_tsc(args) {
    let Some(runner) = runner else {
      return CaseReport {
        name: test.name.clone(),
        status: CaseStatus::TscFailed,
        expected: None,
        actual: None,
        diff: None,
        report: None,
        notes: vec!["tsc runner unavailable".to_string()],
      };
    };

    match run_tsc_on_test(test, runner) {
      Ok(diags) => Some(diags),
      Err(err) => {
        return CaseReport {
          name: test.name.clone(),
          status: CaseStatus::TscFailed,
          expected: None,
          actual: None,
          diff: None,
          report: None,
          notes: vec![err.to_string()],
        };
      }
    }
  } else {
    None
  };

  if args.update_baselines {
    if let Some(tsc) = &live_tsc {
      if let Err(err) = write_baseline(&baseline_path, tsc) {
        return CaseReport {
          name: test.name.clone(),
          status: CaseStatus::TscFailed,
          expected: None,
          actual: None,
          diff: None,
          report: None,
          notes: vec![err.to_string()],
        };
      }
    }
  }

  if !args.compare_rust {
    if args.update_baselines {
      return CaseReport {
        name: test.name.clone(),
        status: CaseStatus::BaselineUpdated,
        expected: None,
        actual: None,
        diff: None,
        report: None,
        notes,
      };
    }

    let baseline = match read_baseline(&baseline_path) {
      Ok(data) => data,
      Err(err) => {
        return CaseReport {
          name: test.name.clone(),
          status: CaseStatus::BaselineMissing,
          expected: None,
          actual: None,
          diff: None,
          report: None,
          notes: vec![err.to_string()],
        };
      }
    };
    let expected = normalize_tsc_diagnostics_with_options(&baseline.diagnostics, normalization);
    let actual = normalize_tsc_diagnostics_with_options(
      &live_tsc.as_ref().expect("live tsc required").diagnostics,
      normalization,
    );
    let diff = diff_diagnostics(&expected, &actual, normalization);
    let status = if diff.is_some() {
      CaseStatus::Mismatch
    } else {
      CaseStatus::Matched
    };
    let report = diff
      .as_ref()
      .map(|d| render_mismatch_report(test, d, normalization));
    if args.print_tsc && diff.is_some() {
      print_tsc_response(test, &baseline_path, &live_tsc);
    }
    return CaseReport {
      name: test.name.clone(),
      status,
      expected: Some(expected),
      actual: Some(actual),
      diff,
      report,
      notes,
    };
  }

  let tsc_diags = if let Some(live) = live_tsc {
    live
  } else {
    match read_baseline(&baseline_path) {
      Ok(data) => data,
      Err(err) => {
        return CaseReport {
          name: test.name.clone(),
          status: CaseStatus::BaselineMissing,
          expected: None,
          actual: None,
          diff: None,
          report: None,
          notes: vec![err.to_string()],
        };
      }
    }
  };

  let file_set = HarnessFileSet::new(&test.files);
  let rust = run_rust(&file_set, &HarnessOptions::default());
  let expected = normalize_tsc_diagnostics_with_options(&tsc_diags.diagnostics, normalization);
  if rust.status != EngineStatus::Ok {
    return CaseReport {
      name: test.name.clone(),
      status: CaseStatus::RustFailed,
      expected: Some(expected),
      actual: None,
      diff: None,
      report: None,
      notes: rust.error.into_iter().collect(),
    };
  }

  let actual: Vec<NormalizedDiagnostic> = rust.diagnostics.clone();

  let diff = diff_diagnostics(&expected, &actual, normalization);
  let status = if diff.is_some() {
    CaseStatus::Mismatch
  } else {
    CaseStatus::Matched
  };
  let report = diff
    .as_ref()
    .map(|d| render_mismatch_report(test, d, normalization));
  if args.print_tsc && diff.is_some() {
    print_tsc_response(test, &baseline_path, &Some(tsc_diags.clone()));
  }

  CaseReport {
    name: test.name.clone(),
    status,
    expected: Some(expected),
    actual: Some(actual),
    diff,
    report,
    notes,
  }
}

fn diff_diagnostics(
  expected: &[NormalizedDiagnostic],
  actual: &[NormalizedDiagnostic],
  normalization: &NormalizationOptions,
) -> Option<MismatchReport> {
  let mut expected_sorted = expected.to_vec();
  let mut actual_sorted = actual.to_vec();
  sort_diagnostics(&mut expected_sorted);
  sort_diagnostics(&mut actual_sorted);

  let mut used = vec![false; actual_sorted.len()];
  let mut diff = MismatchReport::default();

  for exp in expected_sorted {
    if let Some(idx) = find_match(&actual_sorted, &used, |act| exp.matches(act, normalization)) {
      used[idx] = true;
      continue;
    }

    if let Some((idx, reason)) =
      find_code_or_severity_match(&actual_sorted, &used, &exp, normalization)
    {
      used[idx] = true;
      diff.code.push(MismatchPair {
        expected: exp.clone(),
        actual: actual_sorted[idx].clone(),
        reason: Some(reason),
      });
      continue;
    }

    if let Some(idx) = find_span_mismatch(&actual_sorted, &used, &exp) {
      used[idx] = true;
      diff.span.push(MismatchPair {
        expected: exp.clone(),
        actual: actual_sorted[idx].clone(),
        reason: None,
      });
      continue;
    }

    diff.missing.push(exp);
  }

  for (idx, act) in actual_sorted.into_iter().enumerate() {
    if !used[idx] {
      diff.unexpected.push(act);
    }
  }

  if diff.is_empty() {
    None
  } else {
    Some(diff)
  }
}

fn find_match<F>(actual: &[NormalizedDiagnostic], used: &[bool], mut predicate: F) -> Option<usize>
where
  F: FnMut(&NormalizedDiagnostic) -> bool,
{
  actual
    .iter()
    .enumerate()
    .find(|(idx, diag)| !used[*idx] && predicate(diag))
    .map(|(idx, _)| idx)
}

fn find_code_or_severity_match(
  actual: &[NormalizedDiagnostic],
  used: &[bool],
  expected: &NormalizedDiagnostic,
  normalization: &NormalizationOptions,
) -> Option<(usize, MismatchReason)> {
  let mut best: Option<(usize, u32, MismatchReason)> = None;
  for (idx, act) in actual.iter().enumerate() {
    if used[idx] || act.file != expected.file {
      continue;
    }
    if !expected.spans_match(act, normalization) {
      continue;
    }
    if expected.codes_match(act) && expected.severity_matches(act) {
      continue;
    }
    let reason = if !expected.codes_match(act) {
      MismatchReason::Code
    } else {
      MismatchReason::Severity
    };
    let distance = span_distance(expected, act);
    if best
      .as_ref()
      .map(|(_, best, _)| distance < *best)
      .unwrap_or(true)
    {
      best = Some((idx, distance, reason));
    }
  }

  best.map(|(idx, _, reason)| (idx, reason))
}

fn find_span_mismatch(
  actual: &[NormalizedDiagnostic],
  used: &[bool],
  expected: &NormalizedDiagnostic,
) -> Option<usize> {
  let mut best: Option<(usize, u32)> = None;
  for (idx, act) in actual.iter().enumerate() {
    if used[idx] || act.file != expected.file || !expected.codes_match(act) {
      continue;
    }
    let distance = span_distance(expected, act);
    if best
      .as_ref()
      .map(|(_, best)| distance < *best)
      .unwrap_or(true)
    {
      best = Some((idx, distance));
    }
  }

  best.map(|(idx, _)| idx)
}

fn span_distance(a: &NormalizedDiagnostic, b: &NormalizedDiagnostic) -> u32 {
  a.start.abs_diff(b.start) + a.end.abs_diff(b.end)
}

fn render_mismatch_report(
  test: &TestCase,
  diff: &MismatchReport,
  normalization: &NormalizationOptions,
) -> String {
  let files = build_file_map(&test.files, normalization);
  let mut report = String::new();
  if !diff.missing.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut missing = diff.missing.clone();
    sort_diagnostics(&mut missing);
    writeln!(&mut report, "missing diagnostics (tsc only):").ok();
    for diag in missing {
      render_single_diag(&mut report, &diag, &files);
    }
  }

  if !diff.unexpected.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut unexpected = diff.unexpected.clone();
    sort_diagnostics(&mut unexpected);
    writeln!(&mut report, "extra diagnostics (rust only):").ok();
    for diag in unexpected {
      render_single_diag(&mut report, &diag, &files);
    }
  }

  if !diff.code.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut pairs = diff.code.clone();
    sort_pairs(&mut pairs);
    writeln!(&mut report, "code/severity mismatches:").ok();
    for pair in pairs {
      render_pair(&mut report, &pair, &files);
    }
  }

  if !diff.span.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut pairs = diff.span.clone();
    sort_pairs(&mut pairs);
    writeln!(&mut report, "span mismatches:").ok();
    for pair in pairs {
      render_pair(&mut report, &pair, &files);
    }
  }

  report.trim_end().to_string()
}

fn sort_pairs(pairs: &mut Vec<MismatchPair>) {
  pairs.sort_by(|a, b| {
    (
      a.expected.file.as_deref().unwrap_or(""),
      a.expected.start,
      a.expected.end,
      code_key(&a.expected),
    )
      .cmp(&(
        b.expected.file.as_deref().unwrap_or(""),
        b.expected.start,
        b.expected.end,
        code_key(&b.expected),
      ))
  });
}

fn code_key(diag: &NormalizedDiagnostic) -> String {
  diag
    .code
    .as_ref()
    .map(diagnostic_code_display)
    .unwrap_or_default()
}

fn build_file_map(
  files: &[VirtualFile],
  normalization: &NormalizationOptions,
) -> HashMap<String, String> {
  let mut map = HashMap::new();
  for file in files {
    let normalized = normalize_path_for_compare(&file.name, normalization);
    map.insert(normalized, file.content.clone());
  }
  map
}

fn render_pair(report: &mut String, pair: &MismatchPair, files: &HashMap<String, String>) {
  writeln!(
    report,
    "- expected: {}",
    format_location(&pair.expected, files)
  )
  .ok();
  if let Some(reason) = &pair.reason {
    writeln!(
      report,
      "  actual (mismatched {:?}): {}",
      reason,
      format_location(&pair.actual, files)
    )
    .ok();
  } else {
    writeln!(
      report,
      "  actual (different span): {}",
      format_location(&pair.actual, files)
    )
    .ok();
  }

  if let Some(context) = render_context(&pair.expected, files) {
    writeln!(report, "  context:").ok();
    for line in context.lines() {
      writeln!(report, "    {line}").ok();
    }
  }
  if let Some(context) = render_context(&pair.actual, files) {
    writeln!(report, "  actual context:").ok();
    for line in context.lines() {
      writeln!(report, "    {line}").ok();
    }
  }
}

fn render_single_diag(
  report: &mut String,
  diag: &NormalizedDiagnostic,
  files: &HashMap<String, String>,
) {
  writeln!(report, "- {}", format_location(diag, files)).ok();
  if let Some(context) = render_context(diag, files) {
    writeln!(report, "  context:").ok();
    for line in context.lines() {
      writeln!(report, "    {line}").ok();
    }
  }
}

fn format_location(diag: &NormalizedDiagnostic, files: &HashMap<String, String>) -> String {
  let code = diag
    .code
    .as_ref()
    .map(diagnostic_code_display)
    .unwrap_or_else(|| "unknown".to_string());
  let severity = diag.severity.as_deref().unwrap_or("unknown");
  if let Some((file, (start_line, start_col), (end_line, end_col))) = line_info(diag, files) {
    format!(
      "{}:{}:{}-{}:{} [{} {}]",
      file, start_line, start_col, end_line, end_col, severity, code
    )
  } else {
    let file = diag.file.as_deref().unwrap_or("<unknown>");
    format!(
      "{}:{}-{} [{} {}]",
      file, diag.start, diag.end, severity, code
    )
  }
}

fn render_context(diag: &NormalizedDiagnostic, files: &HashMap<String, String>) -> Option<String> {
  let file = diag.file.as_ref()?;
  let content = files.get(file)?;
  let lines = collect_lines(content);
  if lines.is_empty() {
    return None;
  }
  let start = diag.start.min(content.len() as u32) as usize;
  let end = diag.end.min(content.len() as u32) as usize;
  let start_line = line_for_offset(&lines, start);
  let end_line = line_for_offset(&lines, end.saturating_sub(1));
  let context_before = 2usize;
  let context_after = 2usize;
  let render_start = start_line.saturating_sub(context_before);
  let render_end = (end_line + context_after).min(lines.len().saturating_sub(1));
  let mut rendered = String::new();
  for line in &lines[render_start..=render_end] {
    writeln!(rendered, "{:>4} │ {}", line.number, line.text).ok();
    let overlap_start = start.max(line.start);
    let overlap_end = end.max(start).min(line.end);
    if overlap_start <= overlap_end && line.end > line.start {
      let marker_start = overlap_start.saturating_sub(line.start);
      let marker_len = (overlap_end.saturating_sub(overlap_start)).max(1);
      writeln!(
        rendered,
        "     │ {}{}",
        " ".repeat(marker_start),
        "^".repeat(marker_len)
      )
      .ok();
    }
  }

  Some(rendered.trim_end().to_string())
}

fn line_info(
  diag: &NormalizedDiagnostic,
  files: &HashMap<String, String>,
) -> Option<(String, (usize, usize), (usize, usize))> {
  let file = diag.file.as_ref()?;
  let content = files.get(file)?;
  let (start_line, start_col) = offset_to_line_col(content, diag.start as usize);
  let (end_line, end_col) = offset_to_line_col(content, diag.end as usize);
  Some((file.clone(), (start_line, start_col), (end_line, end_col)))
}

#[derive(Debug)]
struct LineInfo<'a> {
  number: usize,
  start: usize,
  end: usize,
  text: &'a str,
}

fn collect_lines(content: &str) -> Vec<LineInfo<'_>> {
  let mut lines = Vec::new();
  let bytes = content.as_bytes();
  let mut start = 0;
  let mut number = 1;
  for (idx, byte) in bytes.iter().enumerate() {
    if *byte == b'\n' {
      let end = if idx > start && bytes[idx - 1] == b'\r' {
        idx - 1
      } else {
        idx
      };
      let text = &content[start..end];
      lines.push(LineInfo {
        number,
        start,
        end,
        text,
      });
      number += 1;
      start = idx + 1;
    }
  }

  if start <= content.len() {
    let text = &content[start..];
    lines.push(LineInfo {
      number,
      start,
      end: content.len(),
      text,
    });
  }

  lines
}

fn line_for_offset(lines: &[LineInfo<'_>], offset: usize) -> usize {
  for (idx, line) in lines.iter().enumerate() {
    if offset <= line.end {
      return idx;
    }
  }
  lines.len().saturating_sub(1)
}

fn offset_to_line_col(content: &str, offset: usize) -> (usize, usize) {
  let mut line = 1usize;
  let mut col = 1usize;
  let mut idx = 0;
  let bytes = content.as_bytes();
  let target = offset.min(bytes.len());
  while idx < target {
    match bytes[idx] {
      b'\n' => {
        line += 1;
        col = 1;
      }
      b'\r' => {
        if idx + 1 < target && bytes[idx + 1] == b'\n' {
          line += 1;
          col = 1;
          idx += 1;
        }
      }
      _ => col += 1,
    }
    idx += 1;
  }
  (line, col)
}

fn print_tsc_response(test: &TestCase, baseline_path: &Path, response: &Option<TscDiagnostics>) {
  if let Some(tsc) = response {
    if let Ok(json) = serde_json::to_string_pretty(tsc) {
      eprintln!(
        "tsc response for {} ({}):\n{}",
        test.name,
        baseline_path.display(),
        json
      );
    }
  }
}

#[cfg(feature = "with-node")]
fn needs_live_tsc(args: &DifftscArgs) -> bool {
  // Updating baselines or baseline-only mode always require a live tsc run.
  args.update_baselines || !args.compare_rust || !args.use_baselines
}

#[cfg(feature = "with-node")]
fn resolve_suite_path(suite: &Path) -> Result<PathBuf> {
  let suite_path = if suite.is_absolute() {
    suite.to_path_buf()
  } else {
    std::env::current_dir()?.join(suite)
  };

  if suite_path.exists() || suite.is_absolute() {
    return Ok(suite_path);
  }

  let manifest_candidate = Path::new(env!("CARGO_MANIFEST_DIR")).join(suite);
  if manifest_candidate.exists() {
    Ok(manifest_candidate)
  } else {
    Ok(suite_path)
  }
}

#[cfg(feature = "with-node")]
fn build_request(test: &TestCase) -> TscRequest {
  let mut files = HashMap::new();
  let mut root_names = Vec::new();

  for file in &test.files {
    let normalized = normalize_name(&file.name);
    root_names.push(normalized.clone());
    files.insert(normalized, file.content.clone());
  }

  root_names.sort();
  root_names.dedup();

  let mut options = Map::new();
  options.insert("noEmit".into(), Value::Bool(true));
  options.insert("skipLibCheck".into(), Value::Bool(true));
  options.insert("pretty".into(), Value::Bool(false));

  TscRequest {
    root_names,
    files,
    options,
  }
}

#[cfg(feature = "with-node")]
fn run_tsc_on_test(test: &TestCase, runner: &mut TscRunner) -> Result<TscDiagnostics> {
  let request = build_request(test);
  runner
    .check(request)
    .with_context(|| format!("run tsc for test {}", test.name))
}

fn collect_tests(suite_path: &Path) -> Result<Vec<TestCase>> {
  let mut entries: Vec<_> = fs::read_dir(suite_path)?.collect::<Result<_, _>>()?;
  entries.sort_by_key(|entry| entry.file_name());

  let mut tests = Vec::new();

  for entry in entries {
    let path = entry.path();
    if path.is_dir() {
      let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .context("test directory missing name")?
        .to_string();
      let files = collect_files_recursively(&path)?;
      tests.push(TestCase { name, files });
    } else if is_source_file(&path) {
      let name = test_name_from_path(&path)?;
      let content =
        fs::read_to_string(&path).with_context(|| format!("read test file {}", path.display()))?;
      tests.push(TestCase {
        name,
        files: vec![VirtualFile {
          name: path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .context("test file missing name")?,
          content,
        }],
      });
    }
  }

  Ok(tests)
}

fn collect_files_recursively(dir: &Path) -> Result<Vec<VirtualFile>> {
  let mut files = Vec::new();
  for entry in WalkDir::new(dir)
    .into_iter()
    .filter_map(|res| res.ok())
    .filter(|entry| entry.file_type().is_file())
  {
    let path = entry.path();
    if !is_source_file(path) {
      continue;
    }
    let relative_path = path
      .strip_prefix(dir)
      .context("compute relative path")?
      .to_string_lossy()
      .to_string();
    let content =
      fs::read_to_string(path).with_context(|| format!("read test file {}", path.display()))?;
    files.push(VirtualFile {
      name: relative_path,
      content,
    });
  }

  files.sort_by(|a, b| a.name.cmp(&b.name));
  Ok(files)
}

fn is_source_file(path: &Path) -> bool {
  let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
  if file_name.ends_with(".d.ts") {
    return true;
  }

  matches!(
    path.extension().and_then(|ext| ext.to_str()),
    Some("ts") | Some("tsx") | Some("js") | Some("jsx") | Some("mts") | Some("cts")
  )
}

fn test_name_from_path(path: &Path) -> Result<String> {
  let file_name = path
    .file_name()
    .and_then(|n| n.to_str())
    .context("test file missing name")?;

  if let Some(stripped) = file_name.strip_suffix(".d.ts") {
    return Ok(stripped.to_string());
  }

  path
    .file_stem()
    .and_then(|stem| stem.to_str())
    .map(|s| s.to_string())
    .context("test file missing stem")
}

fn write_baseline(path: &Path, diagnostics: &TscDiagnostics) -> Result<()> {
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent)?;
  }

  let mut diagnostics = diagnostics.clone();
  diagnostics.schema_version = Some(TSC_BASELINE_SCHEMA_VERSION);
  let json = serde_json::to_string_pretty(&diagnostics)?;
  fs::write(path, format!("{json}\n"))
    .with_context(|| format!("write baseline at {}", path.display()))?;

  Ok(())
}

fn read_baseline(path: &Path) -> Result<TscDiagnostics> {
  let data =
    fs::read_to_string(path).with_context(|| format!("read baseline {}", path.display()))?;
  let parsed: TscDiagnostics = serde_json::from_str(&data).context("parse baseline JSON")?;
  let version = parsed.schema_version.unwrap_or(0);
  if version != TSC_BASELINE_SCHEMA_VERSION {
    return Err(anyhow!(
      "baseline schema mismatch (found {}, expected {}); regenerate baselines",
      version,
      TSC_BASELINE_SCHEMA_VERSION
    ));
  }
  Ok(parsed)
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::diagnostic_norm::{DiagnosticCode, DiagnosticEngine, NormalizedDiagnostic};
  use crate::tsc::TscDiagnostic;

  #[test]
  fn determines_test_name_for_d_ts() {
    let path = Path::new("example.d.ts");
    assert_eq!(test_name_from_path(path).unwrap(), "example");
  }

  #[test]
  fn collects_single_and_multi_file_tests() {
    let dir = tempfile::tempdir().unwrap();
    let single = dir.path().join("one.ts");
    fs::write(&single, "const x: number = 'x';").unwrap();

    let multi_dir = dir.path().join("multi");
    fs::create_dir_all(multi_dir.join("nested")).unwrap();
    fs::write(multi_dir.join("a.ts"), "export const a = 1;").unwrap();
    fs::write(multi_dir.join("nested").join("b.ts"), "export const b = a;").unwrap();

    let tests = collect_tests(dir.path()).unwrap();
    assert_eq!(tests.len(), 2);
    assert_eq!(tests[0].name, "multi");
    assert_eq!(tests[0].files.len(), 2);
    assert_eq!(tests[1].name, "one");
  }

  #[test]
  fn compares_diagnostics_with_tolerance() {
    let expected_raw = vec![TscDiagnostic {
      code: 1,
      file: Some("a.ts".to_string()),
      start: 0,
      end: 4,
      category: None,
      message: None,
    }];
    let actual_raw = vec![TscDiagnostic {
      code: 1,
      file: Some("a.ts".to_string()),
      start: 1,
      end: 5,
      category: None,
      message: None,
    }];
    let tolerant = NormalizationOptions::with_span_tolerance(1);
    let strict = NormalizationOptions::with_span_tolerance(0);
    let expected = normalize_tsc_diagnostics_with_options(&expected_raw, &tolerant);
    let actual = normalize_tsc_diagnostics_with_options(&actual_raw, &tolerant);
    assert!(diff_diagnostics(&expected, &actual, &strict).is_some());
    assert!(diff_diagnostics(&expected, &actual, &tolerant).is_none());
  }

  #[test]
  fn renders_mismatch_report_snapshot() {
    let test = TestCase {
      name: "case".to_string(),
      files: vec![VirtualFile {
        name: "a.ts".to_string(),
        content: "abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz"
          .to_string(),
      }],
    };
    let opts = NormalizationOptions::default();
    let expected = vec![
      NormalizedDiagnostic {
        engine: DiagnosticEngine::Tsc,
        code: Some(DiagnosticCode::Tsc(1)),
        file: Some("/a.ts".to_string()),
        start: 0,
        end: 5,
        severity: Some("error".to_string()),
        message: None,
      },
      NormalizedDiagnostic {
        engine: DiagnosticEngine::Tsc,
        code: Some(DiagnosticCode::Tsc(2)),
        file: Some("/a.ts".to_string()),
        start: 20,
        end: 26,
        severity: Some("warning".to_string()),
        message: None,
      },
      NormalizedDiagnostic {
        engine: DiagnosticEngine::Tsc,
        code: Some(DiagnosticCode::Tsc(5)),
        file: Some("/a.ts".to_string()),
        start: 70,
        end: 71,
        severity: Some("error".to_string()),
        message: None,
      },
    ];
    let actual = vec![
      NormalizedDiagnostic {
        engine: DiagnosticEngine::Rust,
        code: Some(DiagnosticCode::Rust("3".to_string())),
        file: Some("/a.ts".to_string()),
        start: 0,
        end: 5,
        severity: Some("error".to_string()),
        message: None,
      },
      NormalizedDiagnostic {
        engine: DiagnosticEngine::Rust,
        code: Some(DiagnosticCode::Rust("2".to_string())),
        file: Some("/a.ts".to_string()),
        start: 21,
        end: 27,
        severity: Some("warning".to_string()),
        message: None,
      },
      NormalizedDiagnostic {
        engine: DiagnosticEngine::Rust,
        code: Some(DiagnosticCode::Rust("4".to_string())),
        file: Some("/a.ts".to_string()),
        start: 55,
        end: 56,
        severity: Some("error".to_string()),
        message: None,
      },
    ];
    let diff = diff_diagnostics(&expected, &actual, &opts).expect("diff");
    let report = render_mismatch_report(&test, &diff, &opts);
    let expected_report = "\
missing diagnostics (tsc only):
- /a.ts:1:71-1:72 [error 5]
  context:
       1 │ abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz
         │                                                                       ^

extra diagnostics (rust only):
- /a.ts:1:56-1:57 [error 4]
  context:
       1 │ abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz
         │                                                        ^

code/severity mismatches:
- expected: /a.ts:1:1-1:6 [error 1]
  actual (mismatched Code): /a.ts:1:1-1:6 [error 3]
  context:
       1 │ abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz
         │ ^^^^^
  actual context:
       1 │ abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz
         │ ^^^^^

span mismatches:
- expected: /a.ts:1:21-1:27 [warning 2]
  actual (different span): /a.ts:1:22-1:28 [warning 2]
  context:
       1 │ abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz
         │                     ^^^^^^
  actual context:
       1 │ abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz
         │                      ^^^^^^";
    assert_eq!(report, expected_report);
  }
}
