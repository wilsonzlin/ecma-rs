use crate::diagnostic_norm::{
  diagnostic_code_display, normalize_path_for_compare, normalize_tsc_diagnostics_with_options,
  normalize_type_string, sort_diagnostics, NormalizationOptions, NormalizedDiagnostic,
};
use crate::directives::{parse_directive, HarnessOptions};
use crate::expectations::{ExpectationKind, Expectations};
use crate::multifile::normalize_name;
use crate::runner::{
  build_tsc_request, is_source_root, run_rust, EngineStatus, HarnessFileSet, HarnessHost,
  TscRunnerPool,
};
use crate::tsc::{
  node_available, ExportTypeFact, TscDiagnostics, TypeAtFact, TypeFacts, TypeQuery,
  TSC_BASELINE_SCHEMA_VERSION,
};
use crate::{read_utf8_file, FailOn, VirtualFile};
use anyhow::{anyhow, Context, Result};
use clap::Args;
use num_cpus;
use rayon::{prelude::*, ThreadPoolBuilder};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::{HashMap, HashSet};
use std::fmt::Write as FmtWrite;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};
use typecheck_ts::Program;
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

  /// Number of worker threads to use.
  #[arg(long, default_value_t = num_cpus::get())]
  pub jobs: usize,
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

#[derive(Debug, Clone, Serialize, Deserialize, Default, PartialEq, Eq)]
struct NormalizedTypeFacts {
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  exports: Vec<NormalizedExportType>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  markers: Vec<NormalizedMarkerType>,
}

impl NormalizedTypeFacts {
  fn is_empty(&self) -> bool {
    self.exports.is_empty() && self.markers.is_empty()
  }

  fn sort(&mut self) {
    self
      .exports
      .sort_by(|a, b| (&a.file, &a.name).cmp(&(&b.file, &b.name)));
    self
      .markers
      .sort_by(|a, b| (&a.file, a.offset, &a.type_str).cmp(&(&b.file, b.offset, &b.type_str)));
  }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct NormalizedExportType {
  file: String,
  name: String,
  #[serde(rename = "type")]
  type_str: String,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
struct NormalizedMarkerType {
  file: String,
  offset: u32,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  line: Option<u32>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  column: Option<u32>,
  #[serde(rename = "type")]
  type_str: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct TypeMismatchPair<T> {
  expected: T,
  actual: T,
}

#[derive(Debug, Clone, Serialize, Deserialize, Default)]
struct TypeMismatchReport {
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  missing_exports: Vec<NormalizedExportType>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  unexpected_exports: Vec<NormalizedExportType>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  mismatched_exports: Vec<TypeMismatchPair<NormalizedExportType>>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  missing_markers: Vec<NormalizedMarkerType>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  unexpected_markers: Vec<NormalizedMarkerType>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  mismatched_markers: Vec<TypeMismatchPair<NormalizedMarkerType>>,
}

impl TypeMismatchReport {
  fn is_empty(&self) -> bool {
    self.missing_exports.is_empty()
      && self.unexpected_exports.is_empty()
      && self.mismatched_exports.is_empty()
      && self.missing_markers.is_empty()
      && self.unexpected_markers.is_empty()
      && self.mismatched_markers.is_empty()
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CaseReport {
  name: String,
  status: CaseStatus,
  #[serde(skip_serializing_if = "Option::is_none")]
  harness_options: Option<HarnessOptions>,
  #[serde(skip_serializing_if = "Option::is_none")]
  tsc_options: Option<Map<String, Value>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  expected: Option<Vec<NormalizedDiagnostic>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  actual: Option<Vec<NormalizedDiagnostic>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  diff: Option<MismatchReport>,
  #[serde(skip_serializing_if = "Option::is_none")]
  expected_types: Option<NormalizedTypeFacts>,
  #[serde(skip_serializing_if = "Option::is_none")]
  actual_types: Option<NormalizedTypeFacts>,
  #[serde(skip_serializing_if = "Option::is_none")]
  type_diff: Option<TypeMismatchReport>,
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
  if needs_live_tsc(&args) && !cfg!(feature = "with-node") {
    eprintln!("difftsc skipped: built without `with-node` feature");
    return Ok(CommandStatus::Skipped);
  }

  run_impl(args)
}

fn run_impl(args: DifftscArgs) -> Result<CommandStatus> {
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

  let jobs = args.jobs.max(1);
  let pool = ThreadPoolBuilder::new()
    .num_threads(jobs)
    .build()
    .map_err(|err| anyhow!("create thread pool: {err}"))?;

  let needs_live_tsc = needs_live_tsc(&args);
  let tsc_pool = if needs_live_tsc {
    if !node_available(&args.node) {
      eprintln!(
        "difftsc skipped: Node.js not available at {}",
        args.node.display()
      );
      return Ok(CommandStatus::Skipped);
    }
    if !crate::tsc::typescript_available(&args.node) {
      let hint = "TypeScript npm package missing (run `cd typecheck-ts-harness && npm ci`)";
      if args.update_baselines {
        return Err(anyhow!("difftsc requires `tsc`, but {hint}"));
      }
      eprintln!("difftsc skipped: {hint}");
      return Ok(CommandStatus::Skipped);
    }
    Some(TscRunnerPool::new(args.node.clone(), jobs))
  } else {
    None
  };

  let normalization = NormalizationOptions::with_span_tolerance(args.span_tolerance);
  let tsc_pool = tsc_pool.as_ref();
  let mut results_with_ids: Vec<(String, CaseReport)> = pool.install(|| {
    tests
      .par_iter()
      .map(|test| {
        let test_id = format!("{suite_name}/{}", test.name);
        let expectation = expectations.lookup(&test_id);
        if expectation.expectation.kind == ExpectationKind::Skip {
          return (
            test_id,
            CaseReport {
              name: test.name.clone(),
              status: CaseStatus::Skipped,
              harness_options: None,
              tsc_options: None,
              expected: None,
              actual: None,
              diff: None,
              expected_types: None,
              actual_types: None,
              type_diff: None,
              report: None,
              notes: vec!["skipped by manifest".to_string()],
            },
          );
        }

        let report = run_single_test(test, &args, tsc_pool, &baselines_root, &normalization);

        (test_id, report)
      })
      .collect()
  });

  results_with_ids.sort_by(|a, b| a.0.cmp(&b.0));

  let mut expected_mismatches = 0usize;
  let mut unexpected_mismatches = 0usize;
  let mut flaky_mismatches = 0usize;
  let mut results = Vec::with_capacity(results_with_ids.len());
  for (test_id, report) in results_with_ids {
    if matches!(report.status, CaseStatus::Mismatch) {
      let expectation = expectations.lookup(&test_id);
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
    let mut sections = Vec::new();
    if let Some(d) = case.diff.as_ref() {
      sections.push(format!(
        "missing={}, unexpected={}, code_mismatch={}, span_mismatch={}",
        d.missing.len(),
        d.unexpected.len(),
        d.code.len(),
        d.span.len()
      ));
    }
    if let Some(t) = case.type_diff.as_ref() {
      let export_total =
        t.missing_exports.len() + t.unexpected_exports.len() + t.mismatched_exports.len();
      let marker_total =
        t.missing_markers.len() + t.unexpected_markers.len() + t.mismatched_markers.len();
      sections.push(format!(
        "type_exports={}, type_markers={}",
        export_total, marker_total
      ));
    }
    let detail = if sections.is_empty() {
      "differences detected".to_string()
    } else {
      sections.join("; ")
    };
    eprintln!("  {}: {}", case.name, detail);
    if let Some(report) = &case.report {
      eprintln!("{report}");
    }
  }
}

fn run_single_test(
  test: &TestCase,
  args: &DifftscArgs,
  tsc_pool: Option<&TscRunnerPool>,
  baselines_root: &Path,
  normalization: &NormalizationOptions,
) -> CaseReport {
  let baseline_path = baselines_root.join(format!("{}.json", test.name));
  let mut notes = Vec::new();
  let harness_options = harness_options_from_files(&test.files);
  let tsc_options = harness_options.to_tsc_options_map();
  let file_set = HarnessFileSet::new(&test.files);

  let live_tsc = if needs_live_tsc(args) {
    let Some(pool) = tsc_pool else {
      return CaseReport {
        name: test.name.clone(),
        status: CaseStatus::TscFailed,
        harness_options: Some(harness_options),
        tsc_options: Some(tsc_options),
        expected: None,
        actual: None,
        diff: None,
        expected_types: None,
        actual_types: None,
        type_diff: None,
        report: None,
        notes: vec!["tsc runner unavailable".to_string()],
      };
    };

    let request = build_tsc_request(&file_set, &tsc_options, false);
    // `difftsc` is primarily a developer tool, but keep a reasonable upper
    // bound so a wedged Node process does not hang the whole run forever.
    let deadline = Instant::now() + Duration::from_secs(60);
    match pool.run_request(request, deadline) {
      Ok(diags) => Some(diags),
      Err(err) => {
        return CaseReport {
          name: test.name.clone(),
          status: CaseStatus::TscFailed,
          harness_options: Some(harness_options),
          tsc_options: Some(tsc_options),
          expected: None,
          actual: None,
          diff: None,
          expected_types: None,
          actual_types: None,
          type_diff: None,
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
          harness_options: Some(harness_options),
          tsc_options: Some(tsc_options),
          expected: None,
          actual: None,
          diff: None,
          expected_types: None,
          actual_types: None,
          type_diff: None,
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
        harness_options: Some(harness_options),
        tsc_options: Some(tsc_options),
        expected: None,
        actual: None,
        diff: None,
        expected_types: None,
        actual_types: None,
        type_diff: None,
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
          harness_options: Some(harness_options),
          tsc_options: Some(tsc_options),
          expected: None,
          actual: None,
          diff: None,
          expected_types: None,
          actual_types: None,
          type_diff: None,
          report: None,
          notes: vec![err.to_string()],
        };
      }
    };
    notes.extend(baseline_option_mismatch_notes(
      &tsc_options,
      &baseline.metadata.options,
    ));
    let mut expected = normalize_tsc_diagnostics_with_options(&baseline.diagnostics, normalization);
    let mut actual = normalize_tsc_diagnostics_with_options(
      &live_tsc.as_ref().expect("live tsc required").diagnostics,
      normalization,
    );
    sort_diagnostics(&mut expected);
    sort_diagnostics(&mut actual);
    let expected_types = normalize_type_facts(&baseline.type_facts, normalization);
    let actual_types = normalize_type_facts(
      &live_tsc.as_ref().expect("live tsc required").type_facts,
      normalization,
    );
    let diff = diff_diagnostics(&expected, &actual, normalization);
    let type_diff = diff_type_facts(&expected_types, &actual_types);
    let status = if diff.is_some() || type_diff.is_some() {
      CaseStatus::Mismatch
    } else {
      CaseStatus::Matched
    };
    let report = render_full_report(test, diff.as_ref(), type_diff.as_ref(), normalization);
    if args.print_tsc && (diff.is_some() || type_diff.is_some()) {
      print_tsc_response(test, &baseline_path, &live_tsc);
    }
    return CaseReport {
      name: test.name.clone(),
      status,
      harness_options: Some(harness_options),
      tsc_options: Some(tsc_options),
      expected: Some(expected),
      actual: Some(actual),
      expected_types: (!expected_types.is_empty()).then_some(expected_types),
      actual_types: (!actual_types.is_empty()).then_some(actual_types),
      diff,
      type_diff,
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
          harness_options: Some(harness_options),
          tsc_options: Some(tsc_options),
          expected: None,
          actual: None,
          diff: None,
          expected_types: None,
          actual_types: None,
          type_diff: None,
          report: None,
          notes: vec![err.to_string()],
        };
      }
    }
  };
  notes.extend(baseline_option_mismatch_notes(
    &tsc_options,
    &tsc_diags.metadata.options,
  ));

  let rust = run_rust(&file_set, &harness_options);
  let mut expected = normalize_tsc_diagnostics_with_options(&tsc_diags.diagnostics, normalization);
  sort_diagnostics(&mut expected);
  let compare_type_facts = tsc_diags.type_facts.is_some();
  let export_queries: &[ExportTypeFact] = tsc_diags
    .type_facts
    .as_ref()
    .map(|facts| facts.exports.as_slice())
    .unwrap_or(&[]);
  let expected_types = normalize_type_facts(&tsc_diags.type_facts, normalization);
  let marker_queries = marker_queries_from_type_facts(&tsc_diags.type_facts);
  let actual_types = if rust.status == EngineStatus::Ok && compare_type_facts {
    collect_rust_type_facts(
      &file_set,
      &harness_options,
      export_queries,
      &marker_queries,
      normalization,
    )
  } else {
    NormalizedTypeFacts::default()
  };
  if rust.status != EngineStatus::Ok {
    return CaseReport {
      name: test.name.clone(),
      status: CaseStatus::RustFailed,
      harness_options: Some(harness_options),
      tsc_options: Some(tsc_options),
      expected: Some(expected),
      actual: None,
      expected_types: (!expected_types.is_empty()).then_some(expected_types),
      actual_types: None,
      diff: None,
      type_diff: None,
      report: None,
      notes: rust.error.into_iter().collect(),
    };
  }

  let mut actual: Vec<NormalizedDiagnostic> = rust.diagnostics.clone();
  sort_diagnostics(&mut actual);

  let diff = diff_diagnostics(&expected, &actual, normalization);
  let type_diff = compare_type_facts
    .then(|| diff_type_facts(&expected_types, &actual_types))
    .flatten();
  let status = if diff.is_some() || type_diff.is_some() {
    CaseStatus::Mismatch
  } else {
    CaseStatus::Matched
  };
  let report = render_full_report(test, diff.as_ref(), type_diff.as_ref(), normalization);
  if args.print_tsc && (diff.is_some() || type_diff.is_some()) {
    print_tsc_response(test, &baseline_path, &Some(tsc_diags.clone()));
  }

  CaseReport {
    name: test.name.clone(),
    status,
    harness_options: Some(harness_options),
    tsc_options: Some(tsc_options),
    expected: Some(expected),
    actual: Some(actual),
    expected_types: (!expected_types.is_empty()).then_some(expected_types),
    actual_types: (!actual_types.is_empty()).then_some(actual_types),
    diff,
    type_diff,
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

fn normalize_type_facts(
  facts: &Option<TypeFacts>,
  normalization: &NormalizationOptions,
) -> NormalizedTypeFacts {
  let Some(facts) = facts else {
    return NormalizedTypeFacts::default();
  };

  let mut normalized = NormalizedTypeFacts {
    exports: facts
      .exports
      .iter()
      .map(|fact| NormalizedExportType {
        file: normalize_path_for_compare(&fact.file, normalization),
        name: fact.name.clone(),
        type_str: normalize_type_string(&fact.type_str),
      })
      .collect(),
    markers: facts
      .markers
      .iter()
      .map(|fact| NormalizedMarkerType {
        file: normalize_path_for_compare(&fact.file, normalization),
        offset: fact.offset,
        line: fact.line,
        column: fact.column,
        type_str: normalize_type_string(&fact.type_str),
      })
      .collect(),
  };
  normalized.sort();
  normalized
}

fn diff_type_facts(
  expected: &NormalizedTypeFacts,
  actual: &NormalizedTypeFacts,
) -> Option<TypeMismatchReport> {
  let mut report = TypeMismatchReport::default();

  let mut actual_exports: HashMap<(String, String), NormalizedExportType> = actual
    .exports
    .iter()
    .map(|exp| ((exp.file.clone(), exp.name.clone()), exp.clone()))
    .collect();
  for expected_export in &expected.exports {
    let key = (expected_export.file.clone(), expected_export.name.clone());
    if let Some(actual_export) = actual_exports.remove(&key) {
      if expected_export.type_str != actual_export.type_str {
        report.mismatched_exports.push(TypeMismatchPair {
          expected: expected_export.clone(),
          actual: actual_export,
        });
      }
    } else {
      report.missing_exports.push(expected_export.clone());
    }
  }
  if !actual_exports.is_empty() {
    report
      .unexpected_exports
      .extend(actual_exports.into_values());
    report
      .unexpected_exports
      .sort_by(|a, b| (&a.file, &a.name).cmp(&(&b.file, &b.name)));
  }

  let mut actual_markers: HashMap<(String, u32), NormalizedMarkerType> = actual
    .markers
    .iter()
    .map(|marker| ((marker.file.clone(), marker.offset), marker.clone()))
    .collect();
  for expected_marker in &expected.markers {
    let key = (expected_marker.file.clone(), expected_marker.offset);
    if let Some(actual_marker) = actual_markers.remove(&key) {
      if expected_marker.type_str != actual_marker.type_str {
        report.mismatched_markers.push(TypeMismatchPair {
          expected: expected_marker.clone(),
          actual: actual_marker,
        });
      }
    } else {
      report.missing_markers.push(expected_marker.clone());
    }
  }
  if !actual_markers.is_empty() {
    report
      .unexpected_markers
      .extend(actual_markers.into_values());
    report
      .unexpected_markers
      .sort_by(|a, b| (&a.file, a.offset).cmp(&(&b.file, b.offset)));
  }

  if report.is_empty() {
    None
  } else {
    Some(report)
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

fn render_type_mismatch_report(
  test: &TestCase,
  diff: &TypeMismatchReport,
  normalization: &NormalizationOptions,
) -> String {
  let files = build_file_map(&test.files, normalization);
  let mut report = String::new();

  if !diff.missing_exports.is_empty() {
    let mut missing = diff.missing_exports.clone();
    missing.sort_by(|a, b| (&a.file, &a.name).cmp(&(&b.file, &b.name)));
    writeln!(&mut report, "missing export types (tsc only):").ok();
    for fact in missing {
      writeln!(&mut report, "- {}", format_export_fact(&fact)).ok();
    }
  }

  if !diff.unexpected_exports.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut unexpected = diff.unexpected_exports.clone();
    unexpected.sort_by(|a, b| (&a.file, &a.name).cmp(&(&b.file, &b.name)));
    writeln!(&mut report, "extra export types (rust only):").ok();
    for fact in unexpected {
      writeln!(&mut report, "- {}", format_export_fact(&fact)).ok();
    }
  }

  if !diff.mismatched_exports.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut pairs = diff.mismatched_exports.clone();
    pairs.sort_by(|a, b| {
      (
        &a.expected.file,
        &a.expected.name,
        &a.expected.type_str,
        &a.actual.type_str,
      )
        .cmp(&(
          &b.expected.file,
          &b.expected.name,
          &b.expected.type_str,
          &b.actual.type_str,
        ))
    });
    writeln!(&mut report, "export type mismatches:").ok();
    for pair in pairs {
      writeln!(
        &mut report,
        "- expected: {}",
        format_export_fact(&pair.expected)
      )
      .ok();
      writeln!(
        &mut report,
        "  actual: {}",
        format_export_fact(&pair.actual)
      )
      .ok();
    }
  }

  if !diff.missing_markers.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut missing = diff.missing_markers.clone();
    missing.sort_by(|a, b| (&a.file, a.offset).cmp(&(&b.file, b.offset)));
    writeln!(&mut report, "missing type queries (tsc only):").ok();
    for fact in missing {
      writeln!(&mut report, "- {}", format_marker_fact(&fact, &files)).ok();
    }
  }

  if !diff.unexpected_markers.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut unexpected = diff.unexpected_markers.clone();
    unexpected.sort_by(|a, b| (&a.file, a.offset).cmp(&(&b.file, b.offset)));
    writeln!(&mut report, "extra type queries (rust only):").ok();
    for fact in unexpected {
      writeln!(&mut report, "- {}", format_marker_fact(&fact, &files)).ok();
    }
  }

  if !diff.mismatched_markers.is_empty() {
    if !report.is_empty() {
      report.push('\n');
    }
    let mut pairs = diff.mismatched_markers.clone();
    pairs.sort_by(|a, b| {
      (
        &a.expected.file,
        a.expected.offset,
        &a.expected.type_str,
        &a.actual.type_str,
      )
        .cmp(&(
          &b.expected.file,
          b.expected.offset,
          &b.expected.type_str,
          &b.actual.type_str,
        ))
    });
    writeln!(&mut report, "type query mismatches:").ok();
    for pair in pairs {
      writeln!(
        &mut report,
        "- expected: {}",
        format_marker_fact(&pair.expected, &files)
      )
      .ok();
      writeln!(
        &mut report,
        "  actual: {}",
        format_marker_fact(&pair.actual, &files)
      )
      .ok();
    }
  }

  report.trim_end().to_string()
}

fn render_full_report(
  test: &TestCase,
  diag: Option<&MismatchReport>,
  types: Option<&TypeMismatchReport>,
  normalization: &NormalizationOptions,
) -> Option<String> {
  let mut sections = Vec::new();
  if let Some(diag) = diag {
    sections.push(render_mismatch_report(test, diag, normalization));
  }
  if let Some(types) = types {
    let rendered = render_type_mismatch_report(test, types, normalization);
    if !rendered.is_empty() {
      sections.push(rendered);
    }
  }

  if sections.is_empty() {
    None
  } else {
    Some(sections.join("\n\n"))
  }
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

fn format_export_fact(fact: &NormalizedExportType) -> String {
  format!("{}::{} ({})", fact.file, fact.name, fact.type_str)
}

fn format_marker_fact(fact: &NormalizedMarkerType, files: &HashMap<String, String>) -> String {
  let file = fact.file.clone();
  if let Some((line, col)) = fact
    .line
    .zip(fact.column)
    .map(|(l, c)| (l as usize + 1, c as usize + 1))
    .or_else(|| marker_line_col(fact, files))
  {
    format!("{file}:{line}:{col} ({})", fact.type_str)
  } else {
    format!("{file}:{} ({})", fact.offset, fact.type_str)
  }
}

fn build_file_map(
  files: &[VirtualFile],
  normalization: &NormalizationOptions,
) -> HashMap<String, String> {
  let mut map = HashMap::new();
  for file in files {
    let normalized = normalize_path_for_compare(&file.name, normalization);
    map.insert(normalized, file.content.to_string());
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

fn marker_line_col(
  marker: &NormalizedMarkerType,
  files: &HashMap<String, String>,
) -> Option<(usize, usize)> {
  let content = files.get(&marker.file)?;
  Some(offset_to_line_col(content, marker.offset as usize))
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

fn marker_queries_from_type_facts(type_facts: &Option<TypeFacts>) -> Vec<TypeQuery> {
  let Some(type_facts) = type_facts.as_ref() else {
    return Vec::new();
  };

  type_facts
    .markers
    .iter()
    .map(|marker| TypeQuery {
      file: marker.file.clone(),
      offset: marker.offset,
      line: marker.line,
      column: marker.column,
    })
    .collect()
}

fn harness_options_from_files(files: &[VirtualFile]) -> HarnessOptions {
  let mut ordered: Vec<(String, &VirtualFile)> = files
    .iter()
    .map(|file| (normalize_name(&file.name), file))
    .collect();
  ordered.sort_by(|(a_norm, a_file), (b_norm, b_file)| {
    a_norm
      .cmp(b_norm)
      .then_with(|| a_file.name.cmp(&b_file.name))
  });

  let mut directives = Vec::new();
  for (_normalized, file) in ordered {
    for (idx, raw_line) in file.content.split_inclusive('\n').enumerate() {
      let line_number = idx + 1;
      let line = raw_line.trim_end_matches(|c| c == '\n' || c == '\r');
      if let Some(directive) = parse_directive(line, line_number) {
        directives.push(directive);
      }
    }
  }

  HarnessOptions::from_directives(&directives)
}

fn baseline_option_mismatch_notes(
  computed: &Map<String, Value>,
  baseline: &Map<String, Value>,
) -> Vec<String> {
  let mut mismatches = Vec::new();
  for (key, expected) in computed {
    let Some(actual) = baseline.get(key) else {
      continue;
    };
    let matches = match (expected, actual) {
      (Value::Bool(a), Value::Bool(b)) => a == b,
      (Value::String(a), Value::String(b)) => a == b,
      (Value::Number(a), Value::Number(b)) => a == b,
      (Value::Array(a), Value::Array(b)) => a == b,
      _ => continue,
    };
    if !matches {
      mismatches.push(format!(
        "baseline option {key} differs (computed={expected}, baseline={actual})"
      ));
    }
  }
  mismatches.sort();
  mismatches
}

fn collect_rust_type_facts(
  file_set: &HarnessFileSet,
  options: &HarnessOptions,
  export_queries: &[ExportTypeFact],
  markers: &[TypeQuery],
  normalization: &NormalizationOptions,
) -> NormalizedTypeFacts {
  let compiler_options = options.to_compiler_options();
  let host = HarnessHost::new(file_set.clone(), compiler_options.clone());
  let roots = file_set.root_keys();
  let program = Program::new(host, roots);
  let _ = program.check();
  let facts = TypeFacts {
    exports: collect_export_type_facts(&program, file_set, export_queries),
    markers: collect_marker_type_facts(&program, file_set, markers),
  };
  normalize_type_facts(&Some(facts), normalization)
}

fn collect_export_type_facts(
  program: &Program,
  file_set: &HarnessFileSet,
  expected: &[ExportTypeFact],
) -> Vec<ExportTypeFact> {
  let mut cache: HashMap<typecheck_ts::FileId, typecheck_ts::ExportMap> = HashMap::new();
  let mut seen: HashSet<(String, String)> = HashSet::new();
  let mut facts = Vec::new();

  for export in expected {
    if !seen.insert((export.file.clone(), export.name.clone())) {
      continue;
    }
    let normalized = normalize_name(&export.file);
    let Some(file_key) = file_set.resolve(&normalized) else {
      continue;
    };
    let Some(file_id) = program.file_id(&file_key) else {
      continue;
    };

    let exports = cache
      .entry(file_id)
      .or_insert_with(|| program.exports_of(file_id));
    let Some(entry) = exports.get(&export.name) else {
      continue;
    };
    let Some(ty) = entry.type_id else {
      continue;
    };
    facts.push(ExportTypeFact {
      file: export.file.clone(),
      name: export.name.clone(),
      type_str: program.display_type(ty).to_string(),
    });
  }

  facts
}

fn collect_marker_type_facts(
  program: &Program,
  file_set: &HarnessFileSet,
  markers: &[TypeQuery],
) -> Vec<TypeAtFact> {
  let mut facts = Vec::new();
  for marker in markers {
    let normalized = normalize_name(&marker.file);
    let Some(file) = file_set.resolve(&normalized) else {
      continue;
    };
    let Some(file_id) = program.file_id(&file) else {
      continue;
    };
    // `Program::type_at` reports the inferred type for the innermost expression/pattern at
    // `offset`. For binding identifiers, that may return the initializer's literal/object type
    // rather than the declared symbol type. TypeScript's `checker.getTypeAtLocation` on an
    // identifier token generally reflects the declared symbol type, so prefer `symbol_at` when
    // the marker does not land within an expression span.
    let ty = if program.expr_at(file_id, marker.offset).is_some() {
      program.type_at(file_id, marker.offset)
    } else {
      program
        .symbol_at(file_id, marker.offset)
        .and_then(|symbol| program.symbol_info(symbol))
        .and_then(|info| info.type_id)
        .or_else(|| program.type_at(file_id, marker.offset))
    };

    if let Some(ty) = ty {
      facts.push(TypeAtFact {
        file: marker.file.clone(),
        offset: marker.offset,
        line: marker.line,
        column: marker.column,
        type_str: program.display_type(ty).to_string(),
      });
    }
  }
  facts
}

fn needs_live_tsc(args: &DifftscArgs) -> bool {
  // Updating baselines or baseline-only mode always require a live tsc run.
  args.update_baselines || !args.compare_rust || !args.use_baselines
}

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

fn collect_tests(suite_path: &Path) -> Result<Vec<TestCase>> {
  let mut entries: Vec<_> = fs::read_dir(suite_path)?.collect::<Result<_, _>>()?;
  entries.sort_by_key(|entry| entry.file_name());

  let mut tests = Vec::new();
  let mut sources: HashMap<String, Vec<PathBuf>> = HashMap::new();

  for entry in entries {
    let path = entry.path();
    if path.is_dir() {
      let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .context("test directory missing name")?
        .to_string();
      sources.entry(name.clone()).or_default().push(path.clone());
      let files = collect_files_recursively(&path)?;
      tests.push(TestCase { name, files });
    } else if is_source_file(&path) {
      let name = test_name_from_path(&path)?;
      sources.entry(name.clone()).or_default().push(path.clone());
      let content =
        read_utf8_file(&path).with_context(|| format!("read test file {}", path.display()))?;
      tests.push(TestCase {
        name,
        files: vec![VirtualFile {
          name: path
            .file_name()
            .map(|n| n.to_string_lossy().to_string())
            .context("test file missing name")?,
          content: content.into(),
        }],
      });
    }
  }

  let mut duplicates: Vec<_> = sources
    .into_iter()
    .filter(|(_, paths)| paths.len() > 1)
    .collect();

  if !duplicates.is_empty() {
    duplicates.sort_by(|(a, _), (b, _)| a.cmp(b));
    let mut message = String::new();
    let _ = writeln!(
      &mut message,
      "duplicate difftsc test name(s) in suite `{}`",
      suite_path.display()
    );
    let _ = writeln!(
      &mut message,
      "baselines are stored as `baselines/<suite>/<name>.json`, so names must be unique."
    );
    for (name, mut paths) in duplicates {
      paths.sort();
      let _ = writeln!(&mut message, "");
      let _ = writeln!(&mut message, "name `{name}` is used by:");
      for path in paths {
        let relative = path.strip_prefix(suite_path).unwrap_or(&path);
        let suffix = if path.is_dir() { "/" } else { "" };
        let _ = writeln!(&mut message, "  - {}{suffix}", relative.display());
      }
    }
    let _ = writeln!(&mut message, "");
    let _ = writeln!(
      &mut message,
      "Rename one test or move it into a subdirectory to disambiguate."
    );
    return Err(anyhow!(message));
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
      read_utf8_file(path).with_context(|| format!("read test file {}", path.display()))?;
    files.push(VirtualFile {
      name: relative_path,
      content: content.into(),
    });
  }

  files.sort_by(|a, b| a.name.cmp(&b.name));
  Ok(files)
}

fn is_source_file(path: &Path) -> bool {
  let Some(file_name) = path.file_name().and_then(|n| n.to_str()) else {
    return false;
  };
  is_source_root(file_name)
}

fn test_name_from_path(path: &Path) -> Result<String> {
  let file_name = path
    .file_name()
    .and_then(|n| n.to_str())
    .context("test file missing name")?;

  if let Some(stripped) = file_name.strip_suffix(".d.ts") {
    return Ok(stripped.to_string());
  }
  if let Some(stripped) = file_name.strip_suffix(".d.mts") {
    return Ok(stripped.to_string());
  }
  if let Some(stripped) = file_name.strip_suffix(".d.cts") {
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
  diagnostics.canonicalize_for_baseline();
  let json = serde_json::to_string_pretty(&diagnostics)?;
  fs::write(path, format!("{json}\n"))
    .with_context(|| format!("write baseline at {}", path.display()))?;

  Ok(())
}

fn read_baseline(path: &Path) -> Result<TscDiagnostics> {
  let data = read_utf8_file(path).with_context(|| format!("read baseline {}", path.display()))?;
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
  use crate::tsc::{TscDiagnostic, TscMetadata};
  use serde_json::Value;
  use typecheck_ts::lib_support::CompilerOptions;

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
  fn errors_on_duplicate_test_names() {
    let dir = tempfile::tempdir().unwrap();
    fs::write(dir.path().join("a.ts"), "const x = 1;").unwrap();
    fs::write(dir.path().join("a.d.ts"), "declare const x: number;").unwrap();

    let error = collect_tests(dir.path()).unwrap_err().to_string();
    assert!(error.contains("duplicate difftsc test name"), "{error}");
    assert!(error.contains("a.ts"), "{error}");
    assert!(error.contains("a.d.ts"), "{error}");
    assert!(
      error.to_lowercase().contains("rename one test")
        || error.to_lowercase().contains("move it into a subdirectory"),
      "{error}"
    );
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
          .into(),
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

  #[test]
  fn type_fact_diff_reports_unexpected_exports() {
    let expected = NormalizedTypeFacts {
      exports: vec![NormalizedExportType {
        file: "/a.ts".to_string(),
        name: "a".to_string(),
        type_str: "number".to_string(),
      }],
      markers: Vec::new(),
    };
    let actual = NormalizedTypeFacts {
      exports: vec![
        NormalizedExportType {
          file: "/a.ts".to_string(),
          name: "a".to_string(),
          type_str: "number".to_string(),
        },
        NormalizedExportType {
          file: "/a.ts".to_string(),
          name: "b".to_string(),
          type_str: "string".to_string(),
        },
      ],
      markers: Vec::new(),
    };
    let diff = diff_type_facts(&expected, &actual).expect("diff");
    assert_eq!(diff.unexpected_exports.len(), 1);
    assert_eq!(diff.unexpected_exports[0].name, "b");
  }

  #[test]
  fn type_fact_diff_reports_unexpected_markers() {
    let expected = NormalizedTypeFacts {
      exports: Vec::new(),
      markers: vec![NormalizedMarkerType {
        file: "/a.ts".to_string(),
        offset: 1,
        line: None,
        column: None,
        type_str: "number".to_string(),
      }],
    };
    let actual = NormalizedTypeFacts {
      exports: Vec::new(),
      markers: vec![
        NormalizedMarkerType {
          file: "/a.ts".to_string(),
          offset: 1,
          line: None,
          column: None,
          type_str: "number".to_string(),
        },
        NormalizedMarkerType {
          file: "/a.ts".to_string(),
          offset: 2,
          line: None,
          column: None,
          type_str: "string".to_string(),
        },
      ],
    };
    let diff = diff_type_facts(&expected, &actual).expect("diff");
    assert_eq!(diff.unexpected_markers.len(), 1);
    assert_eq!(diff.unexpected_markers[0].offset, 2);
  }

  #[test]
  fn export_type_facts_follow_expected_queries() {
    let files = vec![VirtualFile {
      name: "a.ts".to_string(),
      content: r#"export function f() { return 1; }
export const v = 1;
export interface Foo { x: number }
    "#
      .into(),
    }];
    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());
    let program = Program::new(host, file_set.root_keys());
    let _ = program.check();

    let expected = vec![
      ExportTypeFact {
        file: "a.ts".to_string(),
        name: "f".to_string(),
        type_str: String::new(),
      },
      ExportTypeFact {
        file: "a.ts".to_string(),
        name: "v".to_string(),
        type_str: String::new(),
      },
    ];
    let mut exports = collect_export_type_facts(&program, &file_set, &expected);
    exports.sort_by(|a, b| a.name.cmp(&b.name));
    assert_eq!(exports.len(), 2);
    assert_eq!(exports[0].name, "f");
    assert_eq!(exports[1].name, "v");
  }

  #[test]
  fn write_baseline_sorts_type_facts() {
    let dir = tempfile::tempdir().unwrap();
    let path = dir.path().join("baseline.json");
    let diagnostics = TscDiagnostics {
      schema_version: None,
      metadata: TscMetadata::default(),
      diagnostics: vec![
        TscDiagnostic {
          code: 2,
          file: Some("b.ts".to_string()),
          start: 10,
          end: 12,
          category: None,
          message: None,
        },
        TscDiagnostic {
          code: 1,
          file: Some("a.ts".to_string()),
          start: 0,
          end: 1,
          category: None,
          message: None,
        },
      ],
      crash: None,
      type_facts: Some(TypeFacts {
        exports: vec![
          ExportTypeFact {
            file: "b.ts".to_string(),
            name: "b".to_string(),
            type_str: "string".to_string(),
          },
          ExportTypeFact {
            file: "a.ts".to_string(),
            name: "a".to_string(),
            type_str: "number".to_string(),
          },
        ],
        markers: vec![
          TypeAtFact {
            file: "a.ts".to_string(),
            offset: 2,
            line: None,
            column: None,
            type_str: "string".to_string(),
          },
          TypeAtFact {
            file: "a.ts".to_string(),
            offset: 1,
            line: None,
            column: None,
            type_str: "number".to_string(),
          },
        ],
      }),
    };

    write_baseline(&path, &diagnostics).unwrap();
    let parsed = read_baseline(&path).unwrap();
    let type_facts = parsed.type_facts.unwrap();
    assert_eq!(type_facts.exports[0].name, "a");
    assert_eq!(type_facts.exports[1].name, "b");
    assert_eq!(type_facts.markers[0].offset, 1);
    assert_eq!(type_facts.markers[1].offset, 2);

    assert_eq!(parsed.diagnostics[0].file.as_deref(), Some("a.ts"));
    assert_eq!(parsed.diagnostics[1].file.as_deref(), Some("b.ts"));
  }

  #[test]
  fn reads_harness_options_from_fixture_directives() {
    let case_dir = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("fixtures")
      .join("difftsc")
      .join("this_param_call");
    let files = collect_files_recursively(&case_dir).expect("collect fixture files");
    let options = harness_options_from_files(&files);
    assert_eq!(options.strict, Some(true));

    let tsc = options.to_tsc_options_map();
    assert_eq!(tsc.get("strict"), Some(&Value::Bool(true)));
    assert_eq!(tsc.get("noImplicitAny"), Some(&Value::Bool(true)));
  }
}
