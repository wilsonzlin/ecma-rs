#![cfg_attr(not(feature = "with-node"), allow(dead_code, unused_imports))]

use crate::diagnostic::{
  diff_diagnostics, normalize_tsc_diagnostics, DiagnosticDiff, NormalizedDiagnostic,
};
use crate::diagnostic_norm::DiagnosticCode as NormDiagnosticCode;
use crate::expectations::{ExpectationKind, Expectations};
use crate::multifile::normalize_name;
use crate::runner::{run_rust, EngineStatus, HarnessFileSet};
use crate::tsc::{node_available, TscDiagnostics, TscRequest, TscRunner};
use crate::{FailOn, VirtualFile};
use anyhow::{anyhow, Context, Result};
use clap::Args;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::HashMap;
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

#[derive(Debug, Clone, Serialize, Deserialize)]
struct CaseReport {
  name: String,
  status: CaseStatus,
  #[serde(skip_serializing_if = "Option::is_none")]
  expected: Option<Vec<NormalizedDiagnostic>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  actual: Option<Vec<NormalizedDiagnostic>>,
  #[serde(skip_serializing_if = "Option::is_none")]
  diff: Option<DiagnosticDiff>,
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
        notes: vec!["skipped by manifest".to_string()],
      });
      continue;
    }

    let report = run_single_test(&test, &args, runner.as_mut(), &baselines_root);
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
          "missing={}, unexpected={}, mismatched={}",
          d.missing.len(),
          d.unexpected.len(),
          d.mismatched.len()
        )
      })
      .unwrap_or_else(|| "differences detected".to_string());
    eprintln!("  {}: {}", case.name, detail);
  }
}

#[cfg(feature = "with-node")]
fn run_single_test(
  test: &TestCase,
  args: &DifftscArgs,
  runner: Option<&mut TscRunner>,
  baselines_root: &Path,
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
          notes: vec![err.to_string()],
        };
      }
    };
    let expected = normalize_tsc_diagnostics(&baseline.diagnostics);
    let actual = normalize_tsc_diagnostics(&live_tsc.expect("live tsc required").diagnostics);
    let diff = diff_diagnostics(&expected, &actual, args.span_tolerance);
    let status = if diff.is_some() {
      CaseStatus::Mismatch
    } else {
      CaseStatus::Matched
    };
    return CaseReport {
      name: test.name.clone(),
      status,
      expected: Some(expected),
      actual: Some(actual),
      diff,
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
          notes: vec![err.to_string()],
        };
      }
    }
  };

  let file_set = HarnessFileSet::new(&test.files);
  let rust = run_rust(&file_set);
  let expected = normalize_tsc_diagnostics(&tsc_diags.diagnostics);
  if rust.status != EngineStatus::Ok {
    return CaseReport {
      name: test.name.clone(),
      status: CaseStatus::RustFailed,
      expected: Some(expected),
      actual: None,
      diff: None,
      notes: rust.error.into_iter().collect(),
    };
  }

  let actual: Vec<NormalizedDiagnostic> = rust
    .diagnostics
    .iter()
    .filter_map(|diag| match &diag.code {
      Some(NormDiagnosticCode::Rust(code)) => Some(NormalizedDiagnostic {
        code: Some(code.clone()),
        category: diag.severity.clone(),
        file: diag.file.clone(),
        start: diag.start,
        end: diag.end,
        message: diag.message.clone(),
      }),
      _ => None,
    })
    .collect();

  let diff = diff_diagnostics(&expected, &actual, args.span_tolerance);
  let status = if diff.is_some() {
    CaseStatus::Mismatch
  } else {
    CaseStatus::Matched
  };

  CaseReport {
    name: test.name.clone(),
    status,
    expected: Some(expected),
    actual: Some(actual),
    diff,
    notes,
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

  let json = serde_json::to_string_pretty(diagnostics)?;
  fs::write(path, format!("{json}\n"))
    .with_context(|| format!("write baseline at {}", path.display()))?;

  Ok(())
}

fn read_baseline(path: &Path) -> Result<TscDiagnostics> {
  let data =
    fs::read_to_string(path).with_context(|| format!("read baseline {}", path.display()))?;
  let parsed = serde_json::from_str(&data).context("parse baseline JSON")?;
  Ok(parsed)
}

#[cfg(test)]
mod tests {
  use super::*;
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
    let expected = normalize_tsc_diagnostics(&expected_raw);
    let actual = normalize_tsc_diagnostics(&actual_raw);
    assert!(diff_diagnostics(&expected, &actual, 0).is_some());
    assert!(diff_diagnostics(&expected, &actual, 1).is_none());
  }
}
