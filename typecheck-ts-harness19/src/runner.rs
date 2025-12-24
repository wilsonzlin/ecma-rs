use crate::discover::discover_conformance_tests;
use crate::discover::Filter;
use crate::discover::Shard;
use crate::discover::TestCase;
use crate::Result;
use crate::VirtualFile;
use diagnostics::Diagnostic as InternalDiagnostic;
use diagnostics::Severity as InternalSeverity;
use serde::Deserialize;
use serde::Serialize;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;
use typecheck_ts_h19::FileId;
use typecheck_ts_h19::Host;
use typecheck_ts_h19::{self};

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
pub struct JsonSpan {
  pub file: u32,
  pub start: u32,
  pub end: u32,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum JsonSeverity {
  Error,
  Warning,
  Note,
  Help,
}

impl Default for JsonSeverity {
  fn default() -> Self {
    JsonSeverity::Error
  }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
pub struct JsonDiagnostic {
  pub code: String,
  pub message: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub span: Option<JsonSpan>,
  #[serde(default)]
  pub severity: JsonSeverity,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub notes: Vec<String>,
}

impl JsonDiagnostic {
  pub fn new(code: impl Into<String>, message: impl Into<String>, span: Option<JsonSpan>) -> Self {
    Self {
      code: code.into(),
      message: message.into(),
      span,
      severity: JsonSeverity::Error,
      notes: Vec::new(),
    }
  }

  fn from_internal(diag: InternalDiagnostic) -> Self {
    let InternalDiagnostic {
      code,
      severity,
      message,
      primary,
      notes,
      ..
    } = diag;
    let span = Some(JsonSpan {
      file: primary.file.0,
      start: primary.range.start,
      end: primary.range.end,
    });

    let severity = match severity {
      InternalSeverity::Error => JsonSeverity::Error,
      InternalSeverity::Warning => JsonSeverity::Warning,
      InternalSeverity::Note => JsonSeverity::Note,
      InternalSeverity::Help => JsonSeverity::Help,
    };

    Self {
      code: code.to_string(),
      message,
      span,
      severity,
      notes,
    }
  }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TestStatus {
  Passed,
  ParseError,
  BindError,
  TypeError,
  Ice,
  InternalError,
  Timeout,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestResult {
  pub id: String,
  pub path: String,
  pub status: TestStatus,
  pub duration_ms: u128,
  pub diagnostics: Vec<JsonDiagnostic>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub notes: Vec<String>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Summary {
  pub total: usize,
  pub passed: usize,
  pub failed: usize,
  pub timed_out: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct JsonReport {
  pub summary: Summary,
  pub results: Vec<TestResult>,
}

#[derive(Debug, Clone)]
pub struct ConformanceOptions {
  pub root: PathBuf,
  pub filter: Filter,
  pub shard: Option<Shard>,
  pub json: bool,
  pub update_snapshots: bool,
  pub timeout: Duration,
  pub trace: bool,
  pub profile: bool,
}

pub fn run_conformance(opts: ConformanceOptions) -> Result<JsonReport> {
  let mut cases = discover_conformance_tests(&opts.root, &opts.filter)?;

  if let Some(shard) = opts.shard {
    cases = cases
      .into_iter()
      .enumerate()
      .filter(|(idx, _)| shard.includes(*idx))
      .map(|(_, case)| case)
      .collect();
  }

  let mut results = Vec::new();
  for case in cases.into_iter() {
    let result = run_single_case(case, opts.timeout);
    results.push(result);
  }

  let summary = summarize(&results);
  Ok(JsonReport { summary, results })
}

fn summarize(results: &[TestResult]) -> Summary {
  let mut summary = Summary::default();
  summary.total = results.len();
  for result in results {
    match result.status {
      TestStatus::Passed => summary.passed += 1,
      TestStatus::Timeout => summary.timed_out += 1,
      _ => summary.failed += 1,
    }
  }
  summary
}

fn run_single_case(case: TestCase, timeout: Duration) -> TestResult {
  use std::sync::mpsc;
  let (tx, rx) = mpsc::channel();
  let cloned = case.clone();

  std::thread::spawn(move || {
    let result = execute_case(cloned);
    let _ = tx.send(result);
  });

  match rx.recv_timeout(timeout) {
    Ok(mut result) => {
      // Ensure deterministic ordering of diagnostics for stable JSON output.
      result.diagnostics.sort_by(|a, b| {
        let code_ord = a.code.cmp(&b.code);
        if code_ord != std::cmp::Ordering::Equal {
          return code_ord;
        }

        let span_a = a.span;
        let span_b = b.span;

        match (span_a, span_b) {
          (Some(sa), Some(sb)) => (sa.file, sa.start, sa.end).cmp(&(sb.file, sb.start, sb.end)),
          (Some(_), None) => std::cmp::Ordering::Less,
          (None, Some(_)) => std::cmp::Ordering::Greater,
          (None, None) => std::cmp::Ordering::Equal,
        }
      });
      result
    }
    Err(_) => TestResult {
      id: case.id,
      path: case.path.display().to_string(),
      status: TestStatus::Timeout,
      duration_ms: timeout.as_millis(),
      diagnostics: Vec::new(),
      notes: case.notes,
    },
  }
}

fn execute_case(case: TestCase) -> TestResult {
  let start = Instant::now();
  let notes = case.notes.clone();
  let host = HarnessHost::new(&case.files);

  let result = std::panic::catch_unwind(|| typecheck_ts_h19::check_program(&host));
  let duration_ms = start.elapsed().as_millis();

  match result {
    Ok(Ok(report)) => {
      let diagnostics = report
        .diagnostics
        .into_iter()
        .map(JsonDiagnostic::from_internal)
        .collect::<Vec<_>>();
      let status = categorize(&diagnostics);

      TestResult {
        id: case.id,
        path: case.path.display().to_string(),
        status,
        duration_ms,
        diagnostics,
        notes,
      }
    }
    Ok(Err(err)) => TestResult {
      id: case.id,
      path: case.path.display().to_string(),
      status: TestStatus::InternalError,
      duration_ms,
      diagnostics: vec![JsonDiagnostic::new("HOST", err.to_string(), None)],
      notes,
    },
    Err(_) => TestResult {
      id: case.id,
      path: case.path.display().to_string(),
      status: TestStatus::Ice,
      duration_ms,
      diagnostics: vec![JsonDiagnostic::new("ICE0001", "typechecker panicked", None)],
      notes,
    },
  }
}

fn categorize(diags: &[JsonDiagnostic]) -> TestStatus {
  if diags.is_empty() {
    return TestStatus::Passed;
  }

  if diags
    .iter()
    .any(|d| d.code.to_ascii_uppercase().starts_with("PARSE"))
  {
    return TestStatus::ParseError;
  }

  if diags
    .iter()
    .any(|d| d.code.to_ascii_uppercase().starts_with("BIND"))
  {
    return TestStatus::BindError;
  }

  if diags
    .iter()
    .any(|d| d.code.to_ascii_uppercase().starts_with("ICE"))
  {
    return TestStatus::Ice;
  }

  TestStatus::TypeError
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn categorizes_parse() {
    let diags = vec![JsonDiagnostic::new("PARSE", "", None)];
    assert_eq!(categorize(&diags), TestStatus::ParseError);
  }

  #[test]
  fn categorizes_bind() {
    let diags = vec![JsonDiagnostic::new("BIND001", "", None)];
    assert_eq!(categorize(&diags), TestStatus::BindError);
  }

  #[test]
  fn categorizes_ice() {
    let diags = vec![JsonDiagnostic::new("ICE999", "", None)];
    assert_eq!(categorize(&diags), TestStatus::Ice);
  }

  #[test]
  fn categorizes_type_default() {
    let diags = vec![JsonDiagnostic::new("T100", "", None)];
    assert_eq!(categorize(&diags), TestStatus::TypeError);
  }
}

struct HarnessHost {
  files: Vec<HarnessFile>,
  name_to_id: HashMap<String, FileId>,
}

struct HarnessFile {
  normalized: String,
  content: String,
}

impl HarnessHost {
  fn new(files: &[VirtualFile]) -> Self {
    let mut stored = Vec::with_capacity(files.len());
    let mut name_to_id = HashMap::new();

    for (idx, file) in files.iter().enumerate() {
      let normalized = normalize_name(&file.name);
      stored.push(HarnessFile {
        normalized: normalized.clone(),
        content: file.content.clone(),
      });
      name_to_id.insert(normalized, idx);
    }

    Self {
      files: stored,
      name_to_id,
    }
  }
}

impl Host for HarnessHost {
  fn files(&self) -> Vec<FileId> {
    (0..self.files.len()).collect()
  }

  fn file_name(&self, file_id: FileId) -> Option<&str> {
    self.files.get(file_id).map(|f| f.normalized.as_str())
  }

  fn file_text(
    &self,
    file_id: FileId,
  ) -> std::result::Result<Arc<str>, typecheck_ts_h19::HostError> {
    let file = self
      .files
      .get(file_id)
      .ok_or(typecheck_ts_h19::HostError::MissingFile(file_id))?;
    Ok(Arc::from(file.content.as_str()))
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    let mut candidates = Vec::new();
    let normalized = normalize_name(specifier);
    candidates.push(normalized.clone());

    if !normalized.ends_with(".ts") && !normalized.ends_with(".tsx") {
      candidates.push(format!("{}.ts", normalized));
      candidates.push(format!("{}.tsx", normalized));
    }

    for cand in &candidates {
      if let Some(found) = self.name_to_id.get(cand) {
        return Some(*found);
      }
    }

    if let Some(base) = self.files.get(from) {
      let parent = Path::new(&base.normalized)
        .parent()
        .unwrap_or_else(|| Path::new(""));
      for cand in candidates {
        let joined = parent.join(&cand);
        let normalized = normalize_name(joined.to_string_lossy().as_ref());
        if let Some(found) = self.name_to_id.get(&normalized) {
          return Some(*found);
        }
      }
    }

    None
  }
}

fn normalize_name(path: &str) -> String {
  use std::path::Component;
  let mut normalized = PathBuf::new();
  for component in Path::new(path).components() {
    match component {
      Component::CurDir => {}
      Component::ParentDir => {
        normalized.pop();
      }
      other => normalized.push(other.as_os_str()),
    }
  }

  normalized.to_string_lossy().replace('\\', "/")
}
