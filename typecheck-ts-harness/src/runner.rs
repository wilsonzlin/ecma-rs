use crate::discover::discover_conformance_tests;
use crate::discover::Filter;
use crate::discover::Shard;
use crate::discover::TestCase;
use crate::Result;
use crate::VirtualFile;
use serde::Deserialize;
use serde::Serialize;
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;
use typecheck_ts::Diagnostic;
use typecheck_ts::FileId;
use typecheck_ts::Host;
use typecheck_ts::HostError;
use typecheck_ts::Program;
use typecheck_ts::Severity;

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
  pub diagnostics: Vec<Diagnostic>,
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
      result.diagnostics.sort_by(|a, b| {
        let code_a = a.code.as_deref().unwrap_or("");
        let code_b = b.code.as_deref().unwrap_or("");
        let code_ord = code_a.cmp(code_b);
        if code_ord != std::cmp::Ordering::Equal {
          return code_ord;
        }

        let span_a = a.span;
        let span_b = b.span;

        match (span_a, span_b) {
          (Some(sa), Some(sb)) => {
            (sa.file, sa.range.start, sa.range.end).cmp(&(sb.file, sb.range.start, sb.range.end))
          }
          (Some(_), None) => std::cmp::Ordering::Less,
          (None, Some(_)) => std::cmp::Ordering::Greater,
          (None, None) => a.message.cmp(&b.message),
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
  let roots = host.root_files();

  let result = std::panic::catch_unwind(|| Program::new(host, roots).check());
  let duration_ms = start.elapsed().as_millis();

  match result {
    Ok(diagnostics) => {
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
    Err(_) => TestResult {
      id: case.id,
      path: case.path.display().to_string(),
      status: TestStatus::Ice,
      duration_ms,
      diagnostics: vec![Diagnostic {
        code: Some("ICE0001".to_string()),
        message: "typechecker panicked".to_string(),
        span: None,
        severity: Severity::Error,
      }],
      notes,
    },
  }
}

fn categorize(diags: &[Diagnostic]) -> TestStatus {
  if diags.is_empty() {
    return TestStatus::Passed;
  }

  let has_code_prefix = |prefix: &str| {
    diags.iter().any(|d| {
      d.code
        .as_deref()
        .is_some_and(|code| code.to_ascii_uppercase().starts_with(prefix))
    })
  };

  if has_code_prefix("PARSE") {
    return TestStatus::ParseError;
  }

  if has_code_prefix("BIND") {
    return TestStatus::BindError;
  }

  if has_code_prefix("HOST") {
    return TestStatus::InternalError;
  }

  if has_code_prefix("ICE") {
    return TestStatus::Ice;
  }

  TestStatus::TypeError
}

struct HarnessHost {
  files: Vec<HarnessFile>,
  name_to_id: HashMap<String, FileId>,
}

struct HarnessFile {
  normalized: String,
  content: Arc<str>,
}

impl HarnessHost {
  fn new(files: &[VirtualFile]) -> Self {
    let mut stored = Vec::with_capacity(files.len());
    let mut name_to_id = HashMap::new();

    for (idx, file) in files.iter().enumerate() {
      let normalized = normalize_name(&file.name);
      stored.push(HarnessFile {
        normalized: normalized.clone(),
        content: Arc::from(file.content.clone()),
      });
      name_to_id.insert(normalized, FileId(idx as u32));
    }

    Self {
      files: stored,
      name_to_id,
    }
  }

  fn root_files(&self) -> Vec<FileId> {
    (0..self.files.len()).map(|i| FileId(i as u32)).collect()
  }
}

impl Host for HarnessHost {
  fn file_text(&self, file: FileId) -> std::result::Result<Arc<str>, HostError> {
    let idx = file.0 as usize;
    self
      .files
      .get(idx)
      .map(|f| f.content.clone())
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    let mut candidates = Vec::new();
    let normalized = normalize_name(specifier);
    candidates.push(normalized.clone());

    if !normalized.ends_with(".d.ts")
      && !normalized.ends_with(".ts")
      && !normalized.ends_with(".tsx")
    {
      candidates.push(format!("{normalized}.ts"));
      candidates.push(format!("{normalized}.tsx"));
      candidates.push(format!("{normalized}.d.ts"));
    }

    for cand in &candidates {
      if let Some(found) = self.name_to_id.get(cand) {
        return Some(*found);
      }
    }

    if let Some(base) = self.files.get(from.0 as usize) {
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

fn normalize_name(name: &str) -> String {
  use std::path::Component;
  let name = name.replace('\\', "/");
  let mut normalized = PathBuf::new();
  for component in Path::new(&name).components() {
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

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn shard_parse_rejects_invalid() {
    assert!(Shard::parse("bad").is_err());
    assert!(Shard::parse("1/0").is_err());
    assert!(Shard::parse("2/2").is_err());
  }

  #[test]
  fn conformance_runner_categorizes_empty_as_passed() {
    assert_eq!(categorize(&[]), TestStatus::Passed);
  }

  #[test]
  fn conformance_runner_runs_single_case() {
    let case = TestCase {
      id: "inline".to_string(),
      path: PathBuf::from("inline.ts"),
      files: vec![VirtualFile {
        name: "inline.ts".to_string(),
        content: "const x: number = 1;".to_string(),
      }],
      module_directive: None,
      notes: Vec::new(),
    };

    let result = execute_case(case);
    assert_eq!(result.status, TestStatus::Passed);
  }

  #[test]
  fn host_resolves_missing_file_errors() {
    let host = HarnessHost::new(&[]);
    assert!(host.file_text(FileId(0)).is_err());
  }

  #[test]
  fn normalize_name_strips_dot_slash() {
    assert_eq!(normalize_name("./foo.ts"), "foo.ts");
  }

  #[test]
  fn normalize_name_preserves_subdirs() {
    assert_eq!(normalize_name("./sub/foo.ts"), "sub/foo.ts");
  }

  #[test]
  fn normalize_name_normalizes_backslashes() {
    assert_eq!(normalize_name(".\\sub\\foo.ts"), "sub/foo.ts");
  }
}
