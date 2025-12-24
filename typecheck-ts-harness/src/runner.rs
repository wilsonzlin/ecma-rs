use crate::directives::HarnessDirective;
use crate::directives::HarnessOptions;
use crate::discover::discover_conformance_tests;
use crate::discover::Filter;
use crate::discover::Shard;
use crate::discover::TestCase;
use crate::multifile::normalize_name;
use crate::profile::ProfileBuilder;
use crate::HarnessError;
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
use tracing::{info, info_span, warn};
use typecheck_ts::Diagnostic;
use typecheck_ts::FileId;
use typecheck_ts::Host;
use typecheck_ts::HostError;
use typecheck_ts::Program;
use typecheck_ts::Span;
use typecheck_ts::TextRange;

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
  #[serde(default)]
  pub directives: Vec<HarnessDirective>,
  #[serde(default)]
  pub options: HarnessOptions,
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
  pub filter_pattern: Option<String>,
  pub shard: Option<Shard>,
  pub json: bool,
  pub update_snapshots: bool,
  pub timeout: Duration,
  pub trace: bool,
  pub profile: bool,
  pub profile_out: PathBuf,
  pub extensions: Vec<String>,
  pub allow_empty: bool,
}

pub fn run_conformance(opts: ConformanceOptions) -> Result<JsonReport> {
  if opts.extensions.is_empty() {
    return Err(HarnessError::InvalidExtensions(
      "no extensions provided".to_string(),
    ));
  }

  let run_start = Instant::now();
  let mut profiler = opts.profile.then(|| ProfileBuilder::new(&opts));

  let mut cases = {
    let span = info_span!("discover_tests", root = %opts.root.display());
    let _enter = span.enter();
    info!(phase = "discover_start", root = %opts.root.display());
    let discovered =
      discover_conformance_tests(&opts.root, &opts.filter, &opts.extensions)?;
    info!(phase = "discover_complete", count = discovered.len());
    discovered
  };

  if cases.is_empty() && !opts.allow_empty {
    return Err(HarnessError::EmptySuite {
      root: opts.root.display().to_string(),
      extensions: opts.extensions.join(","),
    });
  }

  if let Some(shard) = opts.shard {
    let before = cases.len();
    cases = cases
      .into_iter()
      .enumerate()
      .filter(|(idx, _)| shard.includes(*idx))
      .map(|(_, case)| case)
      .collect();
    info!(
      phase = "shard",
      shard_index = shard.index,
      shard_total = shard.total,
      before = before,
      after = cases.len()
    );
  }

  let mut results = Vec::new();
  for case in cases.into_iter() {
    let result = run_single_case(case, opts.timeout);
    if let Some(profiler) = profiler.as_mut() {
      profiler.record_test(&result);
    }
    results.push(result);
  }

  let summary = summarize(&results);
  let wall_time = run_start.elapsed();
  info!(
    phase = "summary",
    duration_ms = wall_time.as_millis(),
    total = summary.total,
    passed = summary.passed,
    failed = summary.failed,
    timed_out = summary.timed_out
  );

  if let Some(profiler) = profiler {
    profiler.write(&summary, wall_time, &opts.profile_out)?;
  }

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
  let span = info_span!("test_case", test_id = %case.id);
  let _enter = span.enter();
  let (tx, rx) = mpsc::channel();
  let cloned = case.clone();

  info!(phase = "start", timeout_ms = timeout.as_millis());
  std::thread::spawn({
    let span = span.clone();
    move || {
      let _entered = span.enter();
      let result = execute_case(cloned);
      let _ = tx.send(result);
    }
  });

  match rx.recv_timeout(timeout) {
    Ok(mut result) => {
      info!(
        phase = "finish",
        status = ?result.status,
        duration_ms = result.duration_ms
      );
      result.diagnostics.sort();
      result
    }
    Err(_) => {
      warn!(phase = "timeout", timeout_ms = timeout.as_millis());
      TestResult {
        id: case.id,
        path: case.path.display().to_string(),
        status: TestStatus::Timeout,
        duration_ms: timeout.as_millis(),
        diagnostics: Vec::new(),
        notes: case.notes,
        directives: case.directives,
        options: case.options,
      }
    }
  }
}

fn execute_case(case: TestCase) -> TestResult {
  let start = Instant::now();
  let notes = case.notes.clone();
  let directives = case.directives.clone();
  let options = case.options.clone();
  let host = HarnessHost::new(&case.deduped_files);
  let roots = host.root_files();

  info!(phase = "rust_check_start", file_count = case.files.len());
  let result = std::panic::catch_unwind(|| Program::new(host, roots).check());
  let duration_ms = start.elapsed().as_millis();

  match result {
    Ok(diagnostics) => {
      let status = categorize(&diagnostics);
      info!(
        phase = "rust_check_complete",
        status = ?status,
        duration_ms = duration_ms
      );
      TestResult {
        id: case.id,
        path: case.path.display().to_string(),
        status,
        duration_ms,
        diagnostics,
        notes,
        directives,
        options,
      }
    }
    Err(_) => {
      warn!(phase = "ice", duration_ms = duration_ms);
      TestResult {
        id: case.id,
        path: case.path.display().to_string(),
        status: TestStatus::Ice,
        duration_ms,
        diagnostics: vec![Diagnostic::error(
          "ICE0001",
          "typechecker panicked",
          Span::new(FileId(0), TextRange::new(0, 0)),
        )],
        notes,
        directives,
        options,
      }
    }
  }
}

fn categorize(diags: &[Diagnostic]) -> TestStatus {
  if diags.is_empty() {
    return TestStatus::Passed;
  }

  let has_code_prefix = |prefix: &str| {
    diags
      .iter()
      .any(|d| d.code.as_str().to_ascii_uppercase().starts_with(prefix))
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
    let mut normalized_names = Vec::with_capacity(files.len());
    for file in files {
      normalized_names.push(normalize_name(&file.name));
    }

    let mut last_occurrence = HashMap::new();
    for (idx, normalized) in normalized_names.iter().enumerate() {
      last_occurrence.insert(normalized.clone(), idx);
    }

    let mut stored = Vec::with_capacity(last_occurrence.len());
    let mut name_to_id = HashMap::new();

    for (idx, normalized) in normalized_names.into_iter().enumerate() {
      if last_occurrence.get(&normalized).copied() != Some(idx) {
        continue;
      }

      let file_id = FileId(stored.len() as u32);
      name_to_id.insert(normalized.clone(), file_id);
      stored.push(HarnessFile {
        normalized,
        content: Arc::from(files[idx].content.clone()),
      });
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
    let is_relative = specifier.starts_with("./") || specifier.starts_with("../");
    if !is_relative {
      let normalized = normalize_name(specifier);
      return self.name_to_id.get(&normalized).copied();
    }

    // TypeScript-style relative resolution:
    // 1) exact match
    // 2) add extensions if missing
    // 3) resolve to directory index files
    // For explicit .js/.jsx specifiers, try .ts/.tsx neighbors after the exact path.
    let base = self.files.get(from.0 as usize)?;
    let parent = Path::new(&base.normalized)
      .parent()
      .unwrap_or_else(|| Path::new(""));
    let joined = parent.join(specifier);
    let base_candidate = normalize_name(joined.to_string_lossy().as_ref());

    let mut candidates = Vec::new();
    candidates.push(base_candidate.clone());

    if base_candidate.ends_with(".js") {
      let trimmed = base_candidate.trim_end_matches(".js");
      candidates.push(format!("{trimmed}.ts"));
      candidates.push(format!("{trimmed}.tsx"));
    } else if base_candidate.ends_with(".jsx") {
      let trimmed = base_candidate.trim_end_matches(".jsx");
      candidates.push(format!("{trimmed}.tsx"));
    } else if !has_known_extension(&base_candidate) {
      for ext in ["ts", "tsx", "d.ts", "js", "jsx"] {
        candidates.push(format!("{base_candidate}.{ext}"));
      }
    }

    let base_path = Path::new(&base_candidate);
    for ext in [
      "index.ts",
      "index.tsx",
      "index.d.ts",
      "index.js",
      "index.jsx",
    ] {
      let joined = base_path.join(ext);
      candidates.push(normalize_name(joined.to_string_lossy().as_ref()));
    }

    for cand in candidates {
      if let Some(found) = self.name_to_id.get(&cand) {
        return Some(*found);
      }
    }

    None
  }
}

fn has_known_extension(name: &str) -> bool {
  name.ends_with(".d.ts")
    || name.ends_with(".ts")
    || name.ends_with(".tsx")
    || name.ends_with(".js")
    || name.ends_with(".jsx")
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
    let files = vec![VirtualFile {
      name: "inline.ts".to_string(),
      content: "const x: number = 1;".to_string(),
    }];
    let case = TestCase {
      id: "inline".to_string(),
      path: PathBuf::from("inline.ts"),
      deduped_files: files.clone(),
      files,
      directives: Vec::new(),
      options: HarnessOptions::default(),
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
  fn resolve_directory_imports_to_index_files() {
    let files = vec![
      VirtualFile {
        name: "src/main.ts".to_string(),
        content: "import \"./dir\";".to_string(),
      },
      VirtualFile {
        name: "src/dir/index.ts".to_string(),
        content: "".to_string(),
      },
    ];
    let host = HarnessHost::new(&files);
    assert_eq!(host.resolve(FileId(0), "./dir"), Some(FileId(1)));
  }

  #[test]
  fn resolve_prefers_declaration_files() {
    let files = vec![
      VirtualFile {
        name: "main.ts".to_string(),
        content: "import \"./foo\";".to_string(),
      },
      VirtualFile {
        name: "foo.d.ts".to_string(),
        content: "export declare const value: number;".to_string(),
      },
    ];
    let host = HarnessHost::new(&files);
    assert_eq!(host.resolve(FileId(0), "./foo"), Some(FileId(1)));
  }

  #[test]
  fn resolve_maps_js_specifier_to_ts() {
    let files = vec![
      VirtualFile {
        name: "main.ts".to_string(),
        content: "import \"./foo.js\";".to_string(),
      },
      VirtualFile {
        name: "foo.ts".to_string(),
        content: "export const value = 1;".to_string(),
      },
    ];
    let host = HarnessHost::new(&files);
    assert_eq!(host.resolve(FileId(0), "./foo.js"), Some(FileId(1)));
  }

  #[test]
  fn host_deduplicates_virtual_files() {
    use std::collections::HashSet;

    let files = vec![
      VirtualFile {
        name: "a.ts".to_string(),
        content: "first version".to_string(),
      },
      VirtualFile {
        name: "./a.ts".to_string(),
        content: "second version".to_string(),
      },
      VirtualFile {
        name: "b.ts".to_string(),
        content: "unrelated".to_string(),
      },
    ];

    let host = HarnessHost::new(&files);
    let roots = host.root_files();

    let unique_names = files
      .iter()
      .map(|f| normalize_name(&f.name))
      .collect::<HashSet<_>>();
    assert_eq!(roots.len(), unique_names.len());

    let from = *roots.last().unwrap();
    let a_id = host.resolve(from, "a.ts").expect("a.ts should resolve");
    assert!(roots.contains(&a_id));
    assert_eq!(&*host.file_text(a_id).unwrap(), "second version");

    // Resolution should map extensionless relative imports to the deduplicated FileId.
    assert_eq!(host.resolve(from, "./a"), Some(a_id));
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
