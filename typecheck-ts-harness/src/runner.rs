use crate::diagnostic_norm::{
  describe, normalize_rust_diagnostics, normalize_tsc_diagnostics, sort_diagnostics,
  within_tolerance, NormalizedDiagnostic,
};
use crate::difftsc::{TscDiagnostic, TscDiagnostics};
use crate::discover::{discover_conformance_tests, Filter, Shard, TestCase};
use crate::multifile::normalize_name;
use crate::{Result, VirtualFile};
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::sync::Arc;
use std::time::{Duration, Instant};
use typecheck_ts::{FileId, Host, HostError, Program};
use walkdir::WalkDir;

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum CompareMode {
  Auto,
  None,
  Tsc,
  Snapshot,
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TestOutcome {
  Match,
  RustExtraDiagnostics,
  RustMissingDiagnostics,
  SpanMismatch,
  CodeMismatch,
  RustIce,
  TscCrashed,
  Timeout,
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
  pub compare: CompareMode,
  pub node_path: PathBuf,
  pub span_tolerance: u32,
  pub allow_mismatches: bool,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct OutcomeCounts {
  #[serde(rename = "match")]
  pub match_: usize,
  pub rust_extra_diagnostics: usize,
  pub rust_missing_diagnostics: usize,
  pub span_mismatch: usize,
  pub code_mismatch: usize,
  pub rust_ice: usize,
  pub tsc_crashed: usize,
  pub timeout: usize,
}

impl OutcomeCounts {
  fn increment(&mut self, outcome: TestOutcome) {
    match outcome {
      TestOutcome::Match => self.match_ += 1,
      TestOutcome::RustExtraDiagnostics => self.rust_extra_diagnostics += 1,
      TestOutcome::RustMissingDiagnostics => self.rust_missing_diagnostics += 1,
      TestOutcome::SpanMismatch => self.span_mismatch += 1,
      TestOutcome::CodeMismatch => self.code_mismatch += 1,
      TestOutcome::RustIce => self.rust_ice += 1,
      TestOutcome::TscCrashed => self.tsc_crashed += 1,
      TestOutcome::Timeout => self.timeout += 1,
    }
  }

  fn mismatches(&self) -> usize {
    self.rust_extra_diagnostics
      + self.rust_missing_diagnostics
      + self.span_mismatch
      + self.code_mismatch
      + self.rust_ice
      + self.tsc_crashed
      + self.timeout
  }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct Summary {
  pub total: usize,
  pub outcomes: OutcomeCounts,
}

impl Summary {
  pub fn has_mismatches(&self) -> bool {
    self.outcomes.mismatches() > 0
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ConformanceReport {
  pub summary: Summary,
  pub compare_mode: CompareMode,
  pub results: Vec<TestResult>,
}

pub type JsonReport = ConformanceReport;

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum EngineStatus {
  Ok,
  Ice,
  Crashed,
  Skipped,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct EngineDiagnostics {
  pub status: EngineStatus,
  pub diagnostics: Vec<NormalizedDiagnostic>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub error: Option<String>,
}

impl EngineDiagnostics {
  fn ok(mut diagnostics: Vec<NormalizedDiagnostic>) -> Self {
    sort_diagnostics(&mut diagnostics);
    Self {
      status: EngineStatus::Ok,
      diagnostics,
      error: None,
    }
  }

  fn crashed(error: impl Into<String>) -> Self {
    Self {
      status: EngineStatus::Crashed,
      diagnostics: Vec::new(),
      error: Some(error.into()),
    }
  }

  fn ice(error: impl Into<String>) -> Self {
    Self {
      status: EngineStatus::Ice,
      diagnostics: Vec::new(),
      error: Some(error.into()),
    }
  }

  fn skipped(message: Option<String>) -> Self {
    Self {
      status: EngineStatus::Skipped,
      diagnostics: Vec::new(),
      error: message,
    }
  }
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestResult {
  pub id: String,
  pub path: String,
  pub outcome: TestOutcome,
  pub duration_ms: u128,
  pub rust: EngineDiagnostics,
  pub tsc: EngineDiagnostics,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub notes: Vec<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub detail: Option<MismatchDetail>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MismatchDetail {
  pub message: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub rust: Option<NormalizedDiagnostic>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub tsc: Option<NormalizedDiagnostic>,
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct HarnessOptions {
  pub module: Option<String>,
}

impl HarnessOptions {
  fn from_test_case(case: &TestCase) -> Self {
    HarnessOptions {
      module: case.module_directive.clone(),
    }
  }

  fn to_env_json(&self) -> Option<String> {
    if self.module.is_none() {
      return None;
    }

    serde_json::to_string(self).ok()
  }
}

#[derive(Clone)]
struct HarnessFile {
  normalized: String,
  content: Arc<str>,
}

#[derive(Clone)]
struct HarnessFileSet {
  files: Vec<HarnessFile>,
  name_to_id: HashMap<String, FileId>,
}

impl HarnessFileSet {
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

  fn file_name(&self, file: FileId) -> Option<String> {
    self
      .files
      .get(file.0 as usize)
      .map(|f| f.normalized.clone())
  }

  fn resolve(&self, normalized: &str) -> Option<FileId> {
    self.name_to_id.get(normalized).copied()
  }

  fn iter(&self) -> impl Iterator<Item = &HarnessFile> {
    self.files.iter()
  }

  fn write_to_dir(&self, dir: &Path) -> std::io::Result<()> {
    for file in &self.files {
      let path = dir.join(&file.normalized);
      if let Some(parent) = path.parent() {
        std::fs::create_dir_all(parent)?;
      }
      std::fs::write(&path, &*file.content)?;
    }
    Ok(())
  }
}

pub fn run_conformance(opts: ConformanceOptions) -> Result<ConformanceReport> {
  let mut cases = discover_conformance_tests(&opts.root, &opts.filter)?;

  if let Some(shard) = opts.shard {
    cases = cases
      .into_iter()
      .enumerate()
      .filter(|(idx, _)| shard.includes(*idx))
      .map(|(_, case)| case)
      .collect();
  }

  let tsc_runner = TscRunner::new(opts.node_path.clone());
  let tsc_available = tsc_runner.available();
  let snapshot_store = SnapshotStore::new(&opts.root);
  let compare_mode = resolve_compare_mode(opts.compare, tsc_available, &snapshot_store);

  let mut results = Vec::new();
  for case in cases.into_iter() {
    let result = run_single_case(
      case,
      compare_mode,
      &tsc_runner,
      tsc_available,
      &snapshot_store,
      &opts,
    );
    results.push(result);
  }

  let summary = summarize(&results);
  Ok(ConformanceReport {
    summary,
    compare_mode,
    results,
  })
}

fn resolve_compare_mode(
  requested: CompareMode,
  tsc_available: bool,
  snapshots: &SnapshotStore,
) -> CompareMode {
  match requested {
    CompareMode::Auto => {
      if tsc_available {
        CompareMode::Tsc
      } else if snapshots.has_any() {
        eprintln!("tsc unavailable; falling back to conformance snapshots");
        CompareMode::Snapshot
      } else {
        eprintln!("warning: comparison disabled (tsc unavailable and no snapshots found)");
        CompareMode::None
      }
    }
    other => other,
  }
}

fn run_single_case(
  case: TestCase,
  compare_mode: CompareMode,
  tsc_runner: &TscRunner,
  tsc_available: bool,
  snapshots: &SnapshotStore,
  opts: &ConformanceOptions,
) -> TestResult {
  let (tx, rx) = mpsc::channel();
  let cloned_runner = tsc_runner.clone();
  let cloned_snapshots = snapshots.clone();
  let timeout_id = case.id.clone();
  let timeout_path = case.path.display().to_string();
  let timeout_notes = case.notes.clone();
  let timeout = opts.timeout;
  let span_tolerance = opts.span_tolerance;
  let update_snapshots = opts.update_snapshots;
  std::thread::spawn(move || {
    let result = execute_case(
      case,
      compare_mode,
      cloned_runner,
      tsc_available,
      cloned_snapshots,
      span_tolerance,
      update_snapshots,
    );
    let _ = tx.send(result);
  });

  match rx.recv_timeout(timeout) {
    Ok(result) => result,
    Err(_) => TestResult {
      id: timeout_id,
      path: timeout_path,
      outcome: TestOutcome::Timeout,
      duration_ms: timeout.as_millis(),
      rust: EngineDiagnostics::skipped(None),
      tsc: EngineDiagnostics::skipped(None),
      notes: timeout_notes,
      detail: None,
    },
  }
}

fn execute_case(
  case: TestCase,
  compare_mode: CompareMode,
  tsc_runner: TscRunner,
  tsc_available: bool,
  snapshots: SnapshotStore,
  span_tolerance: u32,
  update_snapshots: bool,
) -> TestResult {
  let start = Instant::now();
  let notes = case.notes.clone();
  let file_set = HarnessFileSet::new(&case.files);
  let harness_options = HarnessOptions::from_test_case(&case);

  let rust = run_rust(&file_set);

  let mut tsc_raw: Option<Vec<TscDiagnostic>> = None;
  let tsc = match compare_mode {
    CompareMode::None => EngineDiagnostics::skipped(Some("comparison disabled".to_string())),
    CompareMode::Tsc => {
      if tsc_available {
        let (diag, raw) = run_tsc_with_raw(&tsc_runner, &file_set, &harness_options);
        tsc_raw = raw;
        diag
      } else {
        EngineDiagnostics::crashed("tsc unavailable")
      }
    }
    CompareMode::Snapshot => {
      if update_snapshots {
        if tsc_available {
          let (diag, raw) = run_tsc_with_raw(&tsc_runner, &file_set, &harness_options);
          tsc_raw = raw;
          diag
        } else {
          EngineDiagnostics::crashed("tsc unavailable for snapshot update")
        }
      } else {
        match snapshots.load(&case.id) {
          Ok(diags) => {
            tsc_raw = Some(diags.clone());
            EngineDiagnostics::ok(normalize_tsc_diagnostics(&diags))
          }
          Err(err) => EngineDiagnostics::crashed(format!("missing snapshot: {err}")),
        }
      }
    }
    CompareMode::Auto => unreachable!("compare mode should be resolved before execution"),
  };

  if update_snapshots {
    if let Some(raw) = tsc_raw.as_ref() {
      let _ = snapshots.save(&case.id, raw);
    }
  }

  let (outcome, detail) = compute_outcome(compare_mode, &rust, &tsc, span_tolerance);

  TestResult {
    id: case.id,
    path: case.path.display().to_string(),
    outcome,
    duration_ms: start.elapsed().as_millis(),
    rust,
    tsc,
    notes,
    detail,
  }
}

fn run_rust(file_set: &HarnessFileSet) -> EngineDiagnostics {
  let host = HarnessHost::new(file_set.clone());
  let roots = file_set.root_files();
  let result = std::panic::catch_unwind(|| {
    let program = Program::new(host, roots);
    program.check()
  });
  match result {
    Ok(diags) => EngineDiagnostics::ok(normalize_rust_diagnostics(&diags, |id| {
      file_set.file_name(id)
    })),
    Err(_) => EngineDiagnostics::ice("typechecker panicked"),
  }
}

fn run_tsc_with_raw(
  runner: &TscRunner,
  file_set: &HarnessFileSet,
  options: &HarnessOptions,
) -> (EngineDiagnostics, Option<Vec<TscDiagnostic>>) {
  match runner.run(file_set, options) {
    Ok(diags) => (
      EngineDiagnostics::ok(normalize_tsc_diagnostics(&diags)),
      Some(diags),
    ),
    Err(err) => (EngineDiagnostics::crashed(err), None),
  }
}

fn compute_outcome(
  compare_mode: CompareMode,
  rust: &EngineDiagnostics,
  tsc: &EngineDiagnostics,
  span_tolerance: u32,
) -> (TestOutcome, Option<MismatchDetail>) {
  if rust.status == EngineStatus::Ice {
    return (
      TestOutcome::RustIce,
      rust.error.as_ref().map(|msg| MismatchDetail {
        message: msg.clone(),
        rust: None,
        tsc: None,
      }),
    );
  }

  if matches!(compare_mode, CompareMode::None) {
    return (TestOutcome::Match, None);
  }

  if tsc.status != EngineStatus::Ok {
    return (
      TestOutcome::TscCrashed,
      tsc.error.as_ref().map(|msg| MismatchDetail {
        message: msg.clone(),
        rust: None,
        tsc: None,
      }),
    );
  }

  diff_diagnostics(&rust.diagnostics, &tsc.diagnostics, span_tolerance)
}

fn diff_diagnostics(
  rust_diags: &[NormalizedDiagnostic],
  tsc_diags: &[NormalizedDiagnostic],
  span_tolerance: u32,
) -> (TestOutcome, Option<MismatchDetail>) {
  let mut rust_sorted = rust_diags.to_vec();
  let mut tsc_sorted = tsc_diags.to_vec();
  sort_diagnostics(&mut rust_sorted);
  sort_diagnostics(&mut tsc_sorted);

  let len = rust_sorted.len().min(tsc_sorted.len());
  for idx in 0..len {
    let rust = &rust_sorted[idx];
    let tsc = &tsc_sorted[idx];
    if rust.file != tsc.file
      || !within_tolerance(rust.start, tsc.start, span_tolerance)
      || !within_tolerance(rust.end, tsc.end, span_tolerance)
    {
      return (
        TestOutcome::SpanMismatch,
        Some(MismatchDetail {
          message: format!(
            "span mismatch between {} and {}",
            describe(rust),
            describe(tsc)
          ),
          rust: Some(rust.clone()),
          tsc: Some(tsc.clone()),
        }),
      );
    }

    if rust.code != tsc.code {
      return (
        TestOutcome::CodeMismatch,
        Some(MismatchDetail {
          message: format!(
            "code mismatch between {} and {}",
            describe(rust),
            describe(tsc)
          ),
          rust: Some(rust.clone()),
          tsc: Some(tsc.clone()),
        }),
      );
    }
  }

  if rust_sorted.len() > tsc_sorted.len() {
    let rust = rust_sorted.get(len).cloned();
    return (
      TestOutcome::RustExtraDiagnostics,
      Some(MismatchDetail {
        message: "rust produced extra diagnostics".to_string(),
        rust,
        tsc: None,
      }),
    );
  }

  if rust_sorted.len() < tsc_sorted.len() {
    let tsc = tsc_sorted.get(len).cloned();
    return (
      TestOutcome::RustMissingDiagnostics,
      Some(MismatchDetail {
        message: "rust missed diagnostics".to_string(),
        rust: None,
        tsc,
      }),
    );
  }

  (TestOutcome::Match, None)
}

fn summarize(results: &[TestResult]) -> Summary {
  let mut summary = Summary::default();
  summary.total = results.len();
  for result in results {
    summary.outcomes.increment(result.outcome);
  }
  summary
}

struct HarnessHost {
  files: HarnessFileSet,
}

impl HarnessHost {
  fn new(files: HarnessFileSet) -> Self {
    Self { files }
  }
}

impl Host for HarnessHost {
  fn file_text(&self, file: FileId) -> std::result::Result<Arc<str>, HostError> {
    let idx = file.0 as usize;
    self
      .files
      .files
      .get(idx)
      .map(|f| f.content.clone())
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    let is_relative = specifier.starts_with("./") || specifier.starts_with("../");
    if !is_relative {
      let normalized = normalize_name(specifier);
      return self.files.resolve(&normalized);
    }

    let base = self.files.file_name(from)?;
    let parent = Path::new(&base).parent().unwrap_or_else(|| Path::new(""));
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
      if let Some(found) = self.files.resolve(&cand) {
        return Some(found);
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

#[derive(Clone)]
struct TscRunner {
  node_path: PathBuf,
}

impl TscRunner {
  fn new(node_path: PathBuf) -> Self {
    Self { node_path }
  }

  fn available(&self) -> bool {
    #[cfg(feature = "with-node")]
    {
      std::process::Command::new(&self.node_path)
        .arg("--version")
        .output()
        .map(|out| out.status.success())
        .unwrap_or(false)
    }

    #[cfg(not(feature = "with-node"))]
    {
      false
    }
  }

  fn run(
    &self,
    files: &HarnessFileSet,
    options: &HarnessOptions,
  ) -> std::result::Result<Vec<TscDiagnostic>, String> {
    #[cfg(not(feature = "with-node"))]
    {
      let _ = (files, options);
      return Err("built without `with-node` feature".to_string());
    }

    #[cfg(feature = "with-node")]
    {
      let wrapper = wrapper_path();
      if !wrapper.exists() {
        return Err(format!("missing tsc wrapper at {}", wrapper.display()));
      }
      let temp_dir = tempfile::tempdir().map_err(|err| err.to_string())?;
      files
        .write_to_dir(temp_dir.path())
        .map_err(|err| err.to_string())?;
      let mut cmd = std::process::Command::new(&self.node_path);
      cmd.current_dir(temp_dir.path());
      cmd.arg(wrapper);
      if let Some(env) = options.to_env_json() {
        cmd.env("HARNESS_OPTIONS", env);
      }
      for file in files.iter() {
        cmd.arg(temp_dir.path().join(&file.normalized));
      }

      let output = cmd.output().map_err(|err| format!("spawn node: {err}"))?;

      if !output.status.success() {
        return Err(format!(
          "tsc wrapper exited with status {}: stdout={} stderr={}",
          output.status,
          String::from_utf8_lossy(&output.stdout),
          String::from_utf8_lossy(&output.stderr)
        ));
      }

      let parsed: TscDiagnostics = serde_json::from_slice(&output.stdout)
        .map_err(|err| format!("parse tsc JSON output: {err}"))?;

      Ok(parsed.diagnostics)
    }
  }
}

fn wrapper_path() -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("scripts")
    .join("tsc_wrapper.js")
}

#[derive(Clone)]
struct SnapshotStore {
  base: PathBuf,
}

impl SnapshotStore {
  fn new(root: &Path) -> Self {
    let suite_name = root
      .file_name()
      .map(|p| p.to_string_lossy().to_string())
      .unwrap_or_else(|| "conformance".to_string());
    let base = Path::new(env!("CARGO_MANIFEST_DIR"))
      .join("baselines")
      .join(suite_name);
    SnapshotStore { base }
  }

  fn has_any(&self) -> bool {
    WalkDir::new(&self.base)
      .into_iter()
      .filter_map(|e| e.ok())
      .any(|entry| entry.file_type().is_file())
  }

  fn path_for(&self, id: &str) -> PathBuf {
    let mut path = self.base.join(id);
    path.set_extension("json");
    path
  }

  fn load(&self, id: &str) -> std::io::Result<Vec<TscDiagnostic>> {
    let path = self.path_for(id);
    let data = std::fs::read_to_string(path)?;
    let parsed: TscDiagnostics = serde_json::from_str(&data)?;
    Ok(parsed.diagnostics)
  }

  fn save(&self, id: &str, diagnostics: &[TscDiagnostic]) -> std::io::Result<()> {
    let path = self.path_for(id);
    if let Some(parent) = path.parent() {
      std::fs::create_dir_all(parent)?;
    }

    let payload = TscDiagnostics {
      diagnostics: diagnostics.to_vec(),
    };
    let json = serde_json::to_string_pretty(&payload)?;
    std::fs::write(path, format!("{json}\n"))
  }
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
  fn diff_detects_extra_and_missing() {
    let rust = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Rust,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Rust("A".into())),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];
    let tsc = Vec::new();
    let (outcome, detail) = diff_diagnostics(&rust, &tsc, 0);
    assert_eq!(outcome, TestOutcome::RustExtraDiagnostics);
    assert!(detail.is_some());

    let (outcome, _) = diff_diagnostics(&tsc, &rust, 0);
    assert_eq!(outcome, TestOutcome::RustMissingDiagnostics);
  }

  #[test]
  fn host_deduplicates_virtual_files() {
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

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone());
    let roots = file_set.root_files();

    assert_eq!(roots.len(), 2);

    let from = *roots.last().unwrap();
    let a_id = host.resolve(from, "a.ts").expect("a.ts should resolve");
    assert!(roots.contains(&a_id));
    assert_eq!(&*host.file_text(a_id).unwrap(), "second version");
  }
}
