use crate::directives::{HarnessDirective, HarnessOptions};
use crate::discover::{discover_conformance_tests, load_conformance_test, Filter, Shard, TestCase, DEFAULT_EXTENSIONS};
use crate::multifile::normalize_name;
use crate::profile::ProfileBuilder;
use crate::{HarnessError, Result, VirtualFile};
use clap::ValueEnum;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::path::Path;
use std::path::PathBuf;
use std::sync::Arc;
use std::time::{Duration, Instant};
use tracing::{info, info_span, warn};
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{Diagnostic, FileId, Host, HostError, Program, Span, TextRange};

const HARNESS_SLEEP_ENV: &str = "HARNESS_SLEEP_MS_PER_TEST";

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ValueEnum)]
#[serde(rename_all = "snake_case")]
pub enum CompareMode {
  None,
  Tsc,
  Snapshot,
}

impl CompareMode {
  pub fn as_str(self) -> &'static str {
    match self {
      CompareMode::None => "none",
      CompareMode::Tsc => "tsc",
      CompareMode::Snapshot => "snapshot",
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Serialize, Deserialize, ValueEnum)]
#[serde(rename_all = "snake_case")]
pub enum Isolation {
  Process,
  None,
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum TestStatus {
  Passed,
  ParseError,
  BindError,
  TypeError,
  RustIce,
  InternalError,
  HarnessCrash,
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
  #[serde(default, skip_serializing_if = "String::is_empty")]
  pub stdout: String,
  #[serde(default, skip_serializing_if = "String::is_empty")]
  pub stderr: String,
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
  pub jobs: usize,
  pub isolate: Isolation,
  pub compare: CompareMode,
}

impl Default for ConformanceOptions {
  fn default() -> Self {
    Self {
      root: PathBuf::new(),
      filter: Filter::All,
      filter_pattern: None,
      shard: None,
      json: false,
      update_snapshots: false,
      timeout: Duration::from_secs(0),
      trace: false,
      profile: false,
      profile_out: PathBuf::from("profile.json"),
      extensions: DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect(),
      allow_empty: false,
      jobs: 1,
      isolate: Isolation::None,
      compare: CompareMode::None,
    }
  }
}

#[derive(Debug, Clone)]
pub struct SingleTestOptions {
  pub root: PathBuf,
  pub id: String,
  pub timeout: Duration,
  pub trace: bool,
  pub profile: bool,
  pub profile_out: PathBuf,
  pub compare: CompareMode,
}

pub fn run_conformance(opts: ConformanceOptions) -> Result<JsonReport> {
  let extensions = if opts.extensions.is_empty() {
    DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect()
  } else {
    opts.extensions.clone()
  };

  let run_start = Instant::now();
  let mut profiler = opts.profile.then(|| ProfileBuilder::new(&opts));

  let mut cases = {
    let span = info_span!("discover_tests", root = %opts.root.display());
    let _enter = span.enter();
    info!(phase = "discover_start", root = %opts.root.display());
    let discovered = discover_conformance_tests(&opts.root, &opts.filter, &extensions)?;
    info!(phase = "discover_complete", count = discovered.len());
    discovered
  };

  if cases.is_empty() && !opts.allow_empty {
    return Err(HarnessError::EmptySuite {
      root: opts.root.display().to_string(),
      extensions: extensions.join(","),
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

  results.sort_by(|a, b| a.id.cmp(&b.id));
  Ok(JsonReport { summary, results })
}

<<<<<<< HEAD
pub fn run_single_conformance(opts: SingleTestOptions) -> Result<TestResult> {
  let case = load_conformance_test(&opts.root, &opts.id)?;
  let mut result = run_single_case(case, opts.timeout);
  if !opts.timeout.is_zero() && result.duration_ms > opts.timeout.as_millis() {
    result.status = TestStatus::Timeout;
=======
fn run_process_isolated(
  cases: Vec<TestCase>,
  opts: &ConformanceOptions,
) -> Result<Vec<TestResult>> {
  let jobs = opts.jobs.max(1);
  let timeout = if opts.timeout.is_zero() {
    Duration::MAX
  } else {
    opts.timeout
  };

  let mut pending: VecDeque<TestCase> = cases.into_iter().collect();
  let mut active: Vec<RunningChild> = Vec::new();
  let mut results = Vec::new();
  let exe = std::env::current_exe()?;

  while !pending.is_empty() || !active.is_empty() {
    while active.len() < jobs {
      if let Some(case) = pending.pop_front() {
        let child = spawn_child(&case, opts, &exe)?;
        active.push(child);
      } else {
        break;
      }
    }

    let mut idx = 0;
    let mut made_progress = false;
    while idx < active.len() {
      let elapsed = active[idx].started.elapsed();
      let child_finished = active[idx].child.try_wait()?.is_some();
      let timed_out = elapsed >= timeout;

      if timed_out {
        let mut finished = active.swap_remove(idx);
        let _ = finished.child.kill();
        let output = finished.child.wait_with_output()?;
        results.push(timeout_result(&finished.case, timeout, output));
        made_progress = true;
      } else if child_finished {
        let finished = active.swap_remove(idx);
        let elapsed_ms = elapsed.as_millis();
        let output = finished.child.wait_with_output()?;
        results.push(parse_child_output(&finished.case, output, elapsed_ms));
        made_progress = true;
      } else {
        idx += 1;
      }
    }

    if !made_progress {
      std::thread::sleep(Duration::from_millis(10));
    }
  }

  Ok(results)
}

struct RunningChild {
  case: TestCase,
  child: std::process::Child,
  started: Instant,
}

fn spawn_child(case: &TestCase, opts: &ConformanceOptions, exe: &Path) -> Result<RunningChild> {
  let mut cmd = Command::new(exe);
  cmd
    .arg("conformance")
    .arg("--single")
    .arg(&case.id)
    .arg("--root")
    .arg(&opts.root)
    .arg("--compare")
    .arg(opts.compare.as_str())
    .arg("--timeout-secs")
    .arg(opts.timeout.as_secs().to_string());

  if opts.trace {
    cmd.arg("--trace");
  }
  if opts.profile {
    cmd.arg("--profile");
  }
  if opts.update_snapshots {
    cmd.arg("--update-snapshots");
  }

  cmd
    .stdout(Stdio::piped())
    .stderr(Stdio::piped())
    .stdin(Stdio::null());

  let child = cmd.spawn()?;
  Ok(RunningChild {
    case: case.clone(),
    child,
    started: Instant::now(),
  })
}

fn parse_child_output(case: &TestCase, output: Output, elapsed_ms: u128) -> TestResult {
  let stdout = String::from_utf8_lossy(&output.stdout).to_string();
  let stderr = String::from_utf8_lossy(&output.stderr).to_string();

  if output.status.success() {
    if let Ok(mut result) = serde_json::from_str::<TestResult>(stdout.trim()) {
      if result.id != case.id {
        let mut notes = result.notes;
        notes.push(format!(
          "child returned result for unexpected case {}; expected {}",
          result.id, case.id
        ));
        return TestResult {
          id: case.id.clone(),
          path: case.path.display().to_string(),
          status: TestStatus::HarnessCrash,
          duration_ms: elapsed_ms,
          diagnostics: Vec::new(),
          notes,
          stdout,
          stderr,
        };
      }

      if result.stderr.is_empty() {
        result.stderr = stderr;
      }
      if result.stdout.is_empty() && !stdout.trim().is_empty() {
        result.stdout = stdout;
      }
      return result;
    }
  }

  harness_crash_result(case, elapsed_ms, stdout, stderr)
}

fn timeout_result(case: &TestCase, timeout: Duration, output: Output) -> TestResult {
  TestResult {
    id: case.id.clone(),
    path: case.path.display().to_string(),
    status: TestStatus::Timeout,
    duration_ms: timeout.as_millis(),
    diagnostics: Vec::new(),
    notes: case.notes.clone(),
    stdout: String::from_utf8_lossy(&output.stdout).to_string(),
    stderr: String::from_utf8_lossy(&output.stderr).to_string(),
  }
}

fn harness_crash_result(
  case: &TestCase,
  elapsed_ms: u128,
  stdout: String,
  stderr: String,
) -> TestResult {
  let mut notes = case.notes.clone();
  notes.push("harness crash: child process exited without a result".to_string());

  TestResult {
    id: case.id.clone(),
    path: case.path.display().to_string(),
    status: TestStatus::HarnessCrash,
    duration_ms: elapsed_ms,
    diagnostics: Vec::new(),
    notes,
    stdout,
    stderr,
>>>>>>> 407bb94 (Treat elapsed timeouts before parsing child output)
  }
  Ok(result)
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
        stdout: String::new(),
        stderr: String::new(),
      }
    }
  }
}

fn execute_case(case: TestCase) -> TestResult {
  let start = Instant::now();
  if let Some(delay) = harness_sleep_for_case(&case.id) {
    std::thread::sleep(delay);
  }
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
        stdout: String::new(),
        stderr: String::new(),
      }
    }
    Err(_) => {
      warn!(phase = "ice", duration_ms = duration_ms);
      TestResult {
        id: case.id,
        path: case.path.display().to_string(),
        status: TestStatus::RustIce,
        duration_ms,
        diagnostics: vec![Diagnostic::error(
          "ICE0001",
          "typechecker panicked",
          Span::new(FileId(0), TextRange::new(0, 0)),
        )],
        notes,
        directives,
        options,
        stdout: String::new(),
        stderr: String::new(),
      }
    }
  }
}

fn harness_sleep_for_case(id: &str) -> Option<Duration> {
  let raw = std::env::var(HARNESS_SLEEP_ENV).ok()?;
  if raw.is_empty() {
    return None;
  }

  if let Ok(ms) = raw.parse::<u64>() {
    return Some(Duration::from_millis(ms));
  }

  for part in raw.split(',') {
    if let Some((pattern, ms_raw)) = part.split_once('=') {
      if id.contains(pattern.trim()) {
        if let Ok(ms) = ms_raw.trim().parse::<u64>() {
          return Some(Duration::from_millis(ms));
        }
      }
    }
  }

  None
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

  if has_code_prefix("PS") || has_code_prefix("PARSE") {
    return TestStatus::ParseError;
  }

  if has_code_prefix("BIND") {
    return TestStatus::BindError;
  }

  if has_code_prefix("HOST") {
    return TestStatus::InternalError;
  }

  if has_code_prefix("ICE") {
    return TestStatus::RustIce;
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

  fn file_names(&self) -> Vec<String> {
    self.files.iter().map(|f| f.normalized.clone()).collect()
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
    for ext in ["index.ts", "index.tsx", "index.d.ts", "index.js", "index.jsx"] {
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

  fn file_kind(&self, file: FileId) -> FileKind {
    let name = self
      .files
      .get(file.0 as usize)
      .map(|f| f.normalized.as_str())
      .unwrap_or("");
    if name.ends_with(".d.ts") {
      FileKind::Dts
    } else if name.ends_with(".tsx") {
      FileKind::Tsx
    } else if name.ends_with(".ts") {
      FileKind::Ts
    } else if name.ends_with(".jsx") {
      FileKind::Jsx
    } else {
      FileKind::Js
    }
  }
}

pub(crate) fn run_rust(files: &[VirtualFile]) -> (Vec<Diagnostic>, Vec<String>) {
  let host = HarnessHost::new(files);
  let names = host.file_names();
  let roots = host.root_files();
  let diagnostics = Program::new(host, roots).check();
  (diagnostics, names)
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
