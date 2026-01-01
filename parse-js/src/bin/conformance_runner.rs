// TypeScript Conformance Test Runner
// Runs all TypeScript conformance tests in parallel with timeouts

use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{
  diagnostic_from_syntax_error, sort_diagnostics, sort_labels, Diagnostic, FileId, Span, TextRange,
};
use parse_js;
use parse_js::error::SyntaxErrorType;
use parse_js::lex::{lex_next, LexMode, Lexer};
use parse_js::{parse_with_options_cancellable, Dialect, ParseOptions, SourceType};
use rayon::prelude::*;
use serde::Serialize;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::env;
use std::fs;
use std::io::{BufWriter, Write};
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

#[derive(Debug, Clone, Serialize)]
struct HarnessDirective {
  name: String,
  value: Option<String>,
}

#[derive(Debug, Clone, Serialize, PartialEq, Eq)]
enum FileKind {
  TypeScript,
  Tsx,
  JavaScript,
  Jsx,
  Other,
}

#[derive(Debug, Clone)]
struct VirtualFile {
  name: String,
  content: String,
  directives: Vec<HarnessDirective>,
  module: bool,
  kind: FileKind,
}

#[derive(Debug, Clone)]
struct VirtualFileResult {
  file_id: FileId,
  name: String,
  module: bool,
  kind: FileKind,
  directives: Vec<HarnessDirective>,
  skipped: bool,
  diagnostics: Vec<Diagnostic>,
}

#[derive(Debug, Clone)]
struct TestResult {
  path: PathBuf,
  directives: Vec<HarnessDirective>,
  files: Vec<VirtualFileResult>,
  duration: Duration,
  duration_ms: u128,
  diagnostics: Vec<Diagnostic>,
  timed_out: bool,
  files_store: SimpleFiles,
}

impl TestResult {
  fn passed(&self) -> bool {
    !self.timed_out
      && self.diagnostics.is_empty()
      && self.files.iter().all(|f| f.diagnostics.is_empty())
  }

  fn failed_files(&self) -> Vec<&VirtualFileResult> {
    self
      .files
      .iter()
      .filter(|f| !f.diagnostics.is_empty())
      .collect::<Vec<_>>()
  }
}

#[derive(Debug, Clone, Default)]
struct RunnerOptions {
  filter: Option<String>,
  failures_path: Option<PathBuf>,
  json_output: Option<PathBuf>,
  timeout_secs: u64,
}

#[derive(Debug, Clone)]
struct SimpleFile {
  name: String,
  text: String,
}

#[derive(Debug, Clone, Default)]
struct SimpleFiles {
  files: Vec<SimpleFile>,
  ids: BTreeMap<String, FileId>,
}

impl SimpleFiles {
  fn insert(&mut self, name: String, text: String) -> FileId {
    let normalized = normalize_virtual_path(&name);
    if let Some(id) = self.ids.get(&normalized) {
      if let Some(file) = self.files.get_mut(id.0 as usize) {
        file.text = text;
      }
      return *id;
    }
    let id = FileId(self.files.len() as u32);
    self.files.push(SimpleFile {
      name: normalized.clone(),
      text,
    });
    self.ids.insert(normalized, id);
    id
  }

  fn iter(&self) -> impl Iterator<Item = (FileId, &SimpleFile)> {
    self
      .files
      .iter()
      .enumerate()
      .map(|(idx, file)| (FileId(idx as u32), file))
  }
}

impl SourceProvider for SimpleFiles {
  fn file_name(&self, file: FileId) -> Option<&str> {
    self
      .files
      .get(file.0 as usize)
      .map(|file| file.name.as_str())
  }

  fn file_text(&self, file: FileId) -> Option<&str> {
    self
      .files
      .get(file.0 as usize)
      .map(|file| file.text.as_str())
  }
}

fn empty_test_result(path: &Path) -> TestResult {
  TestResult {
    path: path.to_path_buf(),
    directives: Vec::new(),
    files: Vec::new(),
    duration: Duration::from_millis(0),
    duration_ms: 0,
    diagnostics: Vec::new(),
    timed_out: false,
    files_store: SimpleFiles::default(),
  }
}

fn normalize_path(path: &Path) -> String {
  path.to_string_lossy().replace('\\', "/")
}

fn normalize_virtual_path(path: &str) -> String {
  path.replace('\\', "/")
}

fn parse_directive(line: &str) -> Option<HarnessDirective> {
  let trimmed = line.trim_start();
  if !trimmed.starts_with("//") {
    return None;
  }

  let directive = trimmed.trim_start_matches('/').trim_start();
  if !directive.starts_with('@') {
    return None;
  }

  let mut parts = directive[1..].splitn(2, ':');
  let name = parts.next()?.trim();
  let value = parts.next().map(|v| v.trim().to_string());
  Some(HarnessDirective {
    name: name.to_ascii_lowercase(),
    value,
  })
}

fn has_module_directive(directives: &[HarnessDirective]) -> Option<bool> {
  directives
    .iter()
    .rev()
    .find(|d| d.name == "module")
    .map(|d| match d.value.as_deref() {
      Some(v) if v.eq_ignore_ascii_case("none") => false,
      _ => true,
    })
}

fn contains_import_export(content: &str, cancel: &Arc<AtomicBool>) -> Option<bool> {
  let mut lexer = Lexer::new(content);
  loop {
    if cancel.load(AtomicOrdering::Relaxed) {
      return None;
    }
    let token = lex_next(&mut lexer, LexMode::Standard, Dialect::Tsx);
    match token.typ {
      parse_js::token::TT::KeywordImport | parse_js::token::TT::KeywordExport => return Some(true),
      parse_js::token::TT::EOF => return Some(false),
      _ => {}
    }
  }
}

fn detect_file_kind(name: &str) -> FileKind {
  let ext = Path::new(name)
    .extension()
    .and_then(|e| e.to_str())
    .unwrap_or("")
    .to_ascii_lowercase();
  match ext.as_str() {
    "ts" | "mts" | "cts" => FileKind::TypeScript,
    "tsx" | "mtsx" | "ctsx" => FileKind::Tsx,
    "js" | "mjs" | "cjs" => FileKind::JavaScript,
    "jsx" => FileKind::Jsx,
    _ => FileKind::Other,
  }
}

fn should_parse(kind: &FileKind) -> bool {
  matches!(
    kind,
    FileKind::TypeScript | FileKind::Tsx | FileKind::JavaScript | FileKind::Jsx
  )
}

fn split_virtual_files(
  path: &Path,
  source: &str,
  cancel: &Arc<AtomicBool>,
) -> Option<(Vec<VirtualFile>, Vec<HarnessDirective>)> {
  let mut global_directives: Vec<HarnessDirective> = Vec::new();
  let mut files: Vec<VirtualFile> = Vec::new();

  let mut current_name: Option<String> = None;
  let mut current_content: Vec<String> = Vec::new();

  for line in source.lines() {
    if cancel.load(AtomicOrdering::Relaxed) {
      return None;
    }
    if let Some(directive) = parse_directive(line) {
      // Capture all directives for debugging purposes
      global_directives.push(directive.clone());

      if directive.name.eq_ignore_ascii_case("filename") {
        if current_name.is_some() || !current_content.is_empty() {
          let name = current_name
            .clone()
            .unwrap_or_else(|| path.file_name().unwrap().to_string_lossy().to_string());
          let content = current_content.join("\n");
          let kind = detect_file_kind(&name);
          let module_directive = has_module_directive(&global_directives).unwrap_or(false);
          let module = module_directive || contains_import_export(&content, cancel)?;
          files.push(VirtualFile {
            name,
            content,
            directives: global_directives.clone(),
            module,
            kind,
          });
          current_content.clear();
        }
        current_name = directive.value.clone();
        continue;
      }
    }

    current_content.push(line.to_string());
  }

  let final_name =
    current_name.unwrap_or_else(|| path.file_name().unwrap().to_string_lossy().to_string());
  let content = current_content.join("\n");
  if cancel.load(AtomicOrdering::Relaxed) {
    return None;
  }
  let kind = detect_file_kind(&final_name);
  let module_directive = has_module_directive(&global_directives).unwrap_or(false);
  let module = module_directive || contains_import_export(&content, cancel)?;
  files.push(VirtualFile {
    name: final_name,
    content,
    directives: global_directives.clone(),
    module,
    kind,
  });

  Some((files, global_directives))
}

fn discover_tests(dir: &Path) -> Vec<PathBuf> {
  let mut tests = Vec::new();
  if let Ok(entries) = fs::read_dir(dir) {
    let mut entries: Vec<_> = entries.flatten().collect();
    entries.sort_by_key(|e| e.path());

    for entry in entries {
      let path = entry.path();
      if path.is_dir() {
        tests.extend(discover_tests(&path));
      } else if let Some(ext) = path.extension() {
        if ext == "ts" || ext == "tsx" {
          tests.push(path);
        }
      }
    }
  }
  tests
}

fn load_failure_paths(path: &Path) -> HashSet<String> {
  let Ok(report) = fs::read_to_string(path) else {
    return HashSet::new();
  };
  report
    .lines()
    .filter_map(|line| line.strip_prefix("File: "))
    .map(|p| p.trim().replace('\\', "/"))
    .collect()
}

fn run_test(path: &Path, cancel: &Arc<AtomicBool>, timeout_secs: u64) -> TestResult {
  let start = Instant::now();
  if cancel.load(AtomicOrdering::Relaxed) {
    return timeout_test_result(path, timeout_secs);
  }
  let mut base_result = empty_test_result(path);

  let source = match fs::read_to_string(path) {
    Ok(s) => s,
    Err(e) => {
      let file_id = base_result
        .files_store
        .insert(normalize_path(path), String::new());
      base_result.diagnostics.push(Diagnostic::error(
        "CONF0001",
        format!("failed to read file: {}", e),
        Span {
          file: file_id,
          range: TextRange::new(0, 0),
        },
      ));
      sort_diagnostics(&mut base_result.diagnostics);
      base_result.duration = start.elapsed();
      base_result.duration_ms = base_result.duration.as_millis();
      return base_result;
    }
  };

  if cancel.load(AtomicOrdering::Relaxed) {
    return timeout_test_result(path, timeout_secs);
  }

  let Some((mut virtual_files, directives)) = split_virtual_files(path, &source, cancel) else {
    return timeout_test_result(path, timeout_secs);
  };
  base_result.directives = directives;
  virtual_files
    .sort_by(|a, b| normalize_virtual_path(&a.name).cmp(&normalize_virtual_path(&b.name)));

  for vf in virtual_files {
    if cancel.load(AtomicOrdering::Relaxed) {
      return timeout_test_result(path, timeout_secs);
    }
    let should_parse = should_parse(&vf.kind);
    let normalized_name = normalize_virtual_path(&vf.name);
    let file_id = base_result
      .files_store
      .insert(normalized_name.clone(), vf.content.clone());
    let mut diagnostics = Vec::new();

    if should_parse {
      let dialect = match vf.kind {
        FileKind::TypeScript => Dialect::Ts,
        FileKind::Tsx => Dialect::Tsx,
        FileKind::JavaScript => Dialect::Js,
        FileKind::Jsx => Dialect::Jsx,
        FileKind::Other => Dialect::Ts,
      };
      let opts = ParseOptions {
        dialect,
        source_type: if vf.module {
          SourceType::Module
        } else {
          SourceType::Script
        },
      };

      if let Err(err) = parse_with_options_cancellable(&vf.content, opts, Arc::clone(cancel)) {
        if err.typ == SyntaxErrorType::Cancelled {
          return timeout_test_result(path, timeout_secs);
        }
        diagnostics.push(diagnostic_from_syntax_error(file_id, &err));
      }
    }

    sort_diagnostics(&mut diagnostics);

    base_result.files.push(VirtualFileResult {
      file_id,
      name: normalized_name,
      module: vf.module,
      kind: vf.kind,
      directives: vf.directives.clone(),
      skipped: !should_parse,
      diagnostics,
    });
  }

  if base_result.passed() {
    for file in &mut base_result.files_store.files {
      file.text.clear();
    }
  }

  base_result.duration = start.elapsed();
  base_result.duration_ms = base_result.duration.as_millis();
  base_result
}

struct TimeoutManager {
  inner: Arc<TimeoutManagerInner>,
  next_id: AtomicUsize,
  thread: Mutex<Option<std::thread::JoinHandle<()>>>,
}

struct TimeoutManagerInner {
  state: Mutex<TimeoutManagerState>,
  cv: Condvar,
}

struct TimeoutManagerState {
  active: HashMap<usize, TimeoutEntry>,
  shutdown: bool,
}

struct TimeoutEntry {
  deadline: Instant,
  cancel: Arc<AtomicBool>,
  cancelled: bool,
}

struct TimeoutGuard {
  id: usize,
  inner: Arc<TimeoutManagerInner>,
}

impl TimeoutManager {
  fn new() -> Self {
    let inner = Arc::new(TimeoutManagerInner {
      state: Mutex::new(TimeoutManagerState {
        active: HashMap::new(),
        shutdown: false,
      }),
      cv: Condvar::new(),
    });
    let thread_inner = Arc::clone(&inner);
    let handle = std::thread::spawn(move || timeout_thread(thread_inner));
    Self {
      inner,
      next_id: AtomicUsize::new(1),
      thread: Mutex::new(Some(handle)),
    }
  }

  fn register(&self, deadline: Instant, cancel: Arc<AtomicBool>) -> TimeoutGuard {
    let id = self.next_id.fetch_add(1, AtomicOrdering::Relaxed);
    let mut state = self.inner.state.lock().unwrap();
    state.active.insert(
      id,
      TimeoutEntry {
        deadline,
        cancel,
        cancelled: false,
      },
    );
    self.inner.cv.notify_one();
    TimeoutGuard {
      id,
      inner: Arc::clone(&self.inner),
    }
  }
}

impl Drop for TimeoutManager {
  fn drop(&mut self) {
    {
      let mut state = self.inner.state.lock().unwrap();
      state.shutdown = true;
      self.inner.cv.notify_one();
    }

    if let Some(handle) = self.thread.lock().unwrap().take() {
      let _ = handle.join();
    }
  }
}

impl Drop for TimeoutGuard {
  fn drop(&mut self) {
    let mut state = self.inner.state.lock().unwrap();
    state.active.remove(&self.id);
    self.inner.cv.notify_one();
  }
}

fn timeout_thread(inner: Arc<TimeoutManagerInner>) {
  let mut guard = inner.state.lock().unwrap();
  loop {
    if guard.shutdown {
      return;
    }

    let now = Instant::now();
    let mut next_deadline: Option<Instant> = None;

    for entry in guard.active.values_mut() {
      if entry.cancelled {
        continue;
      }
      if now >= entry.deadline {
        entry.cancelled = true;
        entry.cancel.store(true, AtomicOrdering::Relaxed);
        continue;
      }

      next_deadline = match next_deadline {
        Some(existing) => Some(existing.min(entry.deadline)),
        None => Some(entry.deadline),
      };
    }

    if let Some(deadline) = next_deadline {
      let wait_for = deadline
        .checked_duration_since(now)
        .unwrap_or_else(|| Duration::from_millis(0));
      let (new_guard, _) = inner.cv.wait_timeout(guard, wait_for).unwrap();
      guard = new_guard;
    } else {
      guard = inner.cv.wait(guard).unwrap();
    }
  }
}

fn timeout_test_result(path: &Path, timeout_secs: u64) -> TestResult {
  let mut result = empty_test_result(path);
  let file_id = result
    .files_store
    .insert(normalize_path(path), String::new());
  result.diagnostics.push(Diagnostic::error(
    "CONF0003",
    format!("timeout after {} seconds", timeout_secs),
    Span {
      file: file_id,
      range: TextRange::new(0, 0),
    },
  ));
  sort_diagnostics(&mut result.diagnostics);
  result.duration = Duration::from_secs(timeout_secs);
  result.duration_ms = result.duration.as_millis();
  result.timed_out = true;
  result
}

fn run_test_with_timeout(path: &Path, timeout_secs: u64, timeouts: &TimeoutManager) -> TestResult {
  let start = Instant::now();
  let cancel = Arc::new(AtomicBool::new(false));
  let deadline = start + Duration::from_secs(timeout_secs);
  let _guard = timeouts.register(deadline, Arc::clone(&cancel));
  let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
    run_test(path, &cancel, timeout_secs)
  }));

  match result {
    Ok(mut result) => {
      if result.timed_out {
        result.duration = Duration::from_secs(timeout_secs);
      } else {
        result.duration = start.elapsed();
      }
      result.duration_ms = result.duration.as_millis();
      result
    }
    Err(panic_err) => {
      let mut result = empty_test_result(path);
      let file_id = result
        .files_store
        .insert(normalize_path(path), String::new());
      result.diagnostics.push(Diagnostic::error(
        "CONF0002",
        format!("runner panicked: {:?}", panic_err),
        Span {
          file: file_id,
          range: TextRange::new(0, 0),
        },
      ));
      sort_diagnostics(&mut result.diagnostics);
      result.duration = start.elapsed();
      result.duration_ms = result.duration.as_millis();
      result
    }
  }
}

fn parse_args() -> RunnerOptions {
  let mut options = RunnerOptions {
    timeout_secs: 10,
    ..RunnerOptions::default()
  };

  let args: Vec<String> = env::args().skip(1).collect();
  let mut i = 0;
  while i < args.len() {
    match args[i].as_str() {
      "--filter" => {
        if let Some(next) = args.get(i + 1) {
          options.filter = Some(next.clone());
          i += 1;
        }
      }
      "--failures" | "--from-report" => {
        if let Some(next) = args.get(i + 1) {
          if !next.starts_with('-') {
            options.failures_path = Some(PathBuf::from(next));
            i += 1;
          }
        }
        if options.failures_path.is_none() {
          options.failures_path = Some(PathBuf::from("typescript_conformance_failures.txt"));
        }
      }
      "--json" => {
        if let Some(next) = args.get(i + 1) {
          options.json_output = Some(PathBuf::from(next));
          i += 1;
        }
      }
      "--timeout" => {
        if let Some(next) = args.get(i + 1) {
          if let Ok(v) = next.parse::<u64>() {
            options.timeout_secs = v;
          }
          i += 1;
        }
      }
      other => {
        eprintln!("Unknown argument: {}", other);
      }
    }
    i += 1;
  }

  options
}

fn rendered_diagnostics(provider: &SimpleFiles, diagnostics: &[Diagnostic]) -> Vec<String> {
  diagnostics
    .iter()
    .map(|diag| render_diagnostic(provider, diag))
    .collect()
}

fn print_rendered_diagnostics(prefix: &str, provider: &SimpleFiles, diagnostics: &[Diagnostic]) {
  for rendered in rendered_diagnostics(provider, diagnostics) {
    for line in rendered.lines() {
      println!("{}{}", prefix, line);
    }
  }
}

fn append_rendered_diagnostics(
  output: &mut String,
  indent: &str,
  provider: &SimpleFiles,
  diagnostics: &[Diagnostic],
) {
  for rendered in rendered_diagnostics(provider, diagnostics) {
    for line in rendered.lines() {
      output.push_str(indent);
      output.push_str(line);
      output.push('\n');
    }
  }
}

#[derive(Serialize)]
struct SerializableSpan {
  file: u32,
  start: u32,
  end: u32,
}

#[derive(Serialize)]
struct SerializableLabel {
  span: SerializableSpan,
  message: String,
  is_primary: bool,
}

#[derive(Serialize)]
struct SerializableDiagnostic {
  code: String,
  severity: String,
  message: String,
  primary: SerializableSpan,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  labels: Vec<SerializableLabel>,
  #[serde(skip_serializing_if = "Vec::is_empty")]
  notes: Vec<String>,
}

#[derive(Serialize)]
struct SerializableVirtualFile {
  file_id: u32,
  name: String,
  module: bool,
  kind: FileKind,
  directives: Vec<HarnessDirective>,
  skipped: bool,
  diagnostics: Vec<SerializableDiagnostic>,
}

#[derive(Serialize)]
struct SerializableTestResult {
  path: String,
  directives: Vec<HarnessDirective>,
  files: Vec<SerializableVirtualFile>,
  duration_ms: u128,
  diagnostics: Vec<SerializableDiagnostic>,
  timed_out: bool,
}

fn serialize_results(results: &[TestResult]) -> Vec<SerializableTestResult> {
  results.iter().map(serialize_test_result).collect()
}

fn serialize_test_result(result: &TestResult) -> SerializableTestResult {
  let mut file_lookup = BTreeMap::new();
  for file in &result.files {
    file_lookup.insert(file.file_id, file);
  }

  let mut files: Vec<SerializableVirtualFile> = result
    .files_store
    .iter()
    .map(|(file_id, file)| {
      if let Some(vf) = file_lookup.get(&file_id) {
        SerializableVirtualFile {
          file_id: file_id.0,
          name: file.name.clone(),
          module: vf.module,
          kind: vf.kind.clone(),
          directives: vf.directives.clone(),
          skipped: vf.skipped,
          diagnostics: serialize_diagnostics(&vf.diagnostics),
        }
      } else {
        SerializableVirtualFile {
          file_id: file_id.0,
          name: file.name.clone(),
          module: false,
          kind: FileKind::Other,
          directives: Vec::new(),
          skipped: true,
          diagnostics: Vec::new(),
        }
      }
    })
    .collect();

  files.sort_by(|a, b| a.name.cmp(&b.name));

  SerializableTestResult {
    path: normalize_path(result.path.as_path()),
    directives: result.directives.clone(),
    files,
    duration_ms: result.duration_ms,
    diagnostics: serialize_diagnostics(&result.diagnostics),
    timed_out: result.timed_out,
  }
}

fn serialize_diagnostics(diagnostics: &[Diagnostic]) -> Vec<SerializableDiagnostic> {
  let mut sorted = diagnostics.to_vec();
  sort_diagnostics(&mut sorted);

  sorted
    .into_iter()
    .map(|diag| {
      let mut labels = diag.labels;
      sort_labels(&mut labels);
      let mut notes = diag.notes;
      notes.sort();
      SerializableDiagnostic {
        code: diag.code.to_string(),
        severity: diag.severity.as_str().to_string(),
        message: diag.message,
        primary: SerializableSpan {
          file: diag.primary.file.0,
          start: diag.primary.range.start,
          end: diag.primary.range.end,
        },
        labels: labels
          .into_iter()
          .map(|label| SerializableLabel {
            span: SerializableSpan {
              file: label.span.file.0,
              start: label.span.range.start,
              end: label.span.range.end,
            },
            message: label.message,
            is_primary: label.is_primary,
          })
          .collect(),
        notes,
      }
    })
    .collect()
}

fn main() {
  let options = parse_args();
  let test_dir =
    PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("tests/TypeScript/tests/cases/conformance");

  if !test_dir.is_dir() {
    eprintln!(
      "TypeScript conformance suite not found at {}.\n\n\
If you are running from the workspace root:\n  git submodule update --init --recursive --depth=1 parse-js/tests/TypeScript\n\n\
If you are running from the parse-js crate directory:\n  git submodule update --init --recursive --depth=1 tests/TypeScript\n",
      test_dir.display()
    );
    std::process::exit(1);
  }

  println!("🔍 Discovering TypeScript conformance tests...");
  let mut tests = discover_tests(test_dir.as_path());
  tests.sort();

  if tests.is_empty() {
    eprintln!(
      "No TypeScript conformance tests discovered under {}.\n\
Ensure the TypeScript submodule is checked out:\n  git submodule update --init --recursive --depth=1 parse-js/tests/TypeScript\n",
      test_dir.display()
    );
    std::process::exit(1);
  }

  if let Some(filter) = &options.filter {
    tests.retain(|path| normalize_path(path).contains(filter));
  }

  if let Some(report_path) = &options.failures_path {
    let failing = load_failure_paths(report_path);
    if !failing.is_empty() {
      tests.retain(|path| failing.contains(&normalize_path(path)));
    }
  }

  tests.sort();
  println!("📊 Running {} test files\n", tests.len());

  let passed = Arc::new(AtomicUsize::new(0));
  let failed = Arc::new(AtomicUsize::new(0));
  let processed = Arc::new(AtomicUsize::new(0));
  let total = tests.len();
  let timeout_manager = Arc::new(TimeoutManager::new());

  let processed_clone = Arc::clone(&processed);
  let progress_handle = std::thread::spawn(move || loop {
    std::thread::sleep(Duration::from_secs(5));
    let current = processed_clone.load(AtomicOrdering::Relaxed);
    if current >= total {
      break;
    }
    eprintln!(
      "Progress: {}/{} ({:.1}%)",
      current,
      total,
      (current as f64 / total as f64) * 100.0
    );
  });

  let results: Vec<TestResult> = tests
    .par_iter()
    .map(|test_path| {
      let result = run_test_with_timeout(test_path, options.timeout_secs, timeout_manager.as_ref());

      let current = processed.fetch_add(1, AtomicOrdering::Relaxed) + 1;
      if current % 100 == 0 {
        eprintln!("[{}/{}] {}", current, total, test_path.display());
      }

      if result.passed() {
        passed.fetch_add(1, AtomicOrdering::Relaxed);
      } else {
        failed.fetch_add(1, AtomicOrdering::Relaxed);
        if result.timed_out {
          eprintln!("⏱️  TIMEOUT: {}", test_path.display());
        }
      }

      result
    })
    .collect();

  progress_handle.join().ok();

  let mut results = results;
  results.sort_by(|a, b| a.path.cmp(&b.path));

  let passed_count = passed.load(AtomicOrdering::Relaxed);
  let failed_count = failed.load(AtomicOrdering::Relaxed);
  let pass_rate = if total == 0 {
    100.0
  } else {
    (passed_count as f64 / total as f64) * 100.0
  };

  let mut failures_by_category: BTreeMap<String, usize> = BTreeMap::new();
  for result in &results {
    if !result.passed() {
      if let Some(parent) = result.path.parent() {
        let category = parent
          .strip_prefix(test_dir.as_path())
          .unwrap_or(parent)
          .to_string_lossy()
          .to_string();
        failures_by_category
          .entry(category)
          .and_modify(|count| *count += 1)
          .or_insert(1);
      }
    }
  }

  let separator = "=".repeat(80);
  println!("\n{}", separator);
  println!("📈 TEST RESULTS SUMMARY");
  println!("{}", separator);
  println!("Total tests:  {}", total);
  println!("✅ Passed:     {} ({:.2}%)", passed_count, pass_rate);
  println!(
    "❌ Failed:     {} ({:.2}%)",
    failed_count,
    100.0 - pass_rate
  );
  println!("{}", separator);

  let timeout_count = results.iter().filter(|r| r.timed_out).count();
  if timeout_count > 0 {
    println!("⏱️  Timeouts:   {}", timeout_count);
  }

  if !failures_by_category.is_empty() {
    println!("\n📋 FAILURES BY CATEGORY:");
    println!("{}", separator);

    let mut categories: Vec<_> = failures_by_category.iter().collect();
    categories.sort_by(|(a_cat, a), (b_cat, b)| b.cmp(a).then_with(|| a_cat.cmp(b_cat)));

    for (category, failures) in categories.iter().take(20) {
      println!("{}: {} failures", category, failures);
    }

    println!("\n🔍 SAMPLE FAILURES (first 50):");
    println!("{}", separator);

    let failed_results: Vec<_> = results.iter().filter(|r| !r.passed()).take(50).collect();
    for (idx, result) in failed_results.iter().enumerate() {
      println!(
        "\n{}. {} ({:?})",
        idx + 1,
        result.path.display(),
        result.duration
      );
      if !result.diagnostics.is_empty() {
        print_rendered_diagnostics("   ", &result.files_store, &result.diagnostics);
      }
      for file in result.failed_files() {
        println!("   File: {}", file.name);
        print_rendered_diagnostics("     ", &result.files_store, &file.diagnostics);
      }
    }
  }

  if let Some(json_path) = options.json_output.as_ref() {
    let serializable = serialize_results(&results);
    match fs::File::create(json_path) {
      Ok(file) => {
        let mut writer = BufWriter::new(file);
        let result = serde_json::to_writer_pretty(&mut writer, &serializable)
          .and_then(|()| writer.write_all(b"\n").map_err(serde_json::Error::io))
          .and_then(|()| writer.flush().map_err(serde_json::Error::io));
        if let Err(err) = result {
          eprintln!("Failed to write JSON output: {}", err);
        } else {
          println!("🧾 JSON results written to {}", json_path.display());
        }
      }
      Err(err) => {
        eprintln!("Failed to write JSON output: {}", err);
      }
    }
  }

  if failed_count > 0 {
    let report_path = "typescript_conformance_failures.txt";
    let mut report = String::new();
    report.push_str("TypeScript Conformance Test Failures Report\n\n");
    report.push_str(&format!(
      "Total: {}, Passed: {}, Failed: {}\n",
      total, passed_count, failed_count
    ));
    report.push_str(&format!("Pass Rate: {:.2}%\n\n", pass_rate));
    report.push_str("=".repeat(80).as_str());
    report.push_str("\n\nFAILURES:\n\n");

    for result in results.iter().filter(|r| !r.passed()) {
      report.push_str(&format!("\n{}\n", "=".repeat(80)));
      report.push_str(&format!("File: {}\n", result.path.display()));
      report.push_str(&format!("Duration: {:?}\n", result.duration));
      if !result.diagnostics.is_empty() {
        append_rendered_diagnostics(&mut report, "", &result.files_store, &result.diagnostics);
      }

      for file in result.failed_files() {
        report.push_str(&format!("  Virtual file: {}\n", file.name));
        report.push_str(&format!("  Module mode: {}\n", file.module));
        if !file.diagnostics.is_empty() {
          append_rendered_diagnostics(&mut report, "    ", &result.files_store, &file.diagnostics);
        }
      }
    }

    fs::write(report_path, report).ok();
    println!("\n📝 Detailed failure report written to: {}", report_path);
  }

  println!("\n");

  if failed_count > 0 {
    std::process::exit(1);
  }
}
