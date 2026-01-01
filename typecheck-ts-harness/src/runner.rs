use crate::diagnostic_norm::{
  describe, normalize_rust_diagnostics, normalize_tsc_diagnostics, sort_diagnostics,
  within_tolerance, NormalizedDiagnostic,
};
use crate::directives::HarnessOptions;
use crate::discover::{discover_conformance_tests, Filter, Shard, TestCase, DEFAULT_EXTENSIONS};
use crate::expectations::{AppliedExpectation, ExpectationKind, Expectations};
use crate::multifile::normalize_name;
use crate::profile::ProfileBuilder;
use crate::resolve::resolve_module_specifier;
use crate::tsc::{
  node_available, typescript_available, TscDiagnostics, TscRequest, TscRunner,
  TSC_BASELINE_SCHEMA_VERSION,
};
use crate::{read_utf8_file, FailOn, Result, VirtualFile};
use rayon::prelude::*;
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value};
use std::collections::HashMap;
use std::panic::AssertUnwindSafe;
use std::path::{Path, PathBuf};
use std::sync::mpsc;
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};
use tracing::{info_span, Level};
use tracing_subscriber::fmt::format::FmtSpan;
use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileKey, Host, HostError, Program, QueryStats};
use walkdir::WalkDir;

const HARNESS_SLEEP_ENV: &str = "HARNESS_SLEEP_MS_PER_TEST";

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
  pub compare: CompareMode,
  pub node_path: PathBuf,
  pub span_tolerance: u32,
  pub allow_mismatches: bool,
  pub jobs: usize,
  pub manifest: Option<PathBuf>,
  pub fail_on: FailOn,
}

impl ConformanceOptions {
  pub fn new(root: PathBuf) -> Self {
    Self {
      root,
      filter: Filter::All,
      filter_pattern: None,
      shard: None,
      json: false,
      update_snapshots: false,
      timeout: Duration::from_secs(10),
      trace: false,
      profile: false,
      profile_out: crate::DEFAULT_PROFILE_OUT.into(),
      extensions: Vec::new(),
      allow_empty: false,
      compare: CompareMode::Auto,
      node_path: "node".into(),
      span_tolerance: 0,
      allow_mismatches: false,
      jobs: 1,
      manifest: None,
      fail_on: FailOn::New,
    }
  }
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

  pub fn mismatches(&self) -> usize {
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
  #[serde(skip_serializing_if = "Option::is_none")]
  pub mismatches: Option<MismatchSummary>,
}

impl Summary {
  pub fn has_mismatches(&self) -> bool {
    self.outcomes.mismatches() > 0
  }

  pub fn should_fail(&self, fail_on: FailOn, mismatches: usize) -> bool {
    let unexpected = self
      .mismatches
      .as_ref()
      .map(|m| m.unexpected)
      .unwrap_or(mismatches);
    fail_on.should_fail(unexpected, mismatches)
  }
}

#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct MismatchSummary {
  pub expected: usize,
  pub unexpected: usize,
  pub flaky: usize,
}

impl MismatchSummary {
  pub fn total(&self) -> usize {
    self.expected + self.unexpected + self.flaky
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
pub struct TestOptions {
  pub harness: HarnessOptions,
  pub rust: CompilerOptions,
  pub tsc: Map<String, Value>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct TestResult {
  pub id: String,
  pub path: String,
  pub outcome: TestOutcome,
  pub duration_ms: u128,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub rust_ms: Option<u128>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub tsc_ms: Option<u128>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub diff_ms: Option<u128>,
  pub rust: EngineDiagnostics,
  pub tsc: EngineDiagnostics,
  pub options: TestOptions,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub query_stats: Option<QueryStats>,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  pub notes: Vec<String>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub detail: Option<MismatchDetail>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub expectation: Option<ExpectationOutcome>,
  #[serde(default)]
  pub mismatched: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct MismatchDetail {
  pub message: String,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub rust: Option<NormalizedDiagnostic>,
  #[serde(skip_serializing_if = "Option::is_none")]
  pub tsc: Option<NormalizedDiagnostic>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ExpectationOutcome {
  pub expectation: ExpectationKind,
  #[serde(default)]
  pub expected: bool,
  #[serde(default, skip_serializing_if = "crate::serde_helpers::is_false")]
  pub from_manifest: bool,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub reason: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub tracking_issue: Option<String>,
}

fn build_test_options(
  harness_options: &HarnessOptions,
  tsc_options: &Map<String, Value>,
) -> TestOptions {
  TestOptions {
    harness: harness_options.clone(),
    rust: harness_options.to_compiler_options(),
    tsc: tsc_options.clone(),
  }
}

#[derive(Clone)]
struct HarnessFile {
  key: FileKey,
  content: Arc<str>,
}

#[derive(Clone)]
pub struct HarnessFileSet {
  files: Vec<HarnessFile>,
  name_to_key: HashMap<String, FileKey>,
  key_to_name: HashMap<FileKey, String>,
  package_json_cache: Arc<PackageJsonCache>,
}

#[derive(Debug, Default)]
struct PackageJsonCache {
  parsed: Mutex<HashMap<FileKey, Option<Arc<Value>>>>,
}

#[derive(Clone)]
struct PlannedCase {
  case: TestCase,
  expectation: AppliedExpectation,
}

impl HarnessFileSet {
  pub fn new(files: &[VirtualFile]) -> Self {
    let mut normalized_names = Vec::with_capacity(files.len());
    for file in files {
      normalized_names.push(normalize_name(&file.name));
    }

    let mut last_occurrence = HashMap::new();
    for (idx, normalized) in normalized_names.iter().enumerate() {
      last_occurrence.insert(normalized.clone(), idx);
    }

    let mut stored = Vec::with_capacity(last_occurrence.len());
    let mut name_to_key = HashMap::new();
    let mut key_to_name = HashMap::new();

    for (idx, normalized) in normalized_names.into_iter().enumerate() {
      if last_occurrence.get(&normalized).copied() != Some(idx) {
        continue;
      }

      let key = FileKey::new(normalized.clone());
      name_to_key.insert(normalized.clone(), key.clone());
      key_to_name.insert(key.clone(), normalized.clone());
      stored.push(HarnessFile {
        key,
        content: Arc::from(files[idx].content.clone()),
      });
    }

    Self {
      files: stored,
      name_to_key,
      key_to_name,
      package_json_cache: Arc::new(PackageJsonCache::default()),
    }
  }

  /// Roots to pass to the Rust checker / `tsc` as `rootNames`.
  ///
  /// The harness virtual file system can include non-source files such as
  /// `package.json` used for module resolution. Those must remain available to
  /// the host/tsc runner, but should not be parsed/typechecked as compilation
  /// roots.
  pub(crate) fn root_keys(&self) -> Vec<FileKey> {
    let mut roots: Vec<_> = self
      .files
      .iter()
      .filter(|file| is_source_root(file.key.as_str()))
      .map(|file| file.key.clone())
      .collect();
    roots.sort_by(|a, b| a.as_str().cmp(b.as_str()));
    roots
  }

  pub(crate) fn resolve(&self, normalized: &str) -> Option<FileKey> {
    self.name_to_key.get(normalized).cloned()
  }

  pub(crate) fn resolve_import(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    resolve_module_specifier(self, from, specifier)
  }

  pub(crate) fn package_json(&self, key: &FileKey) -> Option<Arc<Value>> {
    {
      let guard = self.package_json_cache.parsed.lock().unwrap();
      if let Some(cached) = guard.get(key) {
        return cached.clone();
      }
    }

    let raw = self.content(key)?;
    let parsed: Option<Value> = serde_json::from_str(&raw).ok();
    let parsed = parsed.map(Arc::new);
    let mut guard = self.package_json_cache.parsed.lock().unwrap();
    guard.insert(key.clone(), parsed.clone());
    parsed
  }

  pub(crate) fn name_for_key(&self, key: &FileKey) -> Option<String> {
    self.key_to_name.get(key).cloned()
  }

  fn iter(&self) -> impl Iterator<Item = &HarnessFile> {
    self.files.iter()
  }

  pub(crate) fn content(&self, key: &FileKey) -> Option<Arc<str>> {
    self
      .files
      .iter()
      .find(|f| &f.key == key)
      .map(|f| f.content.clone())
  }
}

pub(crate) fn is_source_root(name: &str) -> bool {
  [
    ".ts", ".tsx", ".d.ts", ".js", ".jsx", ".mjs", ".cjs", ".mts", ".cts", ".d.mts", ".d.cts",
  ]
  .into_iter()
  .any(|suffix| name.ends_with(suffix))
}

pub fn run_conformance(opts: ConformanceOptions) -> Result<ConformanceReport> {
  init_tracing(opts.trace);
  let wall_start = Instant::now();
  let mut profile_builder = opts.profile.then(|| ProfileBuilder::new(&opts));
  let extensions = if opts.extensions.is_empty() {
    DEFAULT_EXTENSIONS.iter().map(|s| s.to_string()).collect()
  } else {
    opts.extensions.clone()
  };

  let mut cases = discover_conformance_tests(&opts.root, &opts.filter, &extensions)?;
  let root_missing = !opts.root.is_dir();
  if (root_missing || cases.is_empty()) && !opts.allow_empty {
    return Err(crate::HarnessError::EmptySuite {
      root: opts.root.display().to_string(),
      extensions: extensions.join(","),
    });
  }

  let expectations = match &opts.manifest {
    Some(path) => Expectations::from_path(path)?,
    None => Expectations::empty(),
  };

  if let Some(shard) = opts.shard {
    cases = cases
      .into_iter()
      .enumerate()
      .filter(|(idx, _)| shard.includes(*idx))
      .map(|(_, case)| case)
      .collect();
  }

  let planned_cases: Vec<PlannedCase> = cases
    .into_iter()
    .map(|case| PlannedCase {
      expectation: expectations.lookup(&case.id),
      case,
    })
    .collect();

  let tsc_available = node_available(&opts.node_path) && typescript_available(&opts.node_path);
  let snapshot_store = SnapshotStore::new(&opts.root);
  let requested_compare = if opts.update_snapshots {
    CompareMode::Snapshot
  } else {
    opts.compare
  };
  let compare_mode = resolve_compare_mode(requested_compare, tsc_available, &snapshot_store);
  if opts.update_snapshots && !tsc_available {
    return Err(crate::HarnessError::Typecheck(
      "cannot update snapshots: tsc unavailable (install Node.js and the `typescript` npm package)"
        .to_string(),
    ));
  }
  if let Some(builder) = profile_builder.as_mut() {
    builder.set_compare_mode(compare_mode);
  }

  let job_count = opts.jobs.max(1);
  let tsc_limiter = Arc::new(ConcurrencyLimiter::new(job_count));
  let tsc_pool = Arc::new(TscRunnerPool::new(
    opts.node_path.clone(),
    tsc_limiter.clone(),
  ));
  let pool = rayon::ThreadPoolBuilder::new()
    .num_threads(job_count)
    .build()
    .map_err(|err| crate::HarnessError::Typecheck(format!("create thread pool: {err}")))?;

  let mut results: Vec<TestResult> = pool.install(|| {
    planned_cases
      .par_iter()
      .map(|planned| {
        let base_result = if planned.expectation.expectation.kind == ExpectationKind::Skip {
          build_skipped_result(&planned.case)
        } else {
          run_single_case(
            planned.case.clone(),
            compare_mode,
            tsc_pool.clone(),
            tsc_available,
            &snapshot_store,
            &opts,
          )
        };
        apply_expectation(base_result, &planned.expectation)
      })
      .collect()
  });

  // Ensure deterministic output ordering regardless of parallel execution timing.
  results.sort_by(|a, b| a.id.cmp(&b.id));

  if let Some(builder) = profile_builder.as_mut() {
    for result in &results {
      builder.record_test(result);
    }
  }

  let mut summary = summarize(&results);
  let mut mismatch_summary = MismatchSummary::default();
  for result in results.iter() {
    if !result.mismatched {
      continue;
    }
    if let Some(exp) = &result.expectation {
      if exp.expectation == ExpectationKind::Flaky {
        mismatch_summary.flaky += 1;
      } else if exp.expected {
        mismatch_summary.expected += 1;
      } else {
        mismatch_summary.unexpected += 1;
      }
    } else {
      mismatch_summary.unexpected += 1;
    }
  }
  if mismatch_summary.total() > 0 {
    summary.mismatches = Some(mismatch_summary);
  }

  let wall_time = wall_start.elapsed();
  if let Some(builder) = profile_builder {
    builder.write(&summary, wall_time, &opts.profile_out)?;
  }

  if !opts.allow_mismatches && summary.should_fail(opts.fail_on, summary.outcomes.mismatches()) {
    return Err(crate::HarnessError::Typecheck(
      "conformance mismatches".to_string(),
    ));
  }

  Ok(ConformanceReport {
    summary,
    compare_mode,
    results,
  })
}

fn build_skipped_result(case: &TestCase) -> TestResult {
  let tsc_options = case.options.to_tsc_options_map();
  TestResult {
    id: case.id.clone(),
    path: case.path.display().to_string(),
    outcome: TestOutcome::Match,
    duration_ms: 0,
    rust_ms: None,
    tsc_ms: None,
    diff_ms: None,
    rust: EngineDiagnostics::skipped(Some("skipped by manifest".into())),
    tsc: EngineDiagnostics::skipped(Some("skipped by manifest".into())),
    options: build_test_options(&case.options, &tsc_options),
    query_stats: None,
    notes: case.notes.clone(),
    detail: None,
    expectation: None,
    mismatched: false,
  }
}

fn apply_expectation(result: TestResult, expectation: &AppliedExpectation) -> TestResult {
  let mismatched = result.outcome != TestOutcome::Match;
  let expected = expectation.matches(mismatched);
  TestResult {
    mismatched,
    expectation: Some(ExpectationOutcome {
      expectation: expectation.expectation.kind,
      expected,
      from_manifest: expectation.from_manifest,
      reason: expectation.expectation.reason.clone(),
      tracking_issue: expectation.expectation.tracking_issue.clone(),
    }),
    ..result
  }
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
  tsc_pool: Arc<TscRunnerPool>,
  tsc_available: bool,
  snapshots: &SnapshotStore,
  opts: &ConformanceOptions,
) -> TestResult {
  let (tx, rx) = mpsc::channel();
  let span = info_span!("test_case", test_id = %case.id);
  let _enter = span.enter();
  let span_for_thread = span.clone();
  let cloned_tsc_pool = tsc_pool.clone();
  let cloned_snapshots = snapshots.clone();
  let timeout_id = case.id.clone();
  let timeout_path = case.path.display().to_string();
  let timeout_notes = case.notes.clone();
  let timeout_options = build_test_options(&case.options, &case.options.to_tsc_options_map());
  let timeout = opts.timeout;
  let span_tolerance = opts.span_tolerance;
  let update_snapshots = opts.update_snapshots;
  let collect_query_stats = opts.profile;
  std::thread::spawn(move || {
    let _entered = span_for_thread.enter();
    let result = execute_case(
      case,
      compare_mode,
      cloned_tsc_pool,
      tsc_available,
      cloned_snapshots,
      span_tolerance,
      update_snapshots,
      collect_query_stats,
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
      rust_ms: None,
      tsc_ms: None,
      diff_ms: None,
      rust: EngineDiagnostics::skipped(None),
      tsc: EngineDiagnostics::skipped(None),
      options: timeout_options,
      query_stats: None,
      notes: timeout_notes,
      detail: None,
      expectation: None,
      mismatched: true,
    },
  }
}

fn execute_case(
  case: TestCase,
  compare_mode: CompareMode,
  tsc_pool: Arc<TscRunnerPool>,
  tsc_available: bool,
  snapshots: SnapshotStore,
  span_tolerance: u32,
  update_snapshots: bool,
  collect_query_stats: bool,
) -> TestResult {
  let total_start = Instant::now();
  if let Some(delay) = harness_sleep_for_case(&case.id) {
    std::thread::sleep(delay);
  }
  let notes = case.notes.clone();
  let file_set = HarnessFileSet::new(&case.deduped_files);
  let harness_options = case.options.clone();

  let rust_start = Instant::now();
  let (rust, query_stats) = run_rust_with_profile(&file_set, &harness_options, collect_query_stats);
  let rust_ms = rust_start.elapsed().as_millis();
  let tsc_options = harness_options.to_tsc_options_map();
  let options = build_test_options(&harness_options, &tsc_options);

  let mut tsc_raw: Option<TscDiagnostics> = None;
  let mut tsc_ms: Option<u128> = None;
  // The diff/normalization phase begins after we have Rust diagnostics. If we
  // invoke tsc, we reset this clock after tsc completes so `diff_ms` does not
  // include `tsc_ms`.
  let mut diff_start = Instant::now();
  let mut run_live_tsc = |unavailable: &str| {
    if tsc_available {
      let tsc_start = Instant::now();
      let (diag, raw) = run_tsc_with_raw(&tsc_pool, &file_set, &tsc_options);
      tsc_ms = Some(tsc_start.elapsed().as_millis());
      diff_start = Instant::now();
      tsc_raw = raw;
      diag
    } else {
      EngineDiagnostics::crashed(unavailable)
    }
  };
  let tsc = match compare_mode {
    CompareMode::None => EngineDiagnostics::skipped(Some("comparison disabled".to_string())),
    CompareMode::Tsc => run_live_tsc("tsc unavailable"),
    CompareMode::Snapshot if update_snapshots => {
      run_live_tsc("tsc unavailable for snapshot update")
    }
    CompareMode::Snapshot => match snapshots.load(&case.id) {
      Ok(snapshot) => {
        let normalized = normalize_tsc_diagnostics(&snapshot.diagnostics);
        let crashed = snapshot
          .crash
          .as_ref()
          .map(|crash| EngineDiagnostics::crashed(crash.message.clone()));
        tsc_raw = Some(snapshot);
        crashed.unwrap_or_else(|| EngineDiagnostics::ok(normalized))
      }
      Err(err) => EngineDiagnostics::crashed(format!("missing snapshot: {err}")),
    },
    CompareMode::Auto => unreachable!("compare mode should be resolved before execution"),
  };

  if update_snapshots && tsc.status == EngineStatus::Ok {
    if let Some(raw) = tsc_raw.as_ref() {
      let _ = snapshots.save(&case.id, raw);
    }
  }

  let (outcome, detail) = compute_outcome(compare_mode, &rust, &tsc, span_tolerance);
  let diff_ms = diff_start.elapsed().as_millis();

  TestResult {
    id: case.id,
    path: case.path.display().to_string(),
    outcome,
    duration_ms: total_start.elapsed().as_millis(),
    rust_ms: Some(rust_ms),
    tsc_ms,
    diff_ms: Some(diff_ms),
    rust,
    tsc,
    options,
    query_stats,
    notes,
    detail,
    expectation: None,
    mismatched: false,
  }
}

pub(crate) fn run_rust(file_set: &HarnessFileSet, options: &HarnessOptions) -> EngineDiagnostics {
  run_rust_with_profile(file_set, options, false).0
}

fn run_rust_with_profile(
  file_set: &HarnessFileSet,
  options: &HarnessOptions,
  collect_profile: bool,
) -> (EngineDiagnostics, Option<QueryStats>) {
  let compiler_options = options.to_compiler_options();
  let host = HarnessHost::new(file_set.clone(), compiler_options.clone());
  let roots = file_set.root_keys();
  let program = Program::new(host, roots);
  let result = std::panic::catch_unwind(AssertUnwindSafe(|| program.check()));
  let stats = (collect_profile && result.is_ok()).then(|| program.query_stats());
  let diagnostics = match result {
    Ok(diags) => EngineDiagnostics::ok(normalize_rust_diagnostics(&diags, |id| {
      program
        .file_key(id)
        .and_then(|key| file_set.name_for_key(&key))
    })),
    Err(_) => EngineDiagnostics::ice("typechecker panicked"),
  };
  (diagnostics, stats)
}

fn init_tracing(enabled: bool) {
  if !enabled {
    return;
  }
  let _ = tracing_subscriber::fmt()
    .with_writer(std::io::stderr)
    .with_span_events(FmtSpan::CLOSE)
    .with_max_level(Level::DEBUG)
    .json()
    .with_ansi(false)
    .try_init();
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

fn run_tsc_with_raw(
  pool: &TscRunnerPool,
  file_set: &HarnessFileSet,
  options: &Map<String, Value>,
) -> (EngineDiagnostics, Option<TscDiagnostics>) {
  match pool.run(file_set, options) {
    Ok(diags) => match &diags.crash {
      Some(crash) => (
        EngineDiagnostics::crashed(crash.message.clone()),
        Some(diags),
      ),
      None => {
        let normalized = normalize_tsc_diagnostics(&diags.diagnostics);
        (EngineDiagnostics::ok(normalized), Some(diags))
      }
    },
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

  // Greedily match expected (tsc) diagnostics to actual (rust) diagnostics.
  //
  // This avoids cascaded mismatches when one side has an extra diagnostic near the
  // top of the sorted list (the previous implementation zipped by index).
  let mut used = vec![false; rust_sorted.len()];
  let mut missing: Vec<NormalizedDiagnostic> = Vec::new();
  let mut extra: Vec<NormalizedDiagnostic> = Vec::new();
  let mut span_mismatches: Vec<(NormalizedDiagnostic, NormalizedDiagnostic)> = Vec::new();
  let mut code_mismatches: Vec<(NormalizedDiagnostic, NormalizedDiagnostic)> = Vec::new();

  for tsc in &tsc_sorted {
    if let Some(idx) = find_diag(&rust_sorted, &used, |rust| {
      rust.file == tsc.file
        && within_tolerance(rust.start, tsc.start, span_tolerance)
        && within_tolerance(rust.end, tsc.end, span_tolerance)
        && rust.codes_match(tsc)
    }) {
      used[idx] = true;
      continue;
    }

    if let Some(idx) = find_best_diag(&rust_sorted, &used, tsc, |rust| {
      rust.file == tsc.file
        && within_tolerance(rust.start, tsc.start, span_tolerance)
        && within_tolerance(rust.end, tsc.end, span_tolerance)
        && !rust.codes_match(tsc)
    }) {
      used[idx] = true;
      code_mismatches.push((rust_sorted[idx].clone(), tsc.clone()));
      continue;
    }

    if let Some(idx) = find_best_diag(&rust_sorted, &used, tsc, |rust| {
      rust.file == tsc.file && rust.codes_match(tsc)
    }) {
      used[idx] = true;
      span_mismatches.push((rust_sorted[idx].clone(), tsc.clone()));
      continue;
    }

    missing.push(tsc.clone());
  }

  for (idx, rust) in rust_sorted.iter().enumerate() {
    if !used[idx] {
      extra.push(rust.clone());
    }
  }

  if let Some(tsc) = missing.first() {
    return (
      TestOutcome::RustMissingDiagnostics,
      Some(MismatchDetail {
        message: format!("rust missed {} diagnostic(s)", missing.len()),
        rust: None,
        tsc: Some(tsc.clone()),
      }),
    );
  }

  if let Some(rust) = extra.first() {
    return (
      TestOutcome::RustExtraDiagnostics,
      Some(MismatchDetail {
        message: format!("rust produced {} extra diagnostic(s)", extra.len()),
        rust: Some(rust.clone()),
        tsc: None,
      }),
    );
  }

  if let Some((rust, tsc)) = span_mismatches.first() {
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

  if let Some((rust, tsc)) = code_mismatches.first() {
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

  (TestOutcome::Match, None)
}

fn find_diag<F>(actual: &[NormalizedDiagnostic], used: &[bool], mut predicate: F) -> Option<usize>
where
  F: FnMut(&NormalizedDiagnostic) -> bool,
{
  actual
    .iter()
    .enumerate()
    .find(|(idx, diag)| !used[*idx] && predicate(diag))
    .map(|(idx, _)| idx)
}

fn find_best_diag<F>(
  actual: &[NormalizedDiagnostic],
  used: &[bool],
  expected: &NormalizedDiagnostic,
  mut predicate: F,
) -> Option<usize>
where
  F: FnMut(&NormalizedDiagnostic) -> bool,
{
  let mut best: Option<(usize, u32)> = None;
  for (idx, diag) in actual.iter().enumerate() {
    if used[idx] || !predicate(diag) {
      continue;
    }
    let distance = expected.start.abs_diff(diag.start) + expected.end.abs_diff(diag.end);
    if best
      .as_ref()
      .map(|(_, best_distance)| distance < *best_distance)
      .unwrap_or(true)
    {
      best = Some((idx, distance));
    }
  }
  best.map(|(idx, _)| idx)
}

fn summarize(results: &[TestResult]) -> Summary {
  let mut summary = Summary::default();
  summary.total = results.len();
  for result in results {
    summary.outcomes.increment(result.outcome);
  }
  summary
}

pub(crate) struct HarnessHost {
  files: HarnessFileSet,
  compiler_options: CompilerOptions,
}

impl HarnessHost {
  pub(crate) fn new(files: HarnessFileSet, compiler_options: CompilerOptions) -> Self {
    Self {
      files,
      compiler_options,
    }
  }
}

impl Host for HarnessHost {
  fn file_text(&self, file: &FileKey) -> std::result::Result<Arc<str>, HostError> {
    self
      .files
      .content(file)
      .ok_or_else(|| HostError::new(format!("missing file {}", file.as_str())))
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    let name = self
      .files
      .name_for_key(file)
      .unwrap_or_else(|| file.as_str().to_string());
    crate::file_kind::infer_file_kind(&name)
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.compiler_options.clone()
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    self.files.resolve_import(from, specifier)
  }
}

pub(crate) struct TscRunnerPool {
  node_path: PathBuf,
  limiter: Arc<ConcurrencyLimiter>,
  runners: Mutex<Vec<TscRunner>>,
}

impl TscRunnerPool {
  pub(crate) fn new(node_path: PathBuf, limiter: Arc<ConcurrencyLimiter>) -> Self {
    Self {
      node_path,
      limiter,
      runners: Mutex::new(Vec::new()),
    }
  }

  pub(crate) fn run(
    &self,
    file_set: &HarnessFileSet,
    options: &Map<String, Value>,
  ) -> std::result::Result<TscDiagnostics, String> {
    let request = build_tsc_request(file_set, options, true);
    self.run_request(request)
  }

  pub(crate) fn run_request(
    &self,
    request: TscRequest,
  ) -> std::result::Result<TscDiagnostics, String> {
    let _permit = self.limiter.acquire();
    let mut runner = self.checkout().map_err(|err| err.to_string())?;
    match runner.check(request) {
      Ok(diags) => {
        self.release(runner);
        Ok(diags)
      }
      Err(err) => {
        // Don't return broken runners back to the pool; `TscRunner::check` only errors when the
        // runner crashed or otherwise failed unexpectedly (not on normal type errors).
        Err(err.to_string())
      }
    }
  }

  fn checkout(&self) -> anyhow::Result<TscRunner> {
    // Avoid holding the mutex while spawning Node. This prevents other threads from being blocked
    // when returning an existing runner to the pool.
    let runner = {
      let mut runners = self.runners.lock().unwrap();
      runners.pop()
    };
    runner
      .map(Ok)
      .unwrap_or_else(|| TscRunner::new(self.node_path.clone()))
  }

  fn release(&self, runner: TscRunner) {
    let mut runners = self.runners.lock().unwrap();
    runners.push(runner);
  }
}

pub(crate) fn build_tsc_request(
  file_set: &HarnessFileSet,
  options: &Map<String, Value>,
  diagnostics_only: bool,
) -> TscRequest {
  let mut files = HashMap::new();

  for file in file_set.iter() {
    let name = file.key.as_str().to_string();
    files.insert(name, file.content.to_string());
  }

  let mut root_names: Vec<String> = file_set
    .root_keys()
    .into_iter()
    .map(|key| key.as_str().to_string())
    .collect();
  root_names.sort();
  root_names.dedup();

  TscRequest {
    root_names,
    files,
    options: options.clone(),
    diagnostics_only,
    type_queries: Vec::new(),
  }
}

#[derive(Clone)]
struct SnapshotStore {
  base: PathBuf,
}

#[derive(Clone, Debug)]
pub(crate) struct ConcurrencyLimiter {
  inner: Arc<LimiterInner>,
}

#[derive(Debug)]
struct LimiterInner {
  max: usize,
  active: Mutex<usize>,
  cv: Condvar,
}

impl ConcurrencyLimiter {
  pub(crate) fn new(max: usize) -> Self {
    let max = max.max(1);
    ConcurrencyLimiter {
      inner: Arc::new(LimiterInner {
        max,
        active: Mutex::new(0),
        cv: Condvar::new(),
      }),
    }
  }

  pub(crate) fn acquire(&self) -> ConcurrencyPermit {
    let mut guard = self.inner.active.lock().unwrap();
    while *guard >= self.inner.max {
      guard = self.inner.cv.wait(guard).unwrap();
    }
    *guard += 1;
    ConcurrencyPermit {
      inner: Arc::clone(&self.inner),
    }
  }
}

#[derive(Debug)]
pub(crate) struct ConcurrencyPermit {
  inner: Arc<LimiterInner>,
}

impl Drop for ConcurrencyPermit {
  fn drop(&mut self) {
    let mut guard = self.inner.active.lock().unwrap();
    *guard = guard.saturating_sub(1);
    self.inner.cv.notify_one();
  }
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
    if let Some(ext) = path.extension().and_then(|s| s.to_str()) {
      path.set_extension(format!("{ext}.json"));
    } else {
      path.set_extension("json");
    }
    path
  }

  fn legacy_path_for(&self, id: &str) -> PathBuf {
    let mut path = self.base.join(id);
    path.set_extension("json");
    path
  }

  fn load(&self, id: &str) -> std::io::Result<TscDiagnostics> {
    let path = self.path_for(id);
    let data = match read_utf8_file(&path) {
      Ok(data) => data,
      Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
        let legacy = self.legacy_path_for(id);
        match read_utf8_file(&legacy) {
          Ok(data) => data,
          Err(err) if err.kind() == std::io::ErrorKind::NotFound => {
            return Err(std::io::Error::new(
              std::io::ErrorKind::NotFound,
              format!(
                "snapshot not found for {id} (tried {} and {})",
                path.display(),
                legacy.display()
              ),
            ));
          }
          Err(err) => return Err(err),
        }
      }
      Err(err) => return Err(err),
    };
    let parsed: TscDiagnostics = serde_json::from_str(&data)?;
    let version = parsed.schema_version.unwrap_or(0);
    if version != TSC_BASELINE_SCHEMA_VERSION {
      return Err(std::io::Error::new(
        std::io::ErrorKind::InvalidData,
        format!(
          "snapshot schema mismatch (found {version}, expected {TSC_BASELINE_SCHEMA_VERSION}); regenerate snapshots"
        ),
      ));
    }
    Ok(parsed)
  }

  fn save(&self, id: &str, diagnostics: &TscDiagnostics) -> std::io::Result<()> {
    let path = self.path_for(id);
    if let Some(parent) = path.parent() {
      std::fs::create_dir_all(parent)?;
    }

    let mut payload = diagnostics.clone();
    payload.canonicalize_for_baseline();
    let json = serde_json::to_string_pretty(&payload)?;
    std::fs::write(path, format!("{json}\n"))
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::sync::atomic::{AtomicUsize, Ordering};
  use std::sync::Arc;
  use std::time::Duration;
  use tempfile::tempdir;

  #[test]
  fn shard_parse_rejects_invalid() {
    assert!(Shard::parse("bad").is_err());
    assert!(Shard::parse("1/0").is_err());
    assert!(Shard::parse("2/2").is_err());
  }

  #[test]
  fn concurrency_limiter_caps_parallelism() {
    let limiter = ConcurrencyLimiter::new(2);
    let active = Arc::new(AtomicUsize::new(0));
    let max_seen = Arc::new(AtomicUsize::new(0));

    let handles: Vec<_> = (0..6)
      .map(|_| {
        let limiter = limiter.clone();
        let active = active.clone();
        let max_seen = max_seen.clone();
        std::thread::spawn(move || {
          let _permit = limiter.acquire();
          let current = active.fetch_add(1, Ordering::SeqCst) + 1;
          max_seen.fetch_max(current, Ordering::SeqCst);
          std::thread::sleep(Duration::from_millis(10));
          active.fetch_sub(1, Ordering::SeqCst);
        })
      })
      .collect();

    for handle in handles {
      handle.join().unwrap();
    }

    assert!(max_seen.load(Ordering::SeqCst) <= 2);
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
  fn diff_matches_rust_ts_prefixed_code_with_tsc_numeric_code() {
    let rust = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Rust,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Rust(
        "TS2345".into(),
      )),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];
    let tsc = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Tsc,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Tsc(2345)),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];

    let (outcome, detail) = diff_diagnostics(&rust, &tsc, 0);
    assert_eq!(outcome, TestOutcome::Match);
    assert!(detail.is_none());
  }

  #[test]
  fn diff_matches_rust_numeric_string_code_with_tsc_numeric_code() {
    let rust = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Rust,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Rust("2345".into())),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];
    let tsc = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Tsc,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Tsc(2345)),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];

    let (outcome, _) = diff_diagnostics(&rust, &tsc, 0);
    assert_eq!(outcome, TestOutcome::Match);
  }

  #[test]
  fn diff_reports_code_mismatch_for_different_codes() {
    let rust = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Rust,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Rust(
        "TS9999".into(),
      )),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];
    let tsc = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Tsc,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Tsc(2345)),
      file: Some("a.ts".into()),
      start: 0,
      end: 1,
      severity: None,
      message: None,
    }];

    let (outcome, detail) = diff_diagnostics(&rust, &tsc, 0);
    assert_eq!(outcome, TestOutcome::CodeMismatch);
    assert!(detail.is_some());
  }

  #[test]
  fn diff_does_not_cascade_span_mismatches_from_extra_diagnostics() {
    let rust = vec![
      NormalizedDiagnostic {
        engine: crate::diagnostic_norm::DiagnosticEngine::Rust,
        code: Some(crate::diagnostic_norm::DiagnosticCode::Rust(
          "TS9999".into(),
        )),
        file: Some("a.ts".into()),
        start: 0,
        end: 1,
        severity: None,
        message: None,
      },
      NormalizedDiagnostic {
        engine: crate::diagnostic_norm::DiagnosticEngine::Rust,
        code: Some(crate::diagnostic_norm::DiagnosticCode::Rust(
          "TS2345".into(),
        )),
        file: Some("a.ts".into()),
        start: 10,
        end: 11,
        severity: None,
        message: None,
      },
    ];
    let tsc = vec![NormalizedDiagnostic {
      engine: crate::diagnostic_norm::DiagnosticEngine::Tsc,
      code: Some(crate::diagnostic_norm::DiagnosticCode::Tsc(2345)),
      file: Some("a.ts".into()),
      start: 10,
      end: 11,
      severity: None,
      message: None,
    }];

    let (outcome, _) = diff_diagnostics(&rust, &tsc, 0);
    assert_eq!(outcome, TestOutcome::RustExtraDiagnostics);
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
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());
    let roots = file_set.root_keys();

    assert_eq!(roots.len(), 2);

    let from = roots.last().unwrap();
    let a_key = host.resolve(from, "a.ts").expect("a.ts should resolve");
    assert!(roots.contains(&a_key));
    assert_eq!(&*host.file_text(&a_key).unwrap(), "second version");
  }

  #[test]
  fn harness_host_carries_compiler_options() {
    let files = vec![VirtualFile {
      name: "a.ts".to_string(),
      content: "const value: string = null;".to_string(),
    }];

    let mut harness_options = HarnessOptions::default();
    harness_options.strict_null_checks = Some(true);
    let compiler_options = harness_options.to_compiler_options();
    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), compiler_options.clone());
    let program = Program::new(host, file_set.root_keys());

    assert_eq!(program.compiler_options(), compiler_options);
  }

  #[test]
  fn harness_file_set_excludes_json_files_from_roots() {
    let files = vec![
      VirtualFile {
        name: "a.ts".to_string(),
        content: "const a = 1;\n".to_string(),
      },
      VirtualFile {
        name: "package.json".to_string(),
        content: "{\n  \"name\": \"pkg\"\n}\n".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let roots = file_set.root_keys();
    let root_names: Vec<&str> = roots.iter().map(|k| k.as_str()).collect();
    assert_eq!(root_names, vec!["/a.ts"]);

    let rust = run_rust(&file_set, &HarnessOptions::default());
    assert!(
      rust.diagnostics.is_empty(),
      "expected JSON to be excluded from roots; got diagnostics: {:#?}",
      rust.diagnostics
    );
  }

  #[test]
  fn harness_file_set_root_order_is_deterministic() {
    let files = vec![
      VirtualFile {
        name: "b.ts".to_string(),
        content: "const b = 1;\n".to_string(),
      },
      VirtualFile {
        name: "a.ts".to_string(),
        content: "const a = 1;\n".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let roots = file_set.root_keys();
    let root_names: Vec<&str> = roots.iter().map(|k| k.as_str()).collect();
    assert_eq!(root_names, vec!["/a.ts", "/b.ts"]);
  }

  #[test]
  fn harness_file_set_roots_include_mts_and_cts() {
    let files = vec![
      VirtualFile {
        name: "a.mts".to_string(),
        content: "export const a = 1;\n".to_string(),
      },
      VirtualFile {
        name: "b.cts".to_string(),
        content: "export const b = 2;\n".to_string(),
      },
      VirtualFile {
        name: "c.d.mts".to_string(),
        content: "export {};\n".to_string(),
      },
      VirtualFile {
        name: "d.d.cts".to_string(),
        content: "export {};\n".to_string(),
      },
      VirtualFile {
        name: "e.mjs".to_string(),
        content: "export const e = 3;\n".to_string(),
      },
      VirtualFile {
        name: "f.cjs".to_string(),
        content: "exports.f = 4;\n".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let roots = file_set.root_keys();
    let root_names: Vec<&str> = roots.iter().map(|k| k.as_str()).collect();
    assert_eq!(
      root_names,
      vec!["/a.mts", "/b.cts", "/c.d.mts", "/d.d.cts", "/e.mjs", "/f.cjs"]
    );
  }

  #[test]
  fn harness_host_uses_tsx_parser_for_tsx_inputs() {
    let files = vec![VirtualFile {
      name: "case.tsx".to_string(),
      content: "const el = <div />;\n".to_string(),
    }];

    let file_set = HarnessFileSet::new(&files);
    let diagnostics = run_rust(&file_set, &HarnessOptions::default());
    assert_eq!(
      diagnostics.status,
      EngineStatus::Ok,
      "{:?}",
      diagnostics.error
    );

    let parse_diags: Vec<_> = diagnostics
      .diagnostics
      .iter()
      .filter(|diag| {
        matches!(
          diag.code.as_ref(),
          Some(crate::diagnostic_norm::DiagnosticCode::Rust(code)) if code.starts_with("PS")
        )
      })
      .collect();

    assert!(
      parse_diags.is_empty(),
      "expected no parse-js diagnostics for TSX input, got: {parse_diags:?}"
    );
  }

  #[test]
  fn resolves_bare_specifier_via_node_modules() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set.resolve("/node_modules/foo/index.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_prefers_nearest_node_modules() {
    let files = vec![
      VirtualFile {
        name: "/src/b.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/src/node_modules/foo/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/index.d.ts".to_string(),
        content: "export const x: string;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/src/b.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set
      .resolve("/src/node_modules/foo/index.d.ts")
      .unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_falls_back_to_ancestor_node_modules() {
    let files = vec![
      VirtualFile {
        name: "/src/b.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/src/b.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set.resolve("/node_modules/foo/index.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_at_types_fallback() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/@types/foo/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set
      .resolve("/node_modules/@types/foo/index.d.ts")
      .unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_package_json_types() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/package.json".to_string(),
        content: r#"{ "name": "foo", "types": "types.d.ts" }"#.to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/types.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set.resolve("/node_modules/foo/types.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_hash_specifier_via_package_json_imports() {
    let files = vec![
      VirtualFile {
        name: "/src/a.ts".to_string(),
        content: "import { x } from \"#foo\";".to_string(),
      },
      VirtualFile {
        name: "/src/package.json".to_string(),
        content: r##"{ "imports": { "#foo": { "types": "./types/foo.d.ts", "default": "./types/foo.js" } } }"##.to_string(),
      },
      VirtualFile {
        name: "/src/types/foo.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/src/a.ts").unwrap();
    let resolved = host.resolve(&from, "#foo").expect("#foo should resolve");
    let expected = file_set.resolve("/src/types/foo.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_hash_specifier_via_package_json_imports_pattern() {
    let files = vec![
      VirtualFile {
        name: "/src/a.ts".to_string(),
        content: "import { x } from \"#foo/bar\";".to_string(),
      },
      VirtualFile {
        name: "/src/package.json".to_string(),
        content: r##"{ "imports": { "#foo/*": { "types": "./types/*.d.ts", "default": "./types/*.js" } } }"##.to_string(),
      },
      VirtualFile {
        name: "/src/types/bar.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/src/a.ts").unwrap();
    let resolved = host
      .resolve(&from, "#foo/bar")
      .expect("#foo/bar should resolve");
    let expected = file_set.resolve("/src/types/bar.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_package_json_exports_root() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/package.json".to_string(),
        content: r#"{ "name": "foo", "exports": { ".": { "types": "./dist/index.d.ts", "default": "./dist/index.js" } } }"#.to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/dist/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set
      .resolve("/node_modules/foo/dist/index.d.ts")
      .unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_package_json_exports_fallback_when_first_missing() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/package.json".to_string(),
        content: r#"{ "name": "foo", "exports": { ".": { "types": "./missing.d.ts", "default": "./dist/index.d.ts" } } }"#.to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/dist/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set
      .resolve("/node_modules/foo/dist/index.d.ts")
      .unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_package_json_exports_subpath() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo/bar\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/package.json".to_string(),
        content: r#"{ "name": "foo", "exports": { "./bar": { "types": "./dist/bar.d.ts", "default": "./dist/bar.js" } } }"#.to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/dist/bar.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host
      .resolve(&from, "foo/bar")
      .expect("foo/bar should resolve");
    let expected = file_set.resolve("/node_modules/foo/dist/bar.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_package_json_exports_subpath_pattern() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo/bar\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/package.json".to_string(),
        content: r#"{ "name": "foo", "exports": { "./*": { "types": "./dist/*.d.ts", "default": "./dist/*.js" } } }"#.to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/dist/bar.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host
      .resolve(&from, "foo/bar")
      .expect("foo/bar should resolve via exports pattern");
    let expected = file_set.resolve("/node_modules/foo/dist/bar.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_relative_js_specifier_via_d_ts_substitution() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import \"./foo.js\";".to_string(),
      },
      VirtualFile {
        name: "/foo.d.ts".to_string(),
        content: "export {};".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host
      .resolve(&from, "./foo.js")
      .expect("./foo.js should resolve");
    let expected = file_set.resolve("/foo.d.ts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn snapshots_preserve_extension_and_load_legacy_paths() {
    let tmp = tempdir().unwrap();
    let store = SnapshotStore {
      base: tmp.path().to_path_buf(),
    };

    let ts = store.path_for("foo.ts");
    let tsx = store.path_for("foo.tsx");
    let d_ts = store.path_for("foo.d.ts");
    assert_ne!(ts, tsx);
    assert_eq!(ts.file_name().unwrap(), "foo.ts.json");
    assert_eq!(tsx.file_name().unwrap(), "foo.tsx.json");
    assert_eq!(d_ts.file_name().unwrap(), "foo.d.ts.json");

    let write_legacy = |id: &str, code: u32| {
      let legacy_path = store.legacy_path_for(id);
      let payload = TscDiagnostics {
        schema_version: Some(TSC_BASELINE_SCHEMA_VERSION),
        metadata: Default::default(),
        diagnostics: vec![crate::tsc::TscDiagnostic {
          code,
          file: None,
          start: 0,
          end: 0,
          category: None,
          message: None,
        }],
        crash: None,
        type_facts: None,
      };
      let json = serde_json::to_string(&payload).unwrap();
      std::fs::write(legacy_path, json).unwrap();
    };

    write_legacy("foo.ts", 1);
    write_legacy("foo.d.ts", 2);

    let loaded = store.load("foo.ts").unwrap();
    assert_eq!(loaded.diagnostics.len(), 1);
    assert_eq!(loaded.diagnostics[0].code, 1);

    let loaded = store.load("foo.d.ts").unwrap();
    assert_eq!(loaded.diagnostics.len(), 1);
    assert_eq!(loaded.diagnostics[0].code, 2);
  }

  #[test]
  fn resolves_scoped_bare_specifier_via_at_types_fallback() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"@scope/pkg\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/@types/scope__pkg/index.d.ts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host
      .resolve(&from, "@scope/pkg")
      .expect("@scope/pkg should resolve");
    let expected = file_set
      .resolve("/node_modules/@types/scope__pkg/index.d.ts")
      .unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_bare_specifier_via_node_modules_d_mts_index() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import { x } from \"foo\";".to_string(),
      },
      VirtualFile {
        name: "/node_modules/foo/index.d.mts".to_string(),
        content: "export const x: number;".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host.resolve(&from, "foo").expect("foo should resolve");
    let expected = file_set.resolve("/node_modules/foo/index.d.mts").unwrap();
    assert_eq!(resolved, expected);
  }

  #[test]
  fn resolves_relative_mjs_specifier_via_d_mts_substitution() {
    let files = vec![
      VirtualFile {
        name: "/a.ts".to_string(),
        content: "import \"./foo.mjs\";".to_string(),
      },
      VirtualFile {
        name: "/foo.d.mts".to_string(),
        content: "export {};".to_string(),
      },
    ];

    let file_set = HarnessFileSet::new(&files);
    let host = HarnessHost::new(file_set.clone(), CompilerOptions::default());

    let from = file_set.resolve("/a.ts").unwrap();
    let resolved = host
      .resolve(&from, "./foo.mjs")
      .expect("./foo.mjs should resolve");
    let expected = file_set.resolve("/foo.d.mts").unwrap();
    assert_eq!(resolved, expected);
  }
}
