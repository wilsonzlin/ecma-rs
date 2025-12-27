use crate::diagnostic_norm::{
  describe, normalize_rust_diagnostics, normalize_tsc_diagnostics, sort_diagnostics,
  within_tolerance, NormalizedDiagnostic,
};
use crate::directives::HarnessOptions;
use crate::discover::{discover_conformance_tests, Filter, Shard, TestCase, DEFAULT_EXTENSIONS};
use crate::expectations::{AppliedExpectation, ExpectationKind, Expectations};
use crate::multifile::normalize_name;
use crate::profile::ProfileBuilder;
use crate::tsc::{TscDiagnostic, TscDiagnostics, TscMetadata, TSC_BASELINE_SCHEMA_VERSION};
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
use typecheck_ts::lib_support::CompilerOptions;
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
  #[serde(default, skip_serializing_if = "is_false")]
  pub from_manifest: bool,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub reason: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub tracking_issue: Option<String>,
}

fn is_false(value: &bool) -> bool {
  !*value
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
  normalized: String,
  key: FileKey,
  content: Arc<str>,
}

#[derive(Clone)]
pub(crate) struct HarnessFileSet {
  files: Vec<HarnessFile>,
  name_to_key: HashMap<String, FileKey>,
  key_to_name: HashMap<FileKey, String>,
}

#[derive(Clone)]
struct PlannedCase {
  case: TestCase,
  expectation: AppliedExpectation,
}

impl HarnessFileSet {
  pub(crate) fn new(files: &[VirtualFile]) -> Self {
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
        normalized,
        key,
        content: Arc::from(files[idx].content.clone()),
      });
    }

    Self {
      files: stored,
      name_to_key,
      key_to_name,
    }
  }

  pub(crate) fn root_keys(&self) -> Vec<FileKey> {
    self.files.iter().map(|f| f.key.clone()).collect()
  }

  pub(crate) fn resolve(&self, normalized: &str) -> Option<FileKey> {
    self.name_to_key.get(normalized).cloned()
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

  pub(crate) fn write_to_dir(&self, dir: &Path) -> std::io::Result<()> {
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

  let tsc_runner = TscRunner::new(opts.node_path.clone());
  let tsc_available = tsc_runner.available();
  let snapshot_store = SnapshotStore::new(&opts.root);
  let compare_mode = resolve_compare_mode(opts.compare, tsc_available, &snapshot_store);

  let job_count = opts.jobs.max(1);
  let tsc_limiter = Arc::new(ConcurrencyLimiter::new(job_count));
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
            &tsc_runner,
            tsc_available,
            &snapshot_store,
            tsc_limiter.clone(),
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

  results.sort_by(|a, b| a.id.cmp(&b.id));
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
  tsc_runner: &TscRunner,
  tsc_available: bool,
  snapshots: &SnapshotStore,
  tsc_limiter: Arc<ConcurrencyLimiter>,
  opts: &ConformanceOptions,
) -> TestResult {
  let (tx, rx) = mpsc::channel();
  let span = info_span!("test_case", test_id = %case.id);
  let _enter = span.enter();
  let span_for_thread = span.clone();
  let cloned_runner = tsc_runner.clone();
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
      cloned_runner,
      tsc_available,
      cloned_snapshots,
      span_tolerance,
      update_snapshots,
      collect_query_stats,
      tsc_limiter,
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
  tsc_runner: TscRunner,
  tsc_available: bool,
  snapshots: SnapshotStore,
  span_tolerance: u32,
  update_snapshots: bool,
  collect_query_stats: bool,
  tsc_limiter: Arc<ConcurrencyLimiter>,
) -> TestResult {
  let start = Instant::now();
  if let Some(delay) = harness_sleep_for_case(&case.id) {
    std::thread::sleep(delay);
  }
  let notes = case.notes.clone();
  let file_set = HarnessFileSet::new(&case.deduped_files);
  let harness_options = case.options.clone();

  let (rust, query_stats) = run_rust_with_profile(&file_set, &harness_options, collect_query_stats);
  let tsc_options = harness_options.to_tsc_options_map();
  let options = build_test_options(&harness_options, &tsc_options);

  let mut tsc_raw: Option<Vec<TscDiagnostic>> = None;
  let tsc = match compare_mode {
    CompareMode::None => EngineDiagnostics::skipped(Some("comparison disabled".to_string())),
    CompareMode::Tsc => {
      if tsc_available {
        let (diag, raw) = run_tsc_with_raw(&tsc_runner, &file_set, &tsc_options, &tsc_limiter);
        tsc_raw = raw;
        diag
      } else {
        EngineDiagnostics::crashed("tsc unavailable")
      }
    }
    CompareMode::Snapshot => {
      if update_snapshots {
        if tsc_available {
          let (diag, raw) = run_tsc_with_raw(&tsc_runner, &file_set, &tsc_options, &tsc_limiter);
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
  runner: &TscRunner,
  file_set: &HarnessFileSet,
  options: &Map<String, Value>,
  limiter: &ConcurrencyLimiter,
) -> (EngineDiagnostics, Option<Vec<TscDiagnostic>>) {
  let _permit = limiter.acquire();
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
  compiler_options: CompilerOptions,
}

impl HarnessHost {
  fn new(files: HarnessFileSet, compiler_options: CompilerOptions) -> Self {
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

  fn compiler_options(&self) -> CompilerOptions {
    self.compiler_options.clone()
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    let is_relative = specifier.starts_with("./") || specifier.starts_with("../");
    if !is_relative {
      let normalized = normalize_name(specifier);
      return self.files.resolve(&normalized);
    }

    let base = self.files.name_for_key(from)?;
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
    options: &Map<String, Value>,
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
      if !options.is_empty() {
        let env = serde_json::to_string(options)
          .map_err(|err| format!("serialize harness options: {err}"))?;
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
    path.set_extension("json");
    path
  }

  fn load(&self, id: &str) -> std::io::Result<Vec<TscDiagnostic>> {
    let path = self.path_for(id);
    let data = read_utf8_file(&path)?;
    let parsed: TscDiagnostics = serde_json::from_str(&data)?;
    Ok(parsed.diagnostics)
  }

  fn save(&self, id: &str, diagnostics: &[TscDiagnostic]) -> std::io::Result<()> {
    let path = self.path_for(id);
    if let Some(parent) = path.parent() {
      std::fs::create_dir_all(parent)?;
    }

    let payload = TscDiagnostics {
      schema_version: Some(TSC_BASELINE_SCHEMA_VERSION),
      metadata: TscMetadata::default(),
      diagnostics: diagnostics.to_vec(),
      type_facts: None,
      crash: None,
    };
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
}
