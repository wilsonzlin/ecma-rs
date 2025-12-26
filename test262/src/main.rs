use anyhow::{anyhow, bail, Context, Result};
use clap::command;
use clap::Parser;
use clap::ValueEnum;
use diagnostics::render::{render_diagnostic, SourceProvider};
use diagnostics::{host_error, Diagnostic, FileId};
use globset::Glob;
use parse_js::{Dialect, ParseOptions, SourceType};
use rayon::prelude::*;
use regex::Regex;
use serde::{Deserialize, Serialize};
use std::fs;
use std::io::{self, BufWriter, Write};
use std::path::{Path, PathBuf};

const REPORT_SCHEMA_VERSION: u32 = 1;

fn main() {
  if let Err(err) = try_main() {
    eprintln!("{err}");
    std::process::exit(1);
  }
}

fn try_main() -> Result<()> {
  let cli = Cli::parse();

  let expectations = match &cli.manifest {
    Some(path) => Expectations::from_path(path)?,
    None => Expectations::empty(),
  };

  let mut cases = discover_cases(&cli.data_dir)?;
  let total_cases = cases.len();
  if let Some(shard) = cli.shard {
    let filtered = apply_shard(cases, shard);
    cases = filtered;
    if cases.is_empty() {
      bail!(
        "shard {}/{} matched no tests out of {total_cases}",
        shard.index + 1,
        shard.total
      );
    }
    eprintln!(
      "Running shard {}/{}: {} of {} tests",
      shard.index + 1,
      shard.total,
      cases.len(),
      total_cases
    );
  }

  let mut results = run_cases(&cases, &expectations);
  results.sort_by(|a, b| a.id.cmp(&b.id));

  let summary = summarize(&results);
  let report = ReportRef::new(&summary, &results);

  if let Some(path) = &cli.report_path {
    write_report(path, &report)?;
    eprintln!("Wrote test262 parser report to {}", path.display());
  }

  if cli.json {
    let stdout = io::stdout();
    let mut handle = stdout.lock();
    serde_json::to_writer_pretty(&mut handle, &report).context("write JSON report to stdout")?;
    writeln!(handle).ok();
  } else {
    print_human_summary(&summary);
  }

  print_unexpected_details(&results);

  if summary.should_fail(cli.fail_on) {
    std::process::exit(1);
  }

  Ok(())
}

#[derive(Parser, Debug)]
#[command(version)]
struct Cli {
  /// Path to tc39/test262-parser-tests repository folder.
  #[arg(long, default_value = "test262/data")]
  data_dir: PathBuf,

  /// Optional manifest describing expected failures or skips.
  #[arg(long)]
  manifest: Option<PathBuf>,

  /// Emit JSON to stdout.
  #[arg(long)]
  json: bool,

  /// Also write the JSON report to the given path.
  #[arg(long, value_name = "PATH")]
  report_path: Option<PathBuf>,

  /// Run only the given shard (format: <index>/<total>).
  #[arg(long)]
  shard: Option<Shard>,

  /// Control which mismatches cause a non-zero exit code.
  #[arg(long, default_value_t = FailOn::New, value_enum)]
  fail_on: FailOn,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
pub enum FailOn {
  /// Non-zero on any mismatch.
  All,
  /// Non-zero only for mismatches not covered by manifest (default).
  New,
  /// Always zero.
  None,
}

impl Default for FailOn {
  fn default() -> Self {
    FailOn::New
  }
}

impl FailOn {
  pub fn should_fail(&self, unexpected_mismatches: usize, total_mismatches: usize) -> bool {
    match self {
      FailOn::All => total_mismatches > 0,
      FailOn::New => unexpected_mismatches > 0,
      FailOn::None => false,
    }
  }
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum TestCategory {
  Pass,
  PassExplicit,
  Fail,
  Early,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum ExpectedOutcome {
  Pass,
  Fail,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum TestOutcome {
  Passed,
  Failed,
  Skipped,
}

#[derive(Debug, Clone, Copy, Serialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
enum SourceMode {
  Script,
  Module,
}

impl SourceMode {
  fn from_path(path: &Path) -> Self {
    let name = path
      .file_name()
      .and_then(|name| name.to_str())
      .unwrap_or_default();
    if name.contains(".module.") {
      SourceMode::Module
    } else {
      SourceMode::Script
    }
  }

  fn to_parse_options(self) -> ParseOptions {
    ParseOptions {
      dialect: Dialect::Js,
      source_type: match self {
        SourceMode::Script => SourceType::Script,
        SourceMode::Module => SourceType::Module,
      },
    }
  }
}

#[derive(Debug, Clone)]
struct TestCase {
  id: String,
  path: PathBuf,
  category: TestCategory,
  expected: ExpectedOutcome,
  source_type: SourceMode,
}

#[derive(Debug, Clone, Serialize)]
struct TestResult {
  id: String,
  path: String,
  category: TestCategory,
  source_type: SourceMode,
  expected: ExpectedOutcome,
  outcome: TestOutcome,
  #[serde(skip_serializing_if = "Option::is_none")]
  diagnostic: Option<DiagnosticSummary>,
  expectation: ExpectationOutcome,
  #[serde(default, skip_serializing_if = "is_false")]
  mismatched: bool,
  #[serde(default, skip_serializing_if = "is_false")]
  expected_mismatch: bool,
  #[serde(default, skip_serializing_if = "is_false")]
  flaky: bool,
  #[serde(skip)]
  source: Option<String>,
  #[serde(skip)]
  raw_diagnostic: Option<Diagnostic>,
}

fn is_false(value: &bool) -> bool {
  !*value
}

#[derive(Debug, Clone, Serialize)]
struct DiagnosticSummary {
  code: String,
  message: String,
  span: SpanSummary,
  #[serde(default, skip_serializing_if = "Vec::is_empty")]
  notes: Vec<String>,
}

#[derive(Debug, Clone, Serialize)]
struct SpanSummary {
  start: u32,
  end: u32,
}

#[derive(Debug, Clone, Serialize)]
struct ExpectationOutcome {
  expectation: ExpectationKind,
  #[serde(default)]
  expected: bool,
  #[serde(default, skip_serializing_if = "is_false")]
  from_manifest: bool,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  reason: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  tracking_issue: Option<String>,
}

#[derive(Debug, Clone, Serialize, Default)]
struct MismatchSummary {
  expected: usize,
  unexpected: usize,
  flaky: usize,
}

impl MismatchSummary {
  fn total(&self) -> usize {
    self.expected + self.unexpected + self.flaky
  }
}

#[derive(Debug, Clone, Serialize, Default)]
struct Summary {
  total: usize,
  passed: usize,
  failed: usize,
  skipped: usize,
  #[serde(skip_serializing_if = "Option::is_none")]
  mismatches: Option<MismatchSummary>,
}

impl Summary {
  fn should_fail(&self, fail_on: FailOn) -> bool {
    let mismatches = self.mismatches.as_ref().map(|m| m.total()).unwrap_or(0);
    let unexpected = self.mismatches.as_ref().map(|m| m.unexpected).unwrap_or(0);
    fail_on.should_fail(unexpected, mismatches)
  }
}

#[derive(Debug, Serialize)]
struct ReportRef<'a> {
  schema_version: u32,
  summary: &'a Summary,
  results: &'a [TestResult],
}

impl<'a> ReportRef<'a> {
  fn new(summary: &'a Summary, results: &'a [TestResult]) -> Self {
    Self {
      schema_version: REPORT_SCHEMA_VERSION,
      summary,
      results,
    }
  }
}

#[derive(Debug, Clone, Copy)]
struct Shard {
  index: usize,
  total: usize,
}

impl Shard {
  fn includes(&self, idx: usize) -> bool {
    idx % self.total == self.index
  }
}

impl std::str::FromStr for Shard {
  type Err = String;

  fn from_str(raw: &str) -> std::result::Result<Self, Self::Err> {
    let Some((index_raw, total_raw)) = raw.split_once('/') else {
      return Err("shard must be in the form <index>/<total>".into());
    };
    let index: usize = index_raw
      .parse()
      .map_err(|err| format!("invalid shard index `{index_raw}`: {err}"))?;
    let total: usize = total_raw
      .parse()
      .map_err(|err| format!("invalid shard total `{total_raw}`: {err}"))?;
    if total == 0 {
      return Err("shard total must be greater than zero".into());
    }
    if index >= total {
      return Err(format!(
        "shard index must be less than total ({} >= {})",
        index, total
      ));
    }

    Ok(Self { index, total })
  }
}

fn discover_cases(data_dir: &Path) -> Result<Vec<TestCase>> {
  if !data_dir.exists() {
    bail!(
      "test262 parser corpus not found at {} (did you update submodules?)",
      data_dir.display()
    );
  }

  let mut cases = Vec::new();
  for (dir, category, expected) in [
    ("pass", TestCategory::Pass, ExpectedOutcome::Pass),
    (
      "pass-explicit",
      TestCategory::PassExplicit,
      ExpectedOutcome::Pass,
    ),
    ("fail", TestCategory::Fail, ExpectedOutcome::Fail),
    ("early", TestCategory::Early, ExpectedOutcome::Fail),
  ] {
    cases.extend(collect_cases(data_dir, dir, category, expected)?);
  }

  if cases.is_empty() {
    bail!("no test cases discovered under {}", data_dir.display());
  }

  cases.sort_by(|a, b| a.id.cmp(&b.id));

  Ok(cases)
}

fn collect_cases(
  data_dir: &Path,
  subdir: &str,
  category: TestCategory,
  expected: ExpectedOutcome,
) -> Result<Vec<TestCase>> {
  let dir = data_dir.join(subdir);
  if !dir.is_dir() {
    bail!("expected directory {} under {}", subdir, data_dir.display());
  }

  let mut entries = fs::read_dir(&dir)
    .with_context(|| format!("read directory {}", dir.display()))?
    .collect::<Result<Vec<_>, _>>()
    .with_context(|| format!("collect entries under {}", dir.display()))?;

  entries.sort_by(|a, b| a.file_name().cmp(&b.file_name()));

  let mut cases = Vec::new();
  for entry in entries {
    let metadata = entry
      .metadata()
      .with_context(|| format!("stat {}", entry.path().display()))?;
    if !metadata.is_file() {
      continue;
    }

    if entry.path().extension().and_then(|ext| ext.to_str()) != Some("js") {
      continue;
    }

    let id = normalize_path(Path::new(subdir).join(entry.file_name()));
    cases.push(TestCase {
      id: id.clone(),
      path: entry.path(),
      category,
      expected,
      source_type: SourceMode::from_path(&entry.path()),
    });
  }

  Ok(cases)
}

fn normalize_path(path: impl AsRef<Path>) -> String {
  path.as_ref().to_string_lossy().replace('\\', "/")
}

fn apply_shard(cases: Vec<TestCase>, shard: Shard) -> Vec<TestCase> {
  cases
    .into_iter()
    .enumerate()
    .filter(|(idx, _)| shard.includes(*idx))
    .map(|(_, case)| case)
    .collect()
}

fn run_cases(cases: &[TestCase], expectations: &Expectations) -> Vec<TestResult> {
  cases
    .par_iter()
    .map(|case| {
      let expectation = expectations.lookup(&case.id);
      run_single_case(case, expectation)
    })
    .collect()
}

fn run_single_case(case: &TestCase, expectation: AppliedExpectation) -> TestResult {
  if expectation.expectation.kind == ExpectationKind::Skip {
    return TestResult {
      id: case.id.clone(),
      path: case.id.clone(),
      category: case.category,
      source_type: case.source_type,
      expected: case.expected,
      outcome: TestOutcome::Skipped,
      diagnostic: None,
      expectation: expectation_outcome(expectation, false),
      mismatched: false,
      expected_mismatch: false,
      flaky: false,
      source: None,
      raw_diagnostic: None,
    };
  }

  let source = match fs::read_to_string(&case.path) {
    Ok(src) => src,
    Err(err) => {
      let diagnostic = host_error(None, format!("read {}: {err}", case.path.display()));
      let mismatched = case.expected == ExpectedOutcome::Pass;
      let expectation = expectation_outcome(expectation, mismatched);
      let expected_mismatch = mismatched && expectation.expectation == ExpectationKind::Xfail;
      let flaky = mismatched && expectation.expectation == ExpectationKind::Flaky;
      return TestResult {
        id: case.id.clone(),
        path: case.id.clone(),
        category: case.category,
        source_type: case.source_type,
        expected: case.expected,
        outcome: TestOutcome::Failed,
        diagnostic: Some(summarize_diagnostic(&diagnostic)),
        expectation,
        mismatched,
        expected_mismatch,
        flaky,
        source: None,
        raw_diagnostic: Some(diagnostic),
      };
    }
  };

  let parse_opts = case.source_type.to_parse_options();
  let parsed = parse_js::parse_with_options(&source, parse_opts);
  let diagnostic = parsed.err().map(|err| err.to_diagnostic(FileId(0)));

  let outcome = if diagnostic.is_some() {
    TestOutcome::Failed
  } else {
    TestOutcome::Passed
  };

  let mismatched = match case.expected {
    ExpectedOutcome::Pass => outcome == TestOutcome::Failed,
    ExpectedOutcome::Fail => outcome == TestOutcome::Passed,
  };

  let raw_diagnostic = if mismatched { diagnostic.clone() } else { None };
  let diagnostic_summary = diagnostic.as_ref().map(summarize_diagnostic);

  TestResult {
    id: case.id.clone(),
    path: case.id.clone(),
    category: case.category,
    source_type: case.source_type,
    expected: case.expected,
    outcome,
    diagnostic: diagnostic_summary,
    expectation: expectation_outcome(expectation.clone(), mismatched),
    mismatched,
    expected_mismatch: mismatched && expectation.expectation.kind == ExpectationKind::Xfail,
    flaky: mismatched && expectation.expectation.kind == ExpectationKind::Flaky,
    source: if mismatched && diagnostic.is_some() {
      Some(source)
    } else {
      None
    },
    raw_diagnostic,
  }
}

fn summarize_diagnostic(diagnostic: &Diagnostic) -> DiagnosticSummary {
  DiagnosticSummary {
    code: diagnostic.code.as_str().to_string(),
    message: diagnostic.message.clone(),
    span: SpanSummary {
      start: diagnostic.primary.range.start,
      end: diagnostic.primary.range.end,
    },
    notes: diagnostic.notes.clone(),
  }
}

fn summarize(results: &[TestResult]) -> Summary {
  let mut summary = Summary::default();
  let mut mismatches = MismatchSummary::default();

  for result in results {
    summary.total += 1;
    match result.outcome {
      TestOutcome::Passed => summary.passed += 1,
      TestOutcome::Failed => summary.failed += 1,
      TestOutcome::Skipped => summary.skipped += 1,
    }

    if result.mismatched {
      if result.flaky {
        mismatches.flaky += 1;
      } else if result.expected_mismatch {
        mismatches.expected += 1;
      } else {
        mismatches.unexpected += 1;
      }
    }
  }

  if mismatches.total() > 0 {
    summary.mismatches = Some(mismatches);
  }

  summary
}

fn write_report(path: &Path, report: &ReportRef<'_>) -> Result<()> {
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent).with_context(|| format!("create {}", parent.display()))?;
  }

  let file = fs::File::create(path).with_context(|| format!("create {}", path.display()))?;
  let mut writer = BufWriter::new(file);
  serde_json::to_writer_pretty(&mut writer, report)
    .with_context(|| format!("write report to {}", path.display()))?;
  writer.flush().ok();

  Ok(())
}

fn print_human_summary(summary: &Summary) {
  println!(
    "test262 parser tests: total={}, passed={}, failed={}, skipped={}",
    summary.total, summary.passed, summary.failed, summary.skipped
  );

  if let Some(mismatches) = &summary.mismatches {
    println!(
      "mismatches: unexpected={}, expected={}, flaky={}",
      mismatches.unexpected, mismatches.expected, mismatches.flaky
    );
  }
}

fn print_unexpected_details(results: &[TestResult]) {
  for result in results
    .iter()
    .filter(|r| r.mismatched && !r.expected_mismatch && !r.flaky)
  {
    match result.expected {
      ExpectedOutcome::Pass => {
        if let (Some(diag), Some(source)) = (&result.raw_diagnostic, &result.source) {
          let provider = SingleFileSource {
            file_name: &result.id,
            text: source,
          };
          eprintln!(
            "Unexpected failure in {}:\n{}",
            result.id,
            render_diagnostic(&provider, diag)
          );
        } else {
          eprintln!(
            "Unexpected failure in {} (no diagnostic available)",
            result.id
          );
        }
      }
      ExpectedOutcome::Fail => {
        eprintln!(
          "Unexpected pass: {} was expected to fail parsing",
          result.id
        );
      }
    }
  }
}

struct SingleFileSource<'a> {
  file_name: &'a str,
  text: &'a str,
}

impl SourceProvider for SingleFileSource<'_> {
  fn file_name(&self, _file: FileId) -> Option<&str> {
    Some(self.file_name)
  }

  fn file_text(&self, _file: FileId) -> Option<&str> {
    Some(self.text)
  }
}

#[derive(Debug, Clone, Copy, Serialize, Deserialize, PartialEq, Eq)]
#[serde(rename_all = "snake_case")]
pub enum ExpectationKind {
  Pass,
  Skip,
  Xfail,
  Flaky,
}

impl Default for ExpectationKind {
  fn default() -> Self {
    ExpectationKind::Pass
  }
}

#[derive(Debug, Clone, Serialize, Deserialize, PartialEq, Eq, Default)]
pub struct Expectation {
  #[serde(default)]
  pub kind: ExpectationKind,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub reason: Option<String>,
  #[serde(default, skip_serializing_if = "Option::is_none")]
  pub tracking_issue: Option<String>,
}

#[derive(Debug, Clone, Default)]
pub struct AppliedExpectation {
  pub expectation: Expectation,
  pub from_manifest: bool,
}

impl AppliedExpectation {
  pub fn matches(&self, mismatched: bool) -> bool {
    match self.expectation.kind {
      ExpectationKind::Pass => !mismatched,
      ExpectationKind::Skip => true,
      ExpectationKind::Xfail | ExpectationKind::Flaky => mismatched,
    }
  }
}

#[derive(Debug, Clone, Default)]
pub struct Expectations {
  exact: Vec<Entry>,
  globs: Vec<Entry>,
  regexes: Vec<Entry>,
}

impl Expectations {
  pub fn empty() -> Self {
    Self::default()
  }

  pub fn from_path(path: &Path) -> Result<Self> {
    let raw =
      fs::read_to_string(path).with_context(|| format!("read manifest {}", path.display()))?;
    Self::from_str(&raw).map_err(|err| anyhow!("{}: {err}", path.display()))
  }

  pub fn from_str(raw: &str) -> Result<Self> {
    let manifest = match toml::from_str::<RawManifest>(raw) {
      Ok(manifest) => manifest,
      Err(toml_err) => serde_json::from_str::<RawManifest>(raw).map_err(|json_err| {
        anyhow!("failed to parse manifest as TOML ({toml_err}) or JSON ({json_err})")
      })?,
    };

    Self::from_manifest(manifest)
  }

  pub fn lookup(&self, id: &str) -> AppliedExpectation {
    if let Some(found) = self.lookup_in(&self.exact, id) {
      return found;
    }

    if let Some(found) = self.lookup_in(&self.globs, id) {
      return found;
    }

    if let Some(found) = self.lookup_in(&self.regexes, id) {
      return found;
    }

    AppliedExpectation::default()
  }

  fn lookup_in(&self, entries: &[Entry], id: &str) -> Option<AppliedExpectation> {
    for entry in entries {
      if entry.matches(id) {
        return Some(AppliedExpectation {
          expectation: entry.expectation.clone(),
          from_manifest: true,
        });
      }
    }

    None
  }

  fn from_manifest(manifest: RawManifest) -> Result<Self> {
    let mut expectations = Expectations::default();
    for entry in manifest.expectations {
      let matcher = entry.matcher()?;
      let expectation = Expectation {
        kind: entry
          .status
          .ok_or_else(|| anyhow!("manifest entry missing `status`"))?,
        reason: entry.reason,
        tracking_issue: entry.tracking_issue,
      };

      match matcher {
        Matcher::Exact(pattern) => expectations.exact.push(Entry {
          matcher: Matcher::Exact(pattern),
          expectation,
        }),
        Matcher::Glob(pattern) => expectations.globs.push(Entry {
          matcher: Matcher::Glob(pattern),
          expectation,
        }),
        Matcher::Regex(pattern) => expectations.regexes.push(Entry {
          matcher: Matcher::Regex(pattern),
          expectation,
        }),
      }
    }

    Ok(expectations)
  }
}

#[derive(Debug, Clone)]
struct Entry {
  matcher: Matcher,
  expectation: Expectation,
}

impl Entry {
  fn matches(&self, id: &str) -> bool {
    self.matcher.matches(id)
  }
}

#[derive(Debug, Clone)]
enum Matcher {
  Exact(String),
  Glob(globset::GlobMatcher),
  Regex(Regex),
}

impl Matcher {
  fn matches(&self, id: &str) -> bool {
    match self {
      Matcher::Exact(pattern) => pattern == id,
      Matcher::Glob(glob) => glob.is_match(id),
      Matcher::Regex(re) => re.is_match(id),
    }
  }
}

#[derive(Debug, Clone, Deserialize)]
struct RawManifest {
  #[serde(default)]
  expectations: Vec<RawEntry>,
}

#[derive(Debug, Clone, Deserialize)]
struct RawEntry {
  id: Option<String>,
  glob: Option<String>,
  regex: Option<String>,
  #[serde(alias = "expectation")]
  status: Option<ExpectationKind>,
  reason: Option<String>,
  tracking_issue: Option<String>,
}

impl RawEntry {
  fn matcher(&self) -> Result<Matcher> {
    let mut seen = 0;
    if self.id.is_some() {
      seen += 1;
    }
    if self.glob.is_some() {
      seen += 1;
    }
    if self.regex.is_some() {
      seen += 1;
    }

    if seen == 0 {
      bail!("manifest entry missing `id`/`glob`/`regex`");
    }

    if seen > 1 {
      bail!("manifest entry must specify exactly one of `id`/`glob`/`regex`");
    }

    if let Some(id) = &self.id {
      return Ok(Matcher::Exact(id.clone()));
    }

    if let Some(glob) = &self.glob {
      let compiled = Glob::new(glob)
        .map_err(|err| anyhow!("invalid glob '{glob}': {err}"))?
        .compile_matcher();
      return Ok(Matcher::Glob(compiled));
    }

    let regex = self.regex.as_ref().expect("validated regex presence");
    let compiled = Regex::new(regex).map_err(|err| anyhow!("invalid regex '{regex}': {err}"))?;

    Ok(Matcher::Regex(compiled))
  }
}

fn expectation_outcome(expectation: AppliedExpectation, mismatched: bool) -> ExpectationOutcome {
  ExpectationOutcome {
    expected: expectation.matches(mismatched),
    expectation: expectation.expectation.kind,
    from_manifest: expectation.from_manifest,
    reason: expectation.expectation.reason,
    tracking_issue: expectation.expectation.tracking_issue,
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn write_case(root: &Path, subdir: &str, name: &str, contents: &str) {
    let dir = root.join(subdir);
    fs::create_dir_all(&dir).expect("created test directory");
    fs::write(dir.join(name), contents).expect("wrote test case");
  }

  fn ensure_dirs(root: &Path) {
    for dir in ["pass", "pass-explicit", "fail", "early"] {
      fs::create_dir_all(root.join(dir)).expect("created data dir");
    }
  }

  #[test]
  fn manifest_prefers_exact_then_glob_then_regex() {
    let manifest = r#"
[[expectations]]
glob = "a/**"
status = "xfail"

[[expectations]]
regex = "a/.*"
status = "flaky"

[[expectations]]
id = "a/b/c.js"
status = "skip"
    "#;

    let expectations = Expectations::from_str(manifest).expect("manifest parsed");
    let applied = expectations.lookup("a/b/c.js");
    assert_eq!(applied.expectation.kind, ExpectationKind::Skip);
  }

  #[test]
  fn sharding_is_deterministic() {
    let temp = tempfile::tempdir().unwrap();
    ensure_dirs(temp.path());
    write_case(temp.path(), "pass", "b.js", "let b = 1;");
    write_case(temp.path(), "pass", "a.js", "let a = 1;");

    let cases = discover_cases(temp.path()).expect("cases discovered");
    let shard = Shard { index: 0, total: 2 };

    let first = apply_shard(cases.clone(), shard);
    let second = apply_shard(cases, shard);

    let ids_one: Vec<_> = first.iter().map(|c| c.id.clone()).collect();
    let ids_two: Vec<_> = second.iter().map(|c| c.id.clone()).collect();
    assert_eq!(ids_one, ids_two);
  }

  #[test]
  fn mismatches_are_reported_in_json() {
    let temp = tempfile::tempdir().unwrap();
    ensure_dirs(temp.path());
    write_case(temp.path(), "pass", "bad.js", "let =;");

    let expectations = Expectations::empty();
    let mut results = run_cases(&discover_cases(temp.path()).unwrap(), &expectations);
    results.sort_by(|a, b| a.id.cmp(&b.id));
    let summary = summarize(&results);
    let report = ReportRef::new(&summary, &results);
    let json = serde_json::to_string(&report).expect("serialize report");

    assert!(json.contains("\"diagnostic\""));
    assert!(json.contains("\"pass/bad.js\""));
  }

  #[test]
  fn manifest_covers_known_failures() {
    let temp = tempfile::tempdir().unwrap();
    ensure_dirs(temp.path());
    write_case(temp.path(), "pass", "bad.js", "let =;");
    let manifest = r#"
[[expectations]]
id = "pass/bad.js"
status = "xfail"
reason = "known parse gap"
    "#;
    let expectations = Expectations::from_str(manifest).unwrap();
    let mut results = run_cases(&discover_cases(temp.path()).unwrap(), &expectations);
    results.sort_by(|a, b| a.id.cmp(&b.id));
    let summary = summarize(&results);
    let mismatches = summary.mismatches.expect("mismatch summary present");
    assert_eq!(mismatches.expected, 1);
    assert_eq!(mismatches.unexpected, 0);
  }
}
