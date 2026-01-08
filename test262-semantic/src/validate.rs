use anyhow::{anyhow, bail, Context, Result};
use clap::{Args, ValueEnum};
use conformance_harness::ExpectationKind;
use globset::Glob;
use regex::Regex;
use serde::Deserialize;
use std::collections::BTreeSet;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use test262_semantic::discover::{discover_tests, DiscoveredTest};
use test262_semantic::suite::{load_builtin_suite, load_suite_from_path, Suite};

const DEFAULT_TEST262_DIR: &str = "test262-semantic/data";

#[derive(Args, Debug)]
pub struct ValidateArgs {
  /// Path to a local checkout of the tc39/test262 repository.
  #[arg(long, value_name = "DIR", default_value = DEFAULT_TEST262_DIR)]
  pub test262_dir: PathBuf,

  /// Built-in curated suite name to validate (e.g. `smoke`); can be passed multiple times.
  ///
  /// If no suites are provided, `validate` defaults to validating every suite file under
  /// `test262-semantic/suites`.
  #[arg(long, value_name = "NAME")]
  pub suite: Vec<String>,

  /// Path to a suite file (TOML/JSON); can be passed multiple times.
  #[arg(long, value_name = "PATH")]
  pub suite_path: Vec<PathBuf>,

  /// Optional expectations manifest file (TOML/JSON).
  #[arg(long, value_name = "PATH")]
  pub manifest: Option<PathBuf>,

  /// How to treat suite include globs that match zero tests.
  #[arg(long, value_enum, default_value_t = ZeroMatchBehavior::Error)]
  pub include_glob_zero: ZeroMatchBehavior,

  /// How to treat suite exclude globs that match zero tests.
  #[arg(long, value_enum, default_value_t = ZeroMatchBehavior::Warn)]
  pub exclude_glob_zero: ZeroMatchBehavior,

  /// Print match counts for manifest glob/regex entries (useful for auditing).
  #[arg(long)]
  pub manifest_counts: bool,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, ValueEnum)]
pub enum ZeroMatchBehavior {
  Error,
  Warn,
  Ignore,
}

#[derive(Default, Debug)]
struct ValidationReport {
  errors: Vec<String>,
  warnings: Vec<String>,
  notes: Vec<String>,
}

impl ValidationReport {
  fn push_issue(&mut self, behavior: ZeroMatchBehavior, msg: String) {
    match behavior {
      ZeroMatchBehavior::Error => self.errors.push(msg),
      ZeroMatchBehavior::Warn => self.warnings.push(msg),
      ZeroMatchBehavior::Ignore => {}
    }
  }

  fn extend(&mut self, other: ValidationReport) {
    self.errors.extend(other.errors);
    self.warnings.extend(other.warnings);
    self.notes.extend(other.notes);
  }

  fn sort_deterministic(&mut self) {
    self.errors.sort();
    self.warnings.sort();
    self.notes.sort();
  }
}

pub fn run_cli(args: ValidateArgs) -> Result<ExitCode> {
  let discovered = discover_tests(&args.test262_dir)?;
  let discovered_ids = discovered
    .iter()
    .map(|test| test.id.clone())
    .collect::<BTreeSet<_>>();

  let suites = load_suites(&args)?;
  if suites.is_empty() {
    bail!("no suite files selected");
  }

  let mut report = ValidationReport::default();

  for suite in suites {
    report.extend(validate_suite(
      &suite,
      &discovered,
      &discovered_ids,
      &args,
    ));
  }

  if let Some(manifest_path) = &args.manifest {
    let manifest = RawManifest::from_path(manifest_path)?;
    report.extend(validate_manifest(
      &manifest,
      &discovered,
      &discovered_ids,
      args.manifest_counts,
    ));
  }

  report.sort_deterministic();

  for line in &report.notes {
    println!("{line}");
  }
  for line in &report.warnings {
    eprintln!("warning: {line}");
  }
  for line in &report.errors {
    eprintln!("error: {line}");
  }

  Ok(if report.errors.is_empty() {
    ExitCode::SUCCESS
  } else {
    ExitCode::FAILURE
  })
}

#[derive(Debug)]
struct SuiteSpec {
  label: String,
  suite: Suite,
}

fn load_suites(args: &ValidateArgs) -> Result<Vec<SuiteSpec>> {
  let mut out = Vec::new();

  for name in &args.suite {
    let suite = load_builtin_suite(name)?;
    out.push(SuiteSpec {
      label: format!("suite {name:?}"),
      suite,
    });
  }

  for path in &args.suite_path {
    let suite = load_suite_from_path(path)?;
    out.push(SuiteSpec {
      label: format!("suite {}", path.display()),
      suite,
    });
  }

  if !out.is_empty() {
    return Ok(out);
  }

  // No suites were explicitly passed; validate all built-in suites.
  let suite_dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("suites");
  let entries = fs::read_dir(&suite_dir)
    .with_context(|| format!("read built-in suite directory {}", suite_dir.display()))?;

  let mut names = Vec::new();
  for entry in entries {
    let entry = entry?;
    if !entry.file_type()?.is_file() {
      continue;
    }
    let path = entry.path();
    if path.extension().and_then(|ext| ext.to_str()) != Some("toml") {
      continue;
    }
    if let Some(name) = path.file_stem().and_then(|stem| stem.to_str()) {
      names.push(name.to_string());
    }
  }

  names.sort();
  names.dedup();

  for name in names {
    let suite = load_builtin_suite(&name)?;
    out.push(SuiteSpec {
      label: format!("suite {name:?}"),
      suite,
    });
  }

  Ok(out)
}

fn validate_suite(
  suite: &SuiteSpec,
  discovered: &[DiscoveredTest],
  discovered_ids: &BTreeSet<String>,
  args: &ValidateArgs,
) -> ValidationReport {
  let mut report = ValidationReport::default();

  let include_matchers = compile_globs(&suite.label, "include", &suite.suite.include, &mut report);
  let exclude_matchers = compile_globs(&suite.label, "exclude", &suite.suite.exclude, &mut report);

  // Per-glob match counts (to catch stale patterns that match 0 tests).
  for (pattern, matcher) in &include_matchers {
    let count = discovered.iter().filter(|t| matcher.is_match(&t.id)).count();
    if count == 0 {
      report.push_issue(
        args.include_glob_zero,
        format!("{} include glob {pattern:?} matched 0 tests", suite.label),
      );
    }
  }
  for (pattern, matcher) in &exclude_matchers {
    let count = discovered.iter().filter(|t| matcher.is_match(&t.id)).count();
    if count == 0 {
      report.push_issue(
        args.exclude_glob_zero,
        format!("{} exclude glob {pattern:?} matched 0 tests", suite.label),
      );
    }
  }

  // Validate explicit ids and compute selected set.
  let mut selected = BTreeSet::<String>::new();
  let mut missing_ids = Vec::<String>::new();
  for id in &suite.suite.tests {
    if discovered_ids.contains(id) {
      selected.insert(id.clone());
    } else {
      missing_ids.push(id.clone());
    }
  }
  missing_ids.sort();
  missing_ids.dedup();
  for id in missing_ids {
    report
      .errors
      .push(format!("{} references missing test id {id:?}", suite.label));
  }

  if !include_matchers.is_empty() {
    for test in discovered {
      if include_matchers.iter().any(|(_, matcher)| matcher.is_match(&test.id)) {
        selected.insert(test.id.clone());
      }
    }
  }

  if !exclude_matchers.is_empty() {
    selected.retain(|id| !exclude_matchers.iter().any(|(_, matcher)| matcher.is_match(id)));
  }

  if selected.is_empty() {
    report.errors.push(format!("{} selected 0 tests", suite.label));
  }

  report
}

fn compile_globs(
  suite_label: &str,
  label: &str,
  patterns: &[String],
  report: &mut ValidationReport,
) -> Vec<(String, globset::GlobMatcher)> {
  let mut out = Vec::new();
  for pattern in patterns {
    match Glob::new(pattern) {
      Ok(glob) => out.push((pattern.clone(), glob.compile_matcher())),
      Err(err) => report.errors.push(format!(
        "{suite_label} has invalid {label} glob {pattern:?}: {err}"
      )),
    }
  }
  out
}

#[derive(Debug, Deserialize)]
struct RawManifest {
  #[serde(default)]
  expectations: Vec<RawEntry>,
}

impl RawManifest {
  fn from_path(path: &Path) -> Result<Self> {
    let raw = fs::read_to_string(path).with_context(|| format!("read {}", path.display()))?;
    match toml::from_str::<RawManifest>(&raw) {
      Ok(manifest) => Ok(manifest),
      Err(toml_err) => serde_json::from_str::<RawManifest>(&raw).map_err(|json_err| {
        anyhow!(
          "{}: failed to parse manifest as TOML ({toml_err}) or JSON ({json_err})",
          path.display()
        )
      }),
    }
  }
}

#[derive(Debug, Deserialize)]
struct RawEntry {
  id: Option<String>,
  glob: Option<String>,
  regex: Option<String>,
  #[serde(alias = "expectation")]
  status: Option<ExpectationKind>,
}

fn validate_manifest(
  manifest: &RawManifest,
  discovered: &[DiscoveredTest],
  discovered_ids: &BTreeSet<String>,
  report_counts: bool,
) -> ValidationReport {
  let mut report = ValidationReport::default();

  for (idx, entry) in manifest.expectations.iter().enumerate() {
    let prefix = format!("manifest entry #{idx}");

    if entry.status.is_none() {
      report
        .errors
        .push(format!("{prefix} missing `status`/`expectation`"));
    }

    let mut seen = 0;
    if entry.id.is_some() {
      seen += 1;
    }
    if entry.glob.is_some() {
      seen += 1;
    }
    if entry.regex.is_some() {
      seen += 1;
    }
    if seen == 0 {
      report
        .errors
        .push(format!("{prefix} missing `id`/`glob`/`regex`"));
      continue;
    }
    if seen > 1 {
      report
        .errors
        .push(format!("{prefix} must specify exactly one of `id`/`glob`/`regex`"));
      continue;
    }

    if let Some(id) = &entry.id {
      if !discovered_ids.contains(id) {
        report
          .errors
          .push(format!("{prefix} references missing id {id:?}"));
      }
      continue;
    }

    if let Some(glob) = &entry.glob {
      match Glob::new(glob) {
        Ok(glob) => {
          let matcher = glob.compile_matcher();
          let count = discovered.iter().filter(|t| matcher.is_match(&t.id)).count();
          if report_counts {
            report
              .notes
              .push(format!("{prefix} glob {glob:?} matched {count}"));
          }
          if count == 0 {
            report
              .warnings
              .push(format!("{prefix} glob {glob:?} matched 0 tests"));
          }
        }
        Err(err) => report
          .errors
          .push(format!("{prefix} glob {glob:?} is invalid: {err}")),
      }
      continue;
    }

    let regex = entry.regex.as_ref().expect("validated presence");
    match Regex::new(regex) {
      Ok(re) => {
        let count = discovered.iter().filter(|t| re.is_match(&t.id)).count();
        if report_counts {
          report
            .notes
            .push(format!("{prefix} regex {regex:?} matched {count}"));
        }
        if count == 0 {
          report
            .warnings
            .push(format!("{prefix} regex {regex:?} matched 0 tests"));
        }
      }
      Err(err) => report
        .errors
        .push(format!("{prefix} regex {regex:?} is invalid: {err}")),
    }
  }

  report
}

#[cfg(test)]
mod tests {
  use super::*;
  use tempfile::tempdir;

  fn write_file(path: &Path, contents: &str) {
    fs::create_dir_all(path.parent().unwrap()).unwrap();
    fs::write(path, contents).unwrap();
  }

  fn discovered_fixture() -> (tempfile::TempDir, Vec<DiscoveredTest>, BTreeSet<String>) {
    let dir = tempdir().unwrap();
    let test_root = dir.path().join("test");
    write_file(&test_root.join("language/a.js"), "");
    write_file(&test_root.join("language/b.js"), "");

    let discovered = discover_tests(dir.path()).unwrap();
    let discovered_ids = discovered
      .iter()
      .map(|t| t.id.clone())
      .collect::<BTreeSet<_>>();
    (dir, discovered, discovered_ids)
  }

  #[test]
  fn stale_exact_id_is_error() {
    let (_dir, discovered, discovered_ids) = discovered_fixture();
    let suite = SuiteSpec {
      label: "suite \"smoke\"".to_string(),
      suite: Suite {
        tests: vec!["language/a.js".to_string(), "language/missing.js".to_string()],
        ..Suite::default()
      },
    };

    let args = ValidateArgs {
      test262_dir: PathBuf::new(),
      suite: vec![],
      suite_path: vec![],
      manifest: None,
      include_glob_zero: ZeroMatchBehavior::Error,
      exclude_glob_zero: ZeroMatchBehavior::Warn,
      manifest_counts: false,
    };

    let report = validate_suite(&suite, &discovered, &discovered_ids, &args);
    assert!(
      report
        .errors
        .iter()
        .any(|msg| msg.contains("missing test id") && msg.contains("language/missing.js")),
      "expected missing id error, got: {:#?}",
      report.errors
    );
  }

  #[test]
  fn include_glob_matching_nothing_is_error_by_default() {
    let (_dir, discovered, discovered_ids) = discovered_fixture();
    let suite = SuiteSpec {
      label: "suite \"smoke\"".to_string(),
      suite: Suite {
        include: vec!["does/not/exist/**/*.js".to_string()],
        ..Suite::default()
      },
    };

    let args = ValidateArgs {
      test262_dir: PathBuf::new(),
      suite: vec![],
      suite_path: vec![],
      manifest: None,
      include_glob_zero: ZeroMatchBehavior::Error,
      exclude_glob_zero: ZeroMatchBehavior::Warn,
      manifest_counts: false,
    };

    let report = validate_suite(&suite, &discovered, &discovered_ids, &args);
    assert!(
      report
        .errors
        .iter()
        .any(|msg| msg.contains("include glob") && msg.contains("matched 0 tests")),
      "expected include-glob-matched-0 error, got: {:#?}",
      report.errors
    );
  }

  #[test]
  fn suite_selecting_zero_tests_is_error() {
    let (_dir, discovered, discovered_ids) = discovered_fixture();
    let suite = SuiteSpec {
      label: "suite \"smoke\"".to_string(),
      suite: Suite {
        include: vec!["language/*.js".to_string()],
        exclude: vec!["language/*".to_string()],
        ..Suite::default()
      },
    };

    let args = ValidateArgs {
      test262_dir: PathBuf::new(),
      suite: vec![],
      suite_path: vec![],
      manifest: None,
      include_glob_zero: ZeroMatchBehavior::Error,
      exclude_glob_zero: ZeroMatchBehavior::Warn,
      manifest_counts: false,
    };

    let report = validate_suite(&suite, &discovered, &discovered_ids, &args);
    assert!(
      report.errors.iter().any(|msg| msg.contains("selected 0 tests")),
      "expected suite-empty error, got: {:#?}",
      report.errors
    );
  }

  #[test]
  fn manifest_stale_exact_id_is_error() {
    let (dir, discovered, discovered_ids) = discovered_fixture();
    let manifest_path = dir.path().join("manifest.toml");
    fs::write(
      &manifest_path,
      r#"
[[expectations]]
id = "language/missing.js"
status = "xfail"
"#,
    )
    .unwrap();

    let manifest = RawManifest::from_path(&manifest_path).unwrap();
    let report = validate_manifest(&manifest, &discovered, &discovered_ids, false);
    assert!(
      report
        .errors
        .iter()
        .any(|msg| msg.contains("missing id") && msg.contains("language/missing.js")),
      "expected missing manifest id error, got: {:#?}",
      report.errors
    );
  }

  #[test]
  fn manifest_entries_with_reason_fields_parse_and_count_matches() {
    let (dir, discovered, discovered_ids) = discovered_fixture();
    let manifest_path = dir.path().join("manifest.toml");
    fs::write(
      &manifest_path,
      r#"
[[expectations]]
glob = "language/*.js"
status = "xfail"
reason = "example"
tracking_issue = "https://example.invalid/issue/1"
"#,
    )
    .unwrap();

    let manifest = RawManifest::from_path(&manifest_path).expect("manifest parsed");
    let report = validate_manifest(&manifest, &discovered, &discovered_ids, true);
    assert!(
      report.errors.is_empty(),
      "expected no errors, got: {:#?}",
      report.errors
    );
    assert!(
      report.warnings.is_empty(),
      "expected no warnings, got: {:#?}",
      report.warnings
    );
    assert!(
      report
        .notes
        .iter()
        .any(|note| note.contains("matched 2")),
      "expected match count note, got: {:#?}",
      report.notes
    );
  }
}
