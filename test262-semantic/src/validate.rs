use anyhow::{bail, Context, Result};
use clap::{Args, ValueEnum};
use globset::Glob;
use regex::Regex;
use serde::Deserialize;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;
use walkdir::WalkDir;

#[derive(Args, Debug)]
pub struct ValidateArgs {
  /// Path to a local checkout of the tc39/test262 repository.
  ///
  /// If `--test262-dir/test` exists, discovery is rooted at that directory.
  /// Otherwise, discovery is rooted at `--test262-dir`.
  #[arg(long, value_name = "DIR", default_value = "test262-semantic/data")]
  pub test262_dir: PathBuf,

  /// Path to the suites config TOML file.
  #[arg(long, value_name = "PATH")]
  pub suites: PathBuf,

  /// Suite name to validate. If omitted, validates all suites in the config file.
  #[arg(long, value_name = "NAME")]
  pub suite: Option<String>,

  /// Optional expectations/xfail manifest TOML file.
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

  let suites = SuitesFile::from_path(&args.suites)?;
  if suites.suites.is_empty() {
    bail!(
      "suite config {} contains no [[suites]] entries",
      args.suites.display()
    );
  }

  let suites_to_validate: Vec<&Suite> = match &args.suite {
    Some(name) => {
      let suite = suites
        .suites
        .iter()
        .find(|suite| suite.name == *name)
        .with_context(|| format!("suite {name:?} not found in {}", args.suites.display()))?;
      vec![suite]
    }
    None => suites.suites.iter().collect(),
  };

  let mut report = ValidationReport::default();

  for suite in suites_to_validate {
    report.extend(validate_suite(suite, &discovered, &args));
  }

  if let Some(manifest_path) = &args.manifest {
    let manifest = ManifestFile::from_path(manifest_path)?;
    report.extend(validate_manifest(&manifest, &discovered, args.manifest_counts));
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
struct DiscoveredTests {
  /// All discovered test ids, sorted.
  ids: Vec<String>,
  /// For fast membership tests.
  id_set: BTreeSet<String>,
}

fn discover_tests(test262_dir: &Path) -> Result<DiscoveredTests> {
  let discovery_root = {
    let candidate = test262_dir.join("test");
    if candidate.is_dir() {
      candidate
    } else {
      test262_dir.to_path_buf()
    }
  };

  if !discovery_root.is_dir() {
    bail!(
      "test262 directory {} does not exist or is not a directory",
      discovery_root.display()
    );
  }

  let mut ids = Vec::new();
  for entry in WalkDir::new(&discovery_root).follow_links(false) {
    let entry = entry.with_context(|| {
      format!(
        "walk test262 directory {}",
        discovery_root.display()
      )
    })?;
    if !entry.file_type().is_file() {
      continue;
    }
    let path = entry.path();
    if path.extension().and_then(|ext| ext.to_str()) != Some("js") {
      continue;
    }
    let id = path_to_id(&discovery_root, path)?;
    ids.push(id);
  }

  ids.sort();
  ids.dedup();

  let id_set = ids.iter().cloned().collect::<BTreeSet<_>>();

  Ok(DiscoveredTests {
    ids,
    id_set,
  })
}

fn path_to_id(root: &Path, path: &Path) -> Result<String> {
  let rel = path
    .strip_prefix(root)
    .with_context(|| format!("path {} was not under {}", path.display(), root.display()))?;
  let mut out = String::new();
  for (i, component) in rel.components().enumerate() {
    if i > 0 {
      out.push('/');
    }
    out.push_str(
      component
        .as_os_str()
        .to_str()
        .context("non-utf8 path component in discovered test path")?,
    );
  }
  Ok(out)
}

#[derive(Debug, Deserialize)]
struct SuitesFile {
  #[serde(default)]
  suites: Vec<Suite>,
}

impl SuitesFile {
  fn from_path(path: &Path) -> Result<Self> {
    let raw = fs::read_to_string(path)
      .with_context(|| format!("read suite config {}", path.display()))?;
    toml::from_str(&raw).with_context(|| format!("parse suite config {}", path.display()))
  }
}

#[derive(Debug, Deserialize)]
struct Suite {
  name: String,

  /// Explicit test ids to include.
  #[serde(default)]
  ids: Vec<String>,

  /// Globs that add matching tests to the suite.
  #[serde(default)]
  include: Vec<String>,

  /// Globs that remove matching tests from the suite.
  #[serde(default)]
  exclude: Vec<String>,
}

fn validate_suite(suite: &Suite, discovered: &DiscoveredTests, args: &ValidateArgs) -> ValidationReport {
  let mut report = ValidationReport::default();

  // Validate explicit ids.
  let mut missing_ids = Vec::new();
  for id in &suite.ids {
    if !discovered.id_set.contains(id) {
      missing_ids.push(id.clone());
    }
  }
  missing_ids.sort();
  for id in missing_ids {
    report
      .errors
      .push(format!("suite {:?} references missing id {id:?}", suite.name));
  }

  // Select tests.
  let mut selected = BTreeSet::<String>::new();

  // If no include globs and no explicit ids are specified, default to "all tests".
  if suite.include.is_empty() && suite.ids.is_empty() {
    selected.extend(discovered.ids.iter().cloned());
  }

  for pattern in &suite.include {
    match glob_match_ids(pattern, &discovered.ids) {
      Ok(matches) => {
        if matches.is_empty() {
          report.push_issue(
            args.include_glob_zero,
            format!("suite {:?} include glob {pattern:?} matched 0 tests", suite.name),
          );
        }
        selected.extend(matches);
      }
      Err(err) => report
        .errors
        .push(format!("suite {:?} include glob {pattern:?} is invalid: {err}", suite.name)),
    }
  }

  // Add explicit ids (after glob handling so the error reporting is independent).
  for id in &suite.ids {
    if discovered.id_set.contains(id) {
      selected.insert(id.clone());
    }
  }

  for pattern in &suite.exclude {
    match glob_match_ids(pattern, &selected.iter().cloned().collect::<Vec<_>>()) {
      Ok(matches) => {
        if matches.is_empty() {
          report.push_issue(
            args.exclude_glob_zero,
            format!("suite {:?} exclude glob {pattern:?} matched 0 tests", suite.name),
          );
        }
        for id in matches {
          selected.remove(&id);
        }
      }
      Err(err) => report
        .errors
        .push(format!("suite {:?} exclude glob {pattern:?} is invalid: {err}", suite.name)),
    }
  }

  if selected.is_empty() {
    report
      .errors
      .push(format!("suite {:?} selected 0 tests", suite.name));
  }

  report
}

fn glob_match_ids(pattern: &str, ids: &[String]) -> Result<Vec<String>> {
  let matcher = Glob::new(pattern)
    .with_context(|| format!("invalid glob pattern {pattern:?}"))?
    .compile_matcher();
  let mut out = Vec::new();
  for id in ids {
    if matcher.is_match(id) {
      out.push(id.clone());
    }
  }
  out.sort();
  out.dedup();
  Ok(out)
}

#[derive(Debug, Deserialize)]
struct ManifestFile {
  #[serde(default)]
  expectations: Vec<ManifestEntry>,
}

impl ManifestFile {
  fn from_path(path: &Path) -> Result<Self> {
    let raw = fs::read_to_string(path)
      .with_context(|| format!("read manifest {}", path.display()))?;
    toml::from_str(&raw).with_context(|| format!("parse manifest {}", path.display()))
  }
}

#[derive(Debug, Deserialize)]
struct ManifestEntry {
  #[serde(default)]
  id: Option<String>,
  #[serde(default)]
  glob: Option<String>,
  #[serde(default)]
  regex: Option<String>,

  // Additional fields (status, reason, etc.) are ignored by validation.
  #[serde(flatten)]
  _rest: BTreeMap<String, toml::Value>,
}

fn validate_manifest(
  manifest: &ManifestFile,
  discovered: &DiscoveredTests,
  report_counts: bool,
) -> ValidationReport {
  let mut report = ValidationReport::default();

  for (idx, entry) in manifest.expectations.iter().enumerate() {
    let prefix = format!("manifest entry #{idx}");

    match (&entry.id, &entry.glob, &entry.regex) {
      (Some(id), None, None) => {
        if !discovered.id_set.contains(id) {
          report
            .errors
            .push(format!("{prefix} references missing id {id:?}"));
        }
      }
      (None, Some(glob), None) => match glob_match_ids(glob, &discovered.ids) {
        Ok(matches) => {
          if report_counts {
            report.notes.push(format!("{prefix} glob {glob:?} matched {}", matches.len()));
          }
          if matches.is_empty() {
            report
              .warnings
              .push(format!("{prefix} glob {glob:?} matched 0 tests"));
          }
        }
        Err(err) => report
          .errors
          .push(format!("{prefix} glob {glob:?} is invalid: {err}")),
      },
      (None, None, Some(regex)) => match Regex::new(regex) {
        Ok(re) => {
          let count = discovered.ids.iter().filter(|id| re.is_match(id)).count();
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
      },
      _ => report.errors.push(format!(
        "{prefix} must contain exactly one of `id`, `glob`, or `regex`"
      )),
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

  #[test]
  fn stale_exact_id_is_error() {
    let dir = tempdir().unwrap();
    let test_root = dir.path().join("test");
    write_file(&test_root.join("language/ok.js"), "");

    let suites_path = dir.path().join("suites.toml");
    fs::write(
      &suites_path,
      r#"
[[suites]]
name = "smoke"
ids = ["language/ok.js", "language/missing.js"]
"#,
    )
    .unwrap();

    let discovered = discover_tests(dir.path()).unwrap();
    let suites = SuitesFile::from_path(&suites_path).unwrap();
    let suite = &suites.suites[0];

    let args = ValidateArgs {
      test262_dir: dir.path().to_path_buf(),
      suites: suites_path,
      suite: Some("smoke".to_string()),
      manifest: None,
      include_glob_zero: ZeroMatchBehavior::Error,
      exclude_glob_zero: ZeroMatchBehavior::Warn,
      manifest_counts: false,
    };

    let report = validate_suite(suite, &discovered, &args);
    assert!(
      report
        .errors
        .iter()
        .any(|msg| msg.contains("missing id") && msg.contains("language/missing.js")),
      "expected missing id error, got: {:#?}",
      report.errors
    );
  }

  #[test]
  fn manifest_stale_exact_id_is_error() {
    let dir = tempdir().unwrap();
    let test_root = dir.path().join("test");
    write_file(&test_root.join("language/ok.js"), "");

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

    let discovered = discover_tests(dir.path()).unwrap();
    let manifest = ManifestFile::from_path(&manifest_path).unwrap();
    let report = validate_manifest(&manifest, &discovered, false);
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
  fn include_glob_matching_nothing_is_error_by_default() {
    let dir = tempdir().unwrap();
    let test_root = dir.path().join("test");
    write_file(&test_root.join("language/ok.js"), "");

    let suites_path = dir.path().join("suites.toml");
    fs::write(
      &suites_path,
      r#"
[[suites]]
name = "smoke"
include = ["does/not/exist/**/*.js"]
"#,
    )
    .unwrap();

    let discovered = discover_tests(dir.path()).unwrap();
    let suites = SuitesFile::from_path(&suites_path).unwrap();
    let suite = &suites.suites[0];

    let args = ValidateArgs {
      test262_dir: dir.path().to_path_buf(),
      suites: suites_path,
      suite: Some("smoke".to_string()),
      manifest: None,
      include_glob_zero: ZeroMatchBehavior::Error,
      exclude_glob_zero: ZeroMatchBehavior::Warn,
      manifest_counts: false,
    };

    let report = validate_suite(suite, &discovered, &args);
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
    let dir = tempdir().unwrap();
    let test_root = dir.path().join("test");
    write_file(&test_root.join("language/a.js"), "");
    write_file(&test_root.join("language/b.js"), "");

    let suites_path = dir.path().join("suites.toml");
    fs::write(
      &suites_path,
      r#"
[[suites]]
name = "smoke"
include = ["language/*.js"]
exclude = ["language/*"]
"#,
    )
    .unwrap();

    let discovered = discover_tests(dir.path()).unwrap();
    let suites = SuitesFile::from_path(&suites_path).unwrap();
    let suite = &suites.suites[0];

    let args = ValidateArgs {
      test262_dir: dir.path().to_path_buf(),
      suites: suites_path,
      suite: Some("smoke".to_string()),
      manifest: None,
      include_glob_zero: ZeroMatchBehavior::Error,
      exclude_glob_zero: ZeroMatchBehavior::Warn,
      manifest_counts: false,
    };

    let report = validate_suite(suite, &discovered, &args);
    assert!(
      report
        .errors
        .iter()
        .any(|msg| msg.contains("selected 0 tests")),
      "expected suite-empty error, got: {:#?}",
      report.errors
    );
  }
}
