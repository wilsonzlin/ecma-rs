#![cfg_attr(not(feature = "with-node"), allow(dead_code, unused_imports))]

use crate::multifile::normalize_name;
use crate::tsc::node_available;
use crate::tsc::TscDiagnostic;
use crate::tsc::TscDiagnostics;
use crate::tsc::TscRequest;
use crate::tsc::TscRunner;
use anyhow::anyhow;
use anyhow::Context;
use anyhow::Result;
use clap::Args;
use serde_json::Map;
use serde_json::Value;
use std::collections::HashMap;
use std::fs;
use std::path::Path;
use std::path::PathBuf;
use walkdir::WalkDir;

#[derive(Debug, Clone, Args)]
pub struct DifftscArgs {
  /// Path to the suite containing fixture tests.
  #[arg(long)]
  pub suite: PathBuf,

  /// Whether to regenerate baselines from tsc output.
  #[arg(long)]
  pub update_baselines: bool,

  /// Path to the Node.js executable.
  #[arg(long, default_value = "node")]
  pub node: PathBuf,

  /// Allowed byte tolerance when comparing spans.
  #[arg(long, default_value_t = 0)]
  pub span_tolerance: u32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum CommandStatus {
  Success,
  Skipped,
}

#[derive(Debug, Clone)]
struct TestCase {
  name: String,
  files: Vec<TestFile>,
}

#[derive(Debug, Clone)]
struct TestFile {
  relative_path: PathBuf,
  content: String,
}

pub fn run(args: DifftscArgs) -> Result<CommandStatus> {
  #[cfg(not(feature = "with-node"))]
  {
    let _ = args;
    eprintln!("difftsc skipped: built without `with-node` feature");
    return Ok(CommandStatus::Skipped);
  }

  #[cfg(feature = "with-node")]
  {
    run_with_node(args)
  }
}

#[cfg(feature = "with-node")]
fn run_with_node(args: DifftscArgs) -> Result<CommandStatus> {
  if !node_available(&args.node) {
    eprintln!(
      "difftsc skipped: Node.js not available at {}",
      args.node.display()
    );
    return Ok(CommandStatus::Skipped);
  }

  let suite_path = if args.suite.is_absolute() {
    args.suite.clone()
  } else {
    std::env::current_dir()?.join(&args.suite)
  };

  let suite_path = if suite_path.exists() || args.suite.is_absolute() {
    suite_path
  } else {
    let manifest_candidate = Path::new(env!("CARGO_MANIFEST_DIR")).join(&args.suite);
    if manifest_candidate.exists() {
      manifest_candidate
    } else {
      suite_path
    }
  };

  if !suite_path.exists() {
    return Err(anyhow!(
      "suite path does not exist: {}",
      suite_path.display()
    ));
  }

  let suite_name = suite_path
    .file_name()
    .context("suite path missing final component")?
    .to_string_lossy()
    .to_string();

  let baselines_root = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("baselines")
    .join(&suite_name);

  if args.update_baselines {
    fs::create_dir_all(&baselines_root)
      .with_context(|| format!("create baselines directory at {}", baselines_root.display()))?;
  }

  let tests = collect_tests(&suite_path)?;
  if tests.is_empty() {
    return Err(anyhow!("suite `{}` contains no tests", suite_name));
  }

  let mut mismatches = Vec::new();
  let mut runner = TscRunner::new(args.node.clone())?;

  for test in tests {
    let actual = run_test(&test, &mut runner)?;
    let baseline_path = baselines_root.join(format!("{}.json", test.name));

    if args.update_baselines {
      write_baseline(&baseline_path, &actual)
        .with_context(|| format!("write baseline for {}", test.name))?;
    } else {
      let baseline = read_baseline(&baseline_path)
        .with_context(|| format!("read baseline for {}", test.name))?;
      if let Some(diff) = compare_diagnostics(
        &baseline.diagnostics,
        &actual.diagnostics,
        args.span_tolerance,
      ) {
        mismatches.push((test.name, diff));
      }
    }
  }

  if args.update_baselines {
    println!("updated baselines under {}", baselines_root.display());
    return Ok(CommandStatus::Success);
  }

  if mismatches.is_empty() {
    println!("difftsc: all tests matched for suite `{suite_name}`");
    Ok(CommandStatus::Success)
  } else {
    eprintln!("difftsc: {} mismatches", mismatches.len());
    for (name, diff) in &mismatches {
      eprintln!("  {name}: {diff}");
    }
    Err(anyhow!("{} difftsc mismatches", mismatches.len()))
  }
}

#[cfg(feature = "with-node")]
fn run_test(test: &TestCase, runner: &mut TscRunner) -> Result<TscDiagnostics> {
  let request = build_request(test);
  runner
    .check(request)
    .with_context(|| format!("run tsc for test {}", test.name))
}

#[cfg(feature = "with-node")]
fn build_request(test: &TestCase) -> TscRequest {
  let mut files = HashMap::new();
  let mut root_names = Vec::new();

  for file in &test.files {
    let normalized = normalize_name(file.relative_path.to_string_lossy().as_ref());
    root_names.push(normalized.clone());
    files.insert(normalized, file.content.clone());
  }

  root_names.sort();
  root_names.dedup();

  let mut options = Map::new();
  options.insert("noEmit".into(), Value::Bool(true));
  options.insert("skipLibCheck".into(), Value::Bool(true));
  options.insert("pretty".into(), Value::Bool(false));

  TscRequest {
    root_names,
    files,
    options,
  }
}

fn compare_diagnostics(
  expected: &[TscDiagnostic],
  actual: &[TscDiagnostic],
  tolerance: u32,
) -> Option<String> {
  let expected_sorted = normalize(expected);
  let actual_sorted = normalize(actual);

  if expected_sorted.len() != actual_sorted.len() {
    return Some(format!(
      "diagnostic count mismatch (expected {}, got {})",
      expected_sorted.len(),
      actual_sorted.len()
    ));
  }

  for (idx, (exp, act)) in expected_sorted.iter().zip(actual_sorted.iter()).enumerate() {
    let file_match = exp.file == act.file;
    let code_match = exp.code == act.code;
    let start_match = within_tolerance(exp.start, act.start, tolerance);
    let end_match = within_tolerance(exp.end, act.end, tolerance);
    if !(file_match && code_match && start_match && end_match) {
      return Some(format!(
        "diagnostic {idx} mismatch: expected {} but got {}",
        describe(exp),
        describe(act)
      ));
    }
  }

  None
}

fn within_tolerance(a: u32, b: u32, tolerance: u32) -> bool {
  let (min, max) = if a <= b { (a, b) } else { (b, a) };
  max - min <= tolerance
}

fn describe(diag: &NormalizedDiagnostic) -> String {
  match &diag.file {
    Some(file) => format!("{}:{}-{} (code {})", file, diag.start, diag.end, diag.code),
    None => format!("<no-file>:{}-{} (code {})", diag.start, diag.end, diag.code),
  }
}

fn normalize(diags: &[TscDiagnostic]) -> Vec<NormalizedDiagnostic> {
  let mut normalized: Vec<_> = diags
    .iter()
    .map(|d| NormalizedDiagnostic {
      code: d.code,
      file: d.file.clone(),
      start: d.start,
      end: d.end,
    })
    .collect();

  normalized.sort_by(|a, b| {
    (a.file.as_deref().unwrap_or(""), a.start, a.end, a.code).cmp(&(
      b.file.as_deref().unwrap_or(""),
      b.start,
      b.end,
      b.code,
    ))
  });

  normalized
}

#[derive(Debug, Clone)]
struct NormalizedDiagnostic {
  code: u32,
  file: Option<String>,
  start: u32,
  end: u32,
}

fn collect_tests(suite_path: &Path) -> Result<Vec<TestCase>> {
  let mut entries: Vec<_> = fs::read_dir(suite_path)?.collect::<Result<_, _>>()?;
  entries.sort_by_key(|entry| entry.file_name());

  let mut tests = Vec::new();

  for entry in entries {
    let path = entry.path();
    if path.is_dir() {
      let name = path
        .file_name()
        .and_then(|n| n.to_str())
        .context("test directory missing name")?
        .to_string();
      let files = collect_files_recursively(&path)?;
      tests.push(TestCase { name, files });
    } else if is_source_file(&path) {
      let name = test_name_from_path(&path)?;
      let content =
        fs::read_to_string(&path).with_context(|| format!("read test file {}", path.display()))?;
      tests.push(TestCase {
        name,
        files: vec![TestFile {
          relative_path: path
            .file_name()
            .map(PathBuf::from)
            .context("test file missing name")?,
          content,
        }],
      });
    }
  }

  Ok(tests)
}

fn collect_files_recursively(dir: &Path) -> Result<Vec<TestFile>> {
  let mut files = Vec::new();
  for entry in WalkDir::new(dir)
    .into_iter()
    .filter_map(|res| res.ok())
    .filter(|entry| entry.file_type().is_file())
  {
    let path = entry.path();
    if !is_source_file(path) {
      continue;
    }
    let relative_path = path
      .strip_prefix(dir)
      .context("compute relative path")?
      .to_path_buf();
    let content =
      fs::read_to_string(path).with_context(|| format!("read test file {}", path.display()))?;
    files.push(TestFile {
      relative_path,
      content,
    });
  }

  files.sort_by(|a, b| a.relative_path.cmp(&b.relative_path));
  Ok(files)
}

fn is_source_file(path: &Path) -> bool {
  let file_name = path.file_name().and_then(|n| n.to_str()).unwrap_or("");
  if file_name.ends_with(".d.ts") {
    return true;
  }

  matches!(
    path.extension().and_then(|ext| ext.to_str()),
    Some("ts") | Some("tsx") | Some("js") | Some("jsx") | Some("mts") | Some("cts")
  )
}

fn test_name_from_path(path: &Path) -> Result<String> {
  let file_name = path
    .file_name()
    .and_then(|n| n.to_str())
    .context("test file missing name")?;

  if let Some(stripped) = file_name.strip_suffix(".d.ts") {
    return Ok(stripped.to_string());
  }

  path
    .file_stem()
    .and_then(|stem| stem.to_str())
    .map(|s| s.to_string())
    .context("test file missing stem")
}

fn write_baseline(path: &Path, diagnostics: &TscDiagnostics) -> Result<()> {
  if let Some(parent) = path.parent() {
    fs::create_dir_all(parent)?;
  }

  let json = serde_json::to_string_pretty(diagnostics)?;
  fs::write(path, format!("{json}\n"))
    .with_context(|| format!("write baseline at {}", path.display()))?;

  Ok(())
}

fn read_baseline(path: &Path) -> Result<TscDiagnostics> {
  let data =
    fs::read_to_string(path).with_context(|| format!("read baseline {}", path.display()))?;
  let parsed = serde_json::from_str(&data).context("parse baseline JSON")?;
  Ok(parsed)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn determines_test_name_for_d_ts() {
    let path = Path::new("example.d.ts");
    assert_eq!(test_name_from_path(path).unwrap(), "example");
  }

  #[test]
  fn collects_single_and_multi_file_tests() {
    let dir = tempfile::tempdir().unwrap();
    let single = dir.path().join("one.ts");
    fs::write(&single, "const x: number = 'x';").unwrap();

    let multi_dir = dir.path().join("multi");
    fs::create_dir_all(multi_dir.join("nested")).unwrap();
    fs::write(multi_dir.join("a.ts"), "export const a = 1;").unwrap();
    fs::write(multi_dir.join("nested").join("b.ts"), "export const b = a;").unwrap();

    let tests = collect_tests(dir.path()).unwrap();
    assert_eq!(tests.len(), 2);
    assert_eq!(tests[0].name, "multi");
    assert_eq!(tests[0].files.len(), 2);
    assert_eq!(tests[1].name, "one");
  }

  #[test]
  fn compares_diagnostics_with_tolerance() {
    let expected = vec![TscDiagnostic {
      code: 1,
      file: Some("a.ts".to_string()),
      start: 0,
      end: 4,
      category: None,
      message: None,
    }];
    let actual = vec![TscDiagnostic {
      code: 1,
      file: Some("a.ts".to_string()),
      start: 1,
      end: 5,
      category: None,
      message: None,
    }];
    assert!(compare_diagnostics(&expected, &actual, 0).is_some());
    assert!(compare_diagnostics(&expected, &actual, 1).is_none());
  }
}
