use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Arc;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileId, Host, HostError, Program};
use typecheck_ts_harness::VirtualFile;

#[cfg(feature = "with-node")]
use serde_json::Map;
#[cfg(feature = "with-node")]
use serde_json::Value;
#[cfg(feature = "with-node")]
use std::collections::HashMap;
#[cfg(feature = "with-node")]
use std::process::Command;
#[cfg(feature = "with-node")]
use typecheck_ts_harness::tsc::{node_available, TscDiagnostics, TscRequest, TscRunner};

#[derive(Clone)]
struct SimpleHost {
  files: Vec<VirtualFile>,
  options: CompilerOptions,
}

impl SimpleHost {
  fn new(files: Vec<VirtualFile>, options: CompilerOptions) -> Self {
    Self { files, options }
  }

  fn roots(&self) -> Vec<FileId> {
    (0..self.files.len()).map(|i| FileId(i as u32)).collect()
  }
}

impl Host for SimpleHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file.0 as usize)
      .map(|f| Arc::from(f.content.clone()))
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

fn fixture_path() -> PathBuf {
  Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("lib_env")
    .join("promise.ts")
}

fn promise_fixture() -> VirtualFile {
  let path = fixture_path();
  VirtualFile {
    name: "promise.ts".to_string(),
    content: fs::read_to_string(path).expect("read fixture"),
  }
}

fn run_rust(files: Vec<VirtualFile>, options: CompilerOptions) -> Vec<typecheck_ts::Diagnostic> {
  let host = SimpleHost::new(files.clone(), options);
  let roots = host.roots();
  Program::new(host, roots).check()
}

#[cfg(feature = "with-node")]
fn runner_or_skip() -> Option<TscRunner> {
  let node_path = PathBuf::from("node");

  if !node_available(&node_path) {
    eprintln!("skipping tsc lib env tests: node not available");
    return None;
  }

  if !typescript_available(&node_path) {
    eprintln!("skipping tsc lib env tests: typescript npm package missing");
    return None;
  }

  match TscRunner::new(node_path) {
    Ok(runner) => Some(runner),
    Err(err) => {
      eprintln!("skipping tsc lib env tests: {err}");
      None
    }
  }
}

#[cfg(feature = "with-node")]
fn typescript_available(node_path: &Path) -> bool {
  Command::new(node_path)
    .arg("-e")
    .arg("require('typescript')")
    .current_dir(env!("CARGO_MANIFEST_DIR"))
    .status()
    .map(|status| status.success())
    .unwrap_or(false)
}

#[cfg(feature = "with-node")]
fn run_tsc(
  runner: &mut TscRunner,
  file: &VirtualFile,
  options: Map<String, Value>,
) -> TscDiagnostics {
  let mut files = HashMap::new();
  files.insert(file.name.clone(), file.content.clone());

  let request = TscRequest {
    root_names: vec![file.name.clone()],
    files,
    options,
    type_queries: Vec::new(),
  };

  runner.check(request).expect("tsc output")
}

#[test]
fn promise_reports_unknown_without_libs() {
  let fixture = promise_fixture();

  let rust_diags = run_rust(
    vec![fixture.clone()],
    CompilerOptions {
      no_default_lib: true,
      ..CompilerOptions::default()
    },
  );
  assert!(
    rust_diags.iter().any(|d| d.message.contains("Promise")),
    "expected an unknown identifier diagnostic, got {rust_diags:?}"
  );

  #[cfg(feature = "with-node")]
  {
    let mut runner = match runner_or_skip() {
      Some(runner) => runner,
      None => return,
    };

    let mut options = Map::new();
    options.insert("noLib".to_string(), Value::Bool(true));
    options.insert("target".to_string(), Value::String("ES2015".to_string()));

    let tsc = run_tsc(&mut runner, &fixture, options);
    assert!(
      tsc
        .diagnostics
        .iter()
        .any(|d| d.message.as_deref().unwrap_or_default().contains("Promise")),
      "expected tsc to report missing Promise, got {:?}",
      tsc.diagnostics
    );
  }
}

#[test]
fn tsc_accepts_promise_with_libs_when_available() {
  let fixture = promise_fixture();
  // Ensure the Rust checker can load bundled libs; diagnostics may still exist as `.d.ts`
  // handling is incomplete, so we don't assert on output yet.
  let _ = run_rust(vec![fixture.clone()], CompilerOptions::default());

  #[cfg(feature = "with-node")]
  {
    let mut runner = match runner_or_skip() {
      Some(runner) => runner,
      None => return,
    };

    let mut options = Map::new();
    options.insert("target".to_string(), Value::String("ES2015".to_string()));

    let tsc = run_tsc(&mut runner, &fixture, options);
    assert!(
      tsc.diagnostics.is_empty(),
      "expected no diagnostics with libs, got {:?}",
      tsc.diagnostics
    );
  }
}
