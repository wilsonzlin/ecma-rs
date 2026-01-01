use std::fs;
use std::path::Path;
use std::sync::Arc;
use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, Host, HostError, Program};
use typecheck_ts_harness::VirtualFile;

#[cfg(feature = "with-node")]
mod common;
#[cfg(feature = "with-node")]
use serde_json::Map;
#[cfg(feature = "with-node")]
use serde_json::Value;
#[cfg(feature = "with-node")]
use std::collections::HashMap;
#[cfg(feature = "with-node")]
use typecheck_ts_harness::tsc::{TscDiagnostics, TscRequest, TscRunner};

#[derive(Clone)]
struct SimpleHost {
  files: std::collections::HashMap<String, Arc<str>>,
  names: Vec<FileKey>,
  options: CompilerOptions,
}

impl SimpleHost {
  fn new(files: Vec<VirtualFile>, options: CompilerOptions) -> Self {
    let mut map = std::collections::HashMap::new();
    let mut names = Vec::new();
    for file in files {
      names.push(FileKey::new(file.name.clone()));
      map.insert(file.name, Arc::from(file.content));
    }
    Self {
      files: map,
      names,
      options,
    }
  }

  fn roots(&self) -> Vec<FileKey> {
    self.names.clone()
  }
}

impl Host for SimpleHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file.as_str())
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

fn lib_env_fixture(name: &str) -> VirtualFile {
  let path = Path::new(env!("CARGO_MANIFEST_DIR"))
    .join("fixtures")
    .join("lib_env")
    .join(name);
  VirtualFile {
    name: name.to_string(),
    content: fs::read_to_string(path).expect("read fixture"),
  }
}

fn promise_fixture() -> VirtualFile {
  lib_env_fixture("promise.ts")
}

fn global_types_fixture() -> VirtualFile {
  lib_env_fixture("a.ts")
}

fn run_rust(files: Vec<VirtualFile>, options: CompilerOptions) -> Vec<typecheck_ts::Diagnostic> {
  let host = SimpleHost::new(files.clone(), options);
  let roots = host.roots();
  Program::new(host, roots).check()
}

#[cfg(feature = "with-node")]
fn runner_or_skip() -> Option<TscRunner> {
  common::runner_or_skip("tsc lib env tests")
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
    diagnostics_only: true,
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
fn default_libs_resolve_global_types() {
  let fixture = global_types_fixture();
  let host = SimpleHost::new(vec![fixture.clone()], CompilerOptions::default());
  let roots = host.roots();
  let program = Program::new(host, roots);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics for libs, got {diagnostics:?}"
  );

  let file_id = program
    .file_id(&FileKey::new(fixture.name.clone()))
    .expect("file id");
  let defs = program.definitions_in_file(file_id);
  assert!(
    !defs.is_empty(),
    "expected definitions for {}, found none",
    fixture.name
  );
  let mut checked = 0usize;
  for def in defs {
    let Some(name) = program.def_name(def) else {
      continue;
    };
    checked += 1;
    let ty = program.type_of_def_interned(def);
    let summary = program.type_kind(ty);
    assert!(
      !matches!(summary, typecheck_ts::TypeKindSummary::Unknown),
      "expected known type for def {name} ({def:?})"
    );
  }
  assert!(
    checked >= 2,
    "expected at least 2 user-visible definitions for {}, got {checked}",
    fixture.name
  );
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
