use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileId, Host, HostError, Program};

#[derive(Default)]
struct TestHost {
  files: HashMap<FileId, Arc<str>>,
  options: CompilerOptions,
  libs: Vec<LibFile>,
}

impl TestHost {
  fn new(options: CompilerOptions) -> Self {
    TestHost {
      files: HashMap::new(),
      options,
      libs: Vec::new(),
    }
  }

  fn with_file(mut self, id: FileId, text: &str) -> Self {
    self.files.insert(id, Arc::from(text));
    self
  }

  fn with_lib(mut self, lib: LibFile) -> Self {
    self.libs.push(lib);
    self
  }
}

impl Host for TestHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: FileId) -> FileKind {
    if let Some(lib) = self.libs.iter().find(|l| l.id == file) {
      lib.kind
    } else {
      FileKind::Ts
    }
  }
}

#[test]
fn bundled_libs_enable_global_promise_and_array() {
  let host = TestHost::new(CompilerOptions::default()).with_file(
    FileId(0),
    "const p = Promise;\nconst a = Array;",
  );
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
}

#[test]
fn missing_libs_emit_unknown_global_diagnostics() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let host = TestHost::new(options).with_file(
    FileId(0),
    "const p = Promise;\nconst a = Array;",
  );
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 2, "unexpected diagnostics: {diagnostics:?}");
  assert!(diagnostics.iter().any(|d| d.message.contains("Promise")));
  assert!(diagnostics.iter().any(|d| d.message.contains("Array")));
}

#[test]
fn host_provided_libs_are_loaded() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let lib = LibFile {
    id: FileId(99),
    name: Arc::from("custom.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("declare const Provided: number;"),
  };
  let host = TestHost::new(options)
    .with_lib(lib)
    .with_file(FileId(0), "const x = Provided;");
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected host libs to satisfy globals: {diagnostics:?}"
  );
}
