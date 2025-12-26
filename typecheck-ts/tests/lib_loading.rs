use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileId, Host, HostError, Program, TextRange};

const PROMISE_DOM: &str = include_str!("fixtures/promise_dom.ts");

#[derive(Default)]
struct TestHost {
  files: HashMap<FileId, Arc<str>>,
  options: CompilerOptions,
  libs: Vec<LibFile>,
  edges: HashMap<(FileId, String), FileId>,
}

impl TestHost {
  fn new(options: CompilerOptions) -> Self {
    TestHost {
      files: HashMap::new(),
      options,
      libs: Vec::new(),
      edges: HashMap::new(),
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

  fn link(mut self, from: FileId, spec: &str, to: FileId) -> Self {
    self.edges.insert((from, spec.to_string()), to);
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

  fn resolve(&self, from: FileId, specifier: &str) -> Option<FileId> {
    self.edges.get(&(from, specifier.to_string())).copied()
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
  let host = TestHost::new(CompilerOptions::default())
    .with_file(FileId(0), "const p = Promise;\nconst a = Array;");
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
  let host = TestHost::new(options).with_file(FileId(0), "const p = Promise;\nconst a = Array;");
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NO_LIBS_LOADED.as_str()),
    "missing libs should surface a dedicated diagnostic: {diagnostics:?}"
  );
  let unknowns = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str())
    .count();
  assert!(
    unknowns >= 2,
    "expected unknown global diagnostics for Promise/Array, got {diagnostics:?}"
  );
}

#[test]
fn non_dts_libs_warn_and_leave_globals_missing() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let lib = LibFile {
    id: FileId(99),
    name: Arc::from("custom.js"),
    kind: FileKind::Js,
    text: Arc::from("var Provided = 1;"),
  };
  let source = "const p = Promise;\nconst a = Array;\nconst value = Provided;";
  let host = TestHost::new(options)
    .with_lib(lib)
    .with_file(FileId(0), source);
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NON_DTS_LIB.as_str()),
    "non-.d.ts libs should emit a warning: {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::NO_LIBS_LOADED.as_str()),
    "ignoring non-.d.ts libs should surface missing libs: {diagnostics:?}"
  );
  let unknown_identifiers: Vec<_> = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str())
    .collect();
  assert!(
    unknown_identifiers.len() >= 3,
    "expected unknown identifier diagnostics for Promise, Array, and Provided: {diagnostics:?}"
  );
  let provided_start = source
    .find("Provided")
    .expect("source should include Provided") as u32;
  let provided_end = provided_start + "Provided".len() as u32;
  assert!(
    unknown_identifiers
      .iter()
      .any(|diag| diag.primary.range == TextRange::new(provided_start, provided_end)),
    "expected unknown identifier diagnostic for Provided: {diagnostics:?}"
  );
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

#[test]
fn declare_global_libs_merge_into_globals() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let lib = LibFile {
    id: FileId(100),
    name: Arc::from("globals.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("export {};\ndeclare global { const FromLib: string; }"),
  };
  let host = TestHost::new(options)
    .with_lib(lib)
    .with_file(FileId(0), "const value = FromLib;");
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "declare global from libs should populate global scope: {diagnostics:?}"
  );
}

#[test]
fn declare_module_libs_do_not_crash() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let lib = LibFile {
    id: FileId(101),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "ambient" { interface Foo { bar: string; } }"#),
  };
  let host = TestHost::new(options)
    .with_lib(lib)
    .with_file(FileId(0), "/* noop */");
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "ambient modules should be tolerated: {diagnostics:?}"
  );
}

#[test]
fn imported_type_alias_resolves_interned_type() {
  let host = TestHost::new(CompilerOptions::default())
    .with_file(FileId(1), "export type Foo = number;")
    .with_file(
      FileId(0),
      "import type { Foo } from \"./types\"; type Bar = Foo;",
    )
    .link(FileId(0), "./types", FileId(1));

  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn bundled_libs_enable_dom_and_promise_fixture() {
  let mut options = CompilerOptions::default();
  options.include_dom = true;
  let host = TestHost::new(options).with_file(FileId(0), PROMISE_DOM);
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected bundled libs to typecheck Promise/DOM fixture, got {diagnostics:?}"
  );
}
