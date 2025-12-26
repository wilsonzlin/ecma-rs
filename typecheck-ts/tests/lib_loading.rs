use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileId, Host, HostError, Program, PropertyKey, TextRange, TypeKindSummary};

const PROMISE_DOM: &str = include_str!("fixtures/promise_dom.ts");
const PROMISE_ARRAY_TYPES: &str = include_str!("fixtures/promise_array_types.ts");

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
  let source = "const p = Promise;\nconst a = Array;";
  let host = TestHost::new(CompilerOptions::default()).with_file(FileId(0), source);
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
  let promise_offset = source.find("Promise").expect("Promise offset") as u32;
  let array_offset = source.find("Array").expect("Array offset") as u32;
  assert!(
    program.symbol_at(FileId(0), promise_offset).is_some(),
    "global Promise should resolve to a symbol"
  );
  assert!(
    program.symbol_at(FileId(0), array_offset).is_some(),
    "global Array should resolve to a symbol"
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
  let offset = "const value = FromLib;"
    .find("FromLib")
    .expect("FromLib reference") as u32;
  assert!(
    program.symbol_at(FileId(0), offset).is_some(),
    "declare global value should resolve to a symbol"
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
fn bundled_lib_types_expose_promise_and_array_shapes() {
  let host = TestHost::new(CompilerOptions::default())
    .with_file(FileId(0), PROMISE_ARRAY_TYPES);
  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected libs to satisfy Promise/Array references: {diagnostics:?}"
  );

  let defs = program.definitions_in_file(FileId(0));
  let find_def = |name: &str| {
    defs
      .iter()
      .copied()
      .find(|def| program.def_name(*def).as_deref() == Some(name))
      .unwrap_or_else(|| panic!("definition {name} not found"))
  };
  let promise_def = find_def("UsesPromise");
  let array_def = find_def("UsesArray");

  let promise_ty = program.type_of_def_interned(promise_def);
  let array_ty = program.type_of_def_interned(array_def);
  assert_ne!(
    program.type_kind(promise_ty),
    TypeKindSummary::Unknown,
    "Promise type should not collapse to unknown"
  );
  assert_ne!(
    program.type_kind(array_ty),
    TypeKindSummary::Unknown,
    "Array type should not collapse to unknown"
  );

  let then_prop = program.property_type(promise_ty, PropertyKey::String("then".to_string()));
  assert!(
    then_prop.is_some(),
    "Promise lib surface should expose then property"
  );
  let length_prop = program.property_type(array_ty, PropertyKey::String("length".to_string()));
  assert!(
    length_prop.is_some(),
    "Array lib surface should expose length property"
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
  let document_offset = PROMISE_DOM
    .find("document")
    .expect("document reference in fixture") as u32;
  assert!(
    program.symbol_at(FileId(0), document_offset).is_some(),
    "DOM globals should resolve to symbols"
  );
}
