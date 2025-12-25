use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileId, Host, HostError, Program};

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

  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    self.edges.get(&(_from, _specifier.to_string())).copied()
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
  assert_eq!(
    diagnostics.len(),
    2,
    "unexpected diagnostics: {diagnostics:?}"
  );
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

  let def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Bar"))
    .expect("Bar type alias");
  let ty = program.type_of_def_interned(def);
  let foo_def = program
    .definitions_in_file(FileId(1))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Foo"))
    .expect("Foo export");
  match program.interned_type_kind(ty) {
    types_ts_interned::TypeKind::Ref { def: target, .. } => {
      assert_eq!(target.0, foo_def.0, "import should resolve to Foo def");
    }
    other => panic!("expected ref to Foo, got {:?}", other),
  }
}
