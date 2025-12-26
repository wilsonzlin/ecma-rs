use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::FileId as HirFileId;
use hir_js::lower_file_with_diagnostics;
use hir_js::FileKind as HirFileKind;
use parse_js::parse;
use semantic_js::ts::{
  bind_ts_program, from_hir_js::lower_to_ts_hir, FileId, ModuleKind, Resolver,
};
use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileId as TcFileId, Host, HostError, Program, TypeKindSummary};

struct NoResolve;

impl Resolver for NoResolve {
  fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
    None
  }
}

struct MemoryHost {
  files: HashMap<TcFileId, Arc<str>>,
  options: CompilerOptions,
  libs: Vec<LibFile>,
}

impl MemoryHost {
  fn new(options: CompilerOptions) -> Self {
    Self {
      files: HashMap::new(),
      options,
      libs: Vec::new(),
    }
  }

  fn insert(&mut self, id: TcFileId, source: &str) {
    self.files.insert(id, Arc::from(source.to_string()));
  }

  fn add_lib(&mut self, lib: LibFile) {
    self.libs.push(lib);
  }
}

impl Default for MemoryHost {
  fn default() -> Self {
    Self::new(CompilerOptions::default())
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: TcFileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: TcFileId, _spec: &str) -> Option<TcFileId> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: TcFileId) -> FileKind {
    if let Some(lib) = self.libs.iter().find(|lib| lib.id == file) {
      lib.kind
    } else {
      FileKind::Ts
    }
  }
}

#[test]
fn declare_global_from_dts_is_available_globally() {
  let source = r#"declare global { interface Foo { bar: string; } }"#;
  let ast = parse(source).expect("parse");
  let (lowered, diags) = lower_file_with_diagnostics(HirFileId(0), HirFileKind::Dts, &ast);
  assert!(diags.is_empty());
  let hir = lower_to_ts_hir(&ast, &lowered);

  let files: HashMap<FileId, Arc<semantic_js::ts::HirFile>> =
    HashMap::from([(FileId(0), Arc::new(hir))]);

  let (semantics, diags) =
    bind_ts_program(&[FileId(0)], &NoResolve, |f| files.get(&f).unwrap().clone());

  assert!(diags.is_empty());
  assert!(
    semantics.global_symbols().contains_key("Foo"),
    "global symbol for Foo is available"
  );
  assert_eq!(
    ModuleKind::Script,
    files.get(&FileId(0)).unwrap().module_kind
  );
}

#[test]
fn interfaces_merge_members_for_interned_types() {
  let mut host = MemoryHost::default();
  host.insert(
    TcFileId(1),
    "interface Foo { a: string; }\ninterface Foo { b: number; }",
  );

  let program = Program::new(host, vec![TcFileId(1)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let def = program
    .definitions_in_file(TcFileId(1))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Foo"))
    .expect("Foo definition");
  let ty = program.type_of_def(def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("a: string") && rendered.contains("b: number"),
    "merged interface should expose all members, got {rendered}"
  );
}

#[test]
fn program_resolves_declare_global_types_from_libs() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let mut host = MemoryHost::new(options);
  host.add_lib(LibFile {
    id: TcFileId(10),
    name: Arc::from("globals.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("export {};\ndeclare global { interface GlobalFromLib { value: string; } }"),
  });
  host.insert(TcFileId(0), "type Alias = GlobalFromLib;");

  let program = Program::new(host, vec![TcFileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "declare global types from libs should be visible: {diagnostics:?}"
  );

  let def = program
    .definitions_in_file(TcFileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Alias"))
    .expect("Alias definition");
  let ty = program.type_of_def_interned(def);
  assert_ne!(
    program.type_kind(ty),
    TypeKindSummary::Unknown,
    "declare global type aliases should lower through interned store"
  );
}
