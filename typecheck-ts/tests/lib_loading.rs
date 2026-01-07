#![cfg(feature = "serde")]

use std::collections::HashMap;
use std::sync::Arc;

mod common;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{
  CompilerOptions, FileKind, LibFile, LibManager, LibName, ScriptTarget,
};
use typecheck_ts::{FileKey, Host, HostError, Program, PropertyKey, TextRange, TypeKindSummary};

const PROMISE_ARRAY_TYPES: &str = include_str!("fixtures/promise_array_types.ts");
const ESNEXT_DISPOSABLE_TYPES: &str = include_str!("fixtures/esnext_disposable_types.ts");

#[derive(Default)]
struct TestHost {
  files: HashMap<FileKey, Arc<str>>,
  options: CompilerOptions,
  libs: Vec<LibFile>,
  edges: HashMap<(FileKey, String), FileKey>,
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

  fn with_file(mut self, key: FileKey, text: &str) -> Self {
    self.files.insert(key, Arc::from(text));
    self
  }

  fn with_lib(mut self, lib: LibFile) -> Self {
    self.libs.push(lib);
    self
  }

  fn link(mut self, from: FileKey, spec: &str, to: FileKey) -> Self {
    self.edges.insert((from, spec.to_string()), to);
    self
  }
}

impl Host for TestHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    self
      .edges
      .get(&(from.clone(), specifier.to_string()))
      .cloned()
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    if let Some(lib) = self.libs.iter().find(|l| &l.key == file) {
      lib.kind
    } else {
      FileKind::Ts
    }
  }
}

#[test]
fn bundled_lib_manager_loads_official_ts_libs() {
  let manager = LibManager::new();
  let loaded = manager.bundled_libs(&CompilerOptions::default());

  let names: Vec<_> = loaded.files.iter().map(|lib| lib.name.as_ref()).collect();
  let mut sorted = names.clone();
  sorted.sort_unstable();
  assert_eq!(
    names, sorted,
    "bundled libs should have deterministic ordering"
  );

  for lib in loaded.files.iter() {
    assert_eq!(
      lib.key,
      FileKey::new(format!("lib:{}", lib.name.as_ref())),
      "bundled lib file keys must be deterministic"
    );
  }

  assert!(
    loaded
      .files
      .iter()
      .any(|lib| lib.name.as_ref() == "lib.dom.d.ts"),
    "default libs should include lib.dom.d.ts"
  );
  assert!(
    loaded
      .files
      .iter()
      .any(|lib| lib.name.as_ref() == "lib.es2015.promise.d.ts"),
    "default libs should include lib.es2015.promise.d.ts"
  );
  assert!(
    loaded
      .files
      .iter()
      .any(|lib| lib.name.as_ref() == "lib.es2015.collection.d.ts"),
    "default libs should include lib.es2015.collection.d.ts"
  );
  assert!(
    loaded
      .files
      .iter()
      .any(|lib| lib.name.as_ref() == "lib.es2015.symbol.d.ts"),
    "default libs should include lib.es2015.symbol.d.ts"
  );

  let dom_text = loaded
    .files
    .iter()
    .find(|lib| lib.name.as_ref() == "lib.dom.d.ts")
    .expect("lib.dom.d.ts should be present")
    .text
    .as_ref();
  assert!(
    dom_text.contains("interface Document"),
    "vendored dom lib should contain real declarations"
  );
}

#[test]
fn missing_libs_emit_unknown_global_diagnostics() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let entry = FileKey::new("entry.ts");
  let host =
    TestHost::new(options).with_file(entry.clone(), "const p = Promise;\nconst a = Array;");
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  let unknowns = diagnostics
    .iter()
    .filter(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str())
    .count();
  assert!(
    unknowns >= 2,
    "expected unknown global diagnostics for Promise/Array, got {diagnostics:?}"
  );
  let globals = program.global_bindings();
  assert!(
    !globals.contains_key("Promise"),
    "Promise should be absent without default libs"
  );
  assert!(
    !globals.contains_key("Array"),
    "Array should be absent without default libs"
  );
}

#[test]
fn non_dts_libs_warn_and_leave_globals_missing() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let lib = LibFile {
    key: FileKey::new("custom.js"),
    name: Arc::from("custom.js"),
    kind: FileKind::Js,
    text: Arc::from("var Provided = 1;"),
  };
  let source = "const p = Promise;\nconst a = Array;\nconst value = Provided;";
  let host = TestHost::new(options)
    .with_lib(lib)
    .with_file(FileKey::new("entry.ts"), source);
  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
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
  let has_provided = unknown_identifiers
    .iter()
    .any(|diag| diag.primary.range == TextRange::new(provided_start, provided_end));
  assert!(
    has_provided,
    "expected unknown identifier diagnostic for Provided: {diagnostics:?}"
  );
}

#[test]
fn host_provided_libs_are_loaded() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let lib = LibFile {
    key: FileKey::new("custom.d.ts"),
    name: Arc::from("custom.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("declare const Provided: number;"),
  };
  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_lib(lib)
    .with_file(FileKey::new("entry.ts"), "const x = Provided;");
  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
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
    key: FileKey::new("globals.d.ts"),
    name: Arc::from("globals.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from("export {};\ndeclare global { const FromLib: string; }"),
  };
  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_lib(lib)
    .with_file(FileKey::new("entry.ts"), "const value = FromLib;");
  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
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
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "ambient" { interface Foo { bar: string; } }"#),
  };
  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_lib(lib)
    .with_file(FileKey::new("entry.ts"), "/* noop */");
  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "ambient modules should be tolerated: {diagnostics:?}"
  );
}

#[test]
fn ambient_module_types_are_bound() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let ambient_key = FileKey::new("ambient.d.ts");
  let ambient_src = r#"declare module "ambient" { export interface Foo { a: string } }"#;
  let lib = LibFile {
    key: ambient_key.clone(),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(ambient_src),
  };
  let entry = FileKey::new("entry.ts");
  let source = "import type { Foo } from \"ambient\";\ntype Uses = Foo;";
  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_lib(lib)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
  let entry_id = program.file_id(&entry).expect("entry id");
  if std::env::var("DEBUG_AMBIENT").is_ok() {
    let snapshot = program.snapshot();
    let store = types_ts_interned::TypeStore::from_snapshot(snapshot.interned_type_store.clone());
    if let Some(ambient_id) = program.file_id(&ambient_key) {
      for def in program.definitions_in_file(ambient_id) {
        let name = program.def_name(def).unwrap_or_default();
        let interned = program.type_of_def_interned(def);
        eprintln!(
          "ambient def {:?} {} => {} (interned {})",
          def,
          name,
          program.display_type(program.type_of_def(def)),
          types_ts_interned::TypeDisplay::new(&store, interned)
        );
      }
    }
    for def in program.definitions_in_file(entry_id) {
      let name = program.def_name(def).unwrap_or_default();
      let interned = program.type_of_def_interned(def);
      eprintln!(
        "entry def {:?} {} => {} (interned {})",
        def,
        name,
        program.display_type(program.type_of_def(def)),
        types_ts_interned::TypeDisplay::new(&store, interned)
      );
    }
  }
  let uses_def = program
    .definitions_in_file(entry_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Uses"))
    .expect("definition for Uses");
  let uses_ty = program.type_of_def(uses_def);
  let has_prop_a = program
    .properties_of(uses_ty)
    .iter()
    .any(|p| p.key == PropertyKey::String("a".to_string()));
  assert!(
    has_prop_a,
    "expected Uses to expose ambient Foo shape; got {}",
    program.display_type(uses_ty)
  );
}

#[test]
fn module_resolution_can_target_lib_file_keys() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let lib_key = FileKey::new("custom_mod.d.ts");
  let entry = FileKey::new("entry.ts");
  let source = r#"import type { Foo } from "custom_mod"; type Uses = Foo;"#;

  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_lib(LibFile {
      key: lib_key.clone(),
      name: Arc::from("custom_mod.d.ts"),
      kind: FileKind::Dts,
      text: Arc::from("export interface Foo { a: string }"),
    })
    .with_file(entry.clone(), source)
    .link(entry.clone(), "custom_mod", lib_key.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics when resolving to a lib file: {diagnostics:?}"
  );

  assert_eq!(
    program.file_ids_for_key(&lib_key).len(),
    1,
    "module resolution should reuse the lib FileId instead of creating a source copy"
  );

  let entry_id = program.file_id(&entry).expect("entry id");
  let uses_def = program
    .definitions_in_file(entry_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Uses"))
    .expect("definition for Uses");
  let uses_ty = program.type_of_def(uses_def);
  let has_prop_a = program
    .properties_of(uses_ty)
    .iter()
    .any(|p| p.key == PropertyKey::String("a".to_string()));
  assert!(
    has_prop_a,
    "expected Uses to expose Foo shape from lib module; got {}",
    program.display_type(uses_ty)
  );
}

#[test]
fn host_file_named_like_bundled_lib_has_distinct_text() {
  let mut options = CompilerOptions::default();
  options.libs = vec![LibName::parse("es5").expect("lib name")];
  let key = FileKey::new("lib:lib.es5.d.ts");
  let host_text = "export const local = 1;";
  let host = TestHost::new(options).with_file(key.clone(), host_text);
  let program = Program::new(host, vec![key.clone()]);
  let mut ids_for_key = program.file_ids_for_key(&key);
  ids_for_key.sort_by_key(|id| id.0);
  ids_for_key.dedup();
  assert_eq!(
    ids_for_key.len(),
    2,
    "both host file and bundled lib should be loaded even when keys collide"
  );
  assert_ne!(ids_for_key[0], ids_for_key[1]);

  let texts: Vec<_> = ids_for_key
    .iter()
    .filter_map(|id| program.file_text(*id))
    .collect();
  assert_eq!(
    texts.len(),
    2,
    "expected to retrieve text for both host and bundled lib files"
  );
  assert!(
    texts.iter().any(|text| text.as_ref() == host_text),
    "host-provided text should be returned for the source-origin file"
  );
  assert!(
    texts.iter().any(|text| text.as_ref() != host_text),
    "bundled lib text should differ from the host file text"
  );
}

#[test]
fn imported_type_alias_resolves_interned_type() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_file(FileKey::new("types.ts"), "export type Foo = number;")
    .with_file(
      FileKey::new("entry.ts"),
      "import type { Foo } from \"./types\"; type Bar = Foo;",
    )
    .link(
      FileKey::new("entry.ts"),
      "./types",
      FileKey::new("types.ts"),
    );

  let program = Program::new(host, vec![FileKey::new("entry.ts")]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
}

#[test]
fn bundled_lib_types_expose_promise_and_array_shapes() {
  let mut options = CompilerOptions::default();
  options.libs = vec![LibName::parse("es2015").expect("es2015 lib")];
  let entry = FileKey::new("libs.ts");
  let host = TestHost::new(options).with_file(entry.clone(), PROMISE_ARRAY_TYPES);
  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected libs to satisfy Promise/Array references: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id for libs");
  let defs = program.definitions_in_file(file_id);
  let find_def = |name: &str| {
    defs
      .iter()
      .copied()
      .find(|def| program.def_name(*def).as_deref() == Some(name))
      .unwrap_or_else(|| panic!("definition {name} not found"))
  };
  let promise_def = find_def("UsesPromise");
  let array_def = find_def("UsesArray");
  let map_def = find_def("UsesMap");
  let symbol_ctor_def = find_def("UsesSymbolConstructor");

  let promise_ty = program.type_of_def_interned(promise_def);
  let array_ty = program.type_of_def_interned(array_def);
  let map_ty = program.type_of_def_interned(map_def);
  let symbol_ctor_ty = program.type_of_def_interned(symbol_ctor_def);
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
  assert_ne!(
    program.type_kind(map_ty),
    TypeKindSummary::Unknown,
    "Map type should not collapse to unknown"
  );
  assert_ne!(
    program.type_kind(symbol_ctor_ty),
    TypeKindSummary::Unknown,
    "SymbolConstructor type should not collapse to unknown"
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
  let get_prop = program.property_type(map_ty, PropertyKey::String("get".to_string()));
  assert!(
    get_prop.is_some(),
    "Map lib surface should expose get property"
  );
  let iterator_prop =
    program.property_type(symbol_ctor_ty, PropertyKey::String("iterator".to_string()));
  assert!(
    iterator_prop.is_some(),
    "SymbolConstructor lib surface should expose iterator property"
  );
}

#[test]
fn bundled_libs_esnext_include_disposable_protocol() {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  options.libs = vec![
    LibName::parse("es5").expect("es5 lib"),
    LibName::parse("esnext.disposable").expect("esnext.disposable lib"),
  ];

  let entry = FileKey::new("esnext.ts");
  let host = TestHost::new(options).with_file(entry.clone(), ESNEXT_DISPOSABLE_TYPES);
  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected esnext bundled libs to typecheck disposable fixture, got {diagnostics:?}"
  );

  let file_id = program
    .file_id(&entry)
    .expect("file id for disposable fixture");
  let defs = program.definitions_in_file(file_id);
  let find_def = |name: &str| {
    defs
      .iter()
      .copied()
      .find(|def| program.def_name(*def).as_deref() == Some(name))
      .unwrap_or_else(|| panic!("definition {name} not found"))
  };
  let symbol_ctor_def = find_def("UsesSymbolConstructor");
  let disposable_def = find_def("UsesDisposable");

  let symbol_ctor_ty = program.type_of_def_interned(symbol_ctor_def);
  let disposable_ty = program.type_of_def_interned(disposable_def);
  assert_ne!(
    program.type_kind(disposable_ty),
    TypeKindSummary::Unknown,
    "Disposable type should not collapse to unknown"
  );

  let dispose_prop =
    program.property_type(symbol_ctor_ty, PropertyKey::String("dispose".to_string()));
  assert!(
    dispose_prop.is_some(),
    "esnext disposable lib surface should expose Symbol.dispose"
  );
  if let Some(dispose_ty) = dispose_prop {
    assert_eq!(
      program.type_kind(dispose_ty),
      TypeKindSummary::UniqueSymbol,
      "Symbol.dispose should be a unique symbol"
    );
  }
}

#[test]
fn type_imports_inside_classes_queue_dependencies() {
  let entry = FileKey::new("entry.ts");
  let class_mod = FileKey::new("class_mod.ts");
  let ambient_mod = FileKey::new("ambient_mod.ts");
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  let host = TestHost::new(options)
    .with_file(
      entry.clone(),
      r#"
class Foo {
  value!: import("./class_mod").Thing;
}

declare class Bar extends import("./ambient_mod").Base {
  method(arg: import("./ambient_mod").Arg): import("./ambient_mod").Ret;
}
"#,
    )
    .with_file(class_mod.clone(), "export type Thing = string;")
    .with_file(
      ambient_mod.clone(),
      "export class Base {}\nexport type Arg = number;\nexport type Ret = string;",
    )
    .link(entry.clone(), "./class_mod", class_mod.clone())
    .link(entry.clone(), "./ambient_mod", ambient_mod.clone());
  let program = Program::new(host, vec![entry.clone()]);
  let class_loaded = program.file_id(&class_mod);
  let ambient_loaded = program.file_id(&ambient_mod);
  assert!(
    class_loaded.is_some(),
    "class member type imports should queue referenced module"
  );
  assert!(
    ambient_loaded.is_some(),
    "ambient class type references should queue referenced module"
  );
}

#[test]
fn type_imports_in_lib_files_queue_dependencies() {
  let entry = FileKey::new("entry.ts");
  let dep = FileKey::new("dep.ts");
  let lib = FileKey::new("lib:custom");

  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let host = TestHost::new(options)
    .with_lib(common::core_globals_lib())
    .with_file(entry.clone(), "export const value = 1;")
    .with_file(dep.clone(), "export type Thing = number;")
    .with_lib(LibFile {
      key: lib.clone(),
      name: Arc::from("custom.d.ts"),
      kind: FileKind::Dts,
      text: Arc::from(r#"export interface FromDep { value: import("./dep").Thing; }"#),
    })
    .link(lib.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let entry_id = program.file_id(&entry).expect("entry file id");
  let dep_id = program
    .file_id(&dep)
    .expect("dep should be discovered via import() type inside a lib file");

  let mut expected = vec![entry_id, dep_id];
  expected.sort_by_key(|id| id.0);
  assert_eq!(program.reachable_files(), expected);

  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
}
