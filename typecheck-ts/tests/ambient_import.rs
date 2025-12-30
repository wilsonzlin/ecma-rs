use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, Host, HostError, Program, TypeKindSummary};

#[derive(Default)]
struct AmbientHost {
  files: HashMap<FileKey, Arc<str>>,
  libs: Vec<LibFile>,
  options: CompilerOptions,
}

impl AmbientHost {
  fn new(options: CompilerOptions) -> Self {
    AmbientHost {
      files: HashMap::new(),
      libs: Vec::new(),
      options,
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
}

impl Host for AmbientHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: &FileKey, _specifier: &str) -> Option<FileKey> {
    None
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    if self.libs.iter().any(|lib| &lib.key == file) {
      FileKind::Dts
    } else {
      FileKind::Ts
    }
  }
}

#[test]
fn imports_from_ambient_modules_without_host_resolution() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let entry = FileKey::new("entry.ts");
  let ambient_lib = LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "ambient" { export const x: string; }"#),
  };

  let host = AmbientHost::new(options).with_lib(ambient_lib).with_file(
    entry.clone(),
    r#"import { x } from "ambient"; const y = x;"#,
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("entry file id");
  let y_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("y"))
    .expect("definition for y");

  let ty = program.type_of_def(y_def);
  let rendered = program.display_type(ty).to_string();
  assert_eq!(rendered, "string");
}

#[test]
fn ambient_module_type_imports_resolve_types() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let entry = FileKey::new("entry.ts");
  let ambient_lib = LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "ambient" { export interface Foo { a: string } }"#),
  };

  let host = AmbientHost::new(options).with_lib(ambient_lib).with_file(
    entry.clone(),
    r#"import type { Foo } from "ambient"; type Uses = Foo;"#,
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("entry file id");
  let uses_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Uses"))
    .expect("definition for Uses");

  let kind = program.type_kind(program.type_of_def(uses_def));
  assert_ne!(
    kind,
    TypeKindSummary::Unknown,
    "type-only imports from ambient modules should resolve to a known type"
  );

  let rendered = program
    .display_type(program.type_of_def(uses_def))
    .to_string();
  assert!(
    rendered != "unknown",
    "expected Uses to resolve to a concrete type; got {rendered}"
  );
}

#[test]
fn ambient_module_exports_map_to_module_defs() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let entry = FileKey::new("entry.ts");
  let ambient_lib = LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
interface Foo { fromTop: number }
declare module "ambient" {
  export interface Foo { fromAmbient: string }
}
"#,
    ),
  };

  let host = AmbientHost::new(options).with_lib(ambient_lib).with_file(
    entry.clone(),
    r#"import type { Foo } from "ambient"; const value: Foo = { fromAmbient: "ok" };"#,
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  let file_id = program.file_id(&entry).expect("entry file id");
  let foo_import_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("Foo"))
    .expect("imported Foo def");
  let foo_ty = program.type_of_def(foo_import_def);
  assert_eq!(
    program.display_type(foo_ty).to_string(),
    "{ fromAmbient: string }",
    "imported Foo should resolve to the ambient module export, not the global interface"
  );
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics when preferring ambient module declarations: {diagnostics:?}"
  );

  let value_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("value"))
    .expect("definition for value");

  let value_kind = program.type_kind(program.type_of_def(value_def));
  assert_ne!(
    value_kind,
    TypeKindSummary::Unknown,
    "annotated imports from ambient modules should preserve their declared shape"
  );
}

#[test]
fn ambient_module_types_drive_object_checks() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let entry = FileKey::new("entry.ts");
  let ambient_lib = LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "ambient" { export interface Foo { a: string } }"#),
  };

  let host = AmbientHost::new(options).with_lib(ambient_lib).with_file(
    entry.clone(),
    r#"
import type { Foo } from "ambient";
const ok: Foo = { a: "ok" };
const bad: Foo = { a: 123 };
"#,
  );

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics.is_empty(),
    "assigning the wrong property type should produce a diagnostic"
  );
}
