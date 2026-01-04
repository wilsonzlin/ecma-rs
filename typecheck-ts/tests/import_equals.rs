use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn import_equals_entity_name_aliases_value() {
  let mut host = MemoryHost::new();
  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
namespace Bar { export const Baz = 1 as const; }
import Foo = Bar.Baz;
export const x = Foo;
"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn import_equals_require_aliases_module_namespace() {
  let mut host = MemoryHost::new();
  let dep = FileKey::new("dep.ts");
  host.insert(dep, "export const value: number = 1;");

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"import Foo = require("./dep"); export const x = Foo.value;"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn import_equals_require_aliases_ambient_module_namespace() {
  let mut host = MemoryHost::new();
  host.add_lib(LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "dep" { export const value: number; }"#),
  });

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"import Foo = require("dep"); export const x = Foo.value;"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn import_equals_require_interops_with_ambient_export_assignment() {
  let mut host = MemoryHost::new();
  host.add_lib(LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare module "dep" {
  declare const foo: 1;
  export = foo;
}
"#,
    ),
  });

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
import foo = require("dep");
export const x: 1 = foo;
"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn ambient_module_exports_resolve_through_import_equals_require_type_members() {
  let mut host = MemoryHost::new();
  host.add_lib(LibFile {
    key: FileKey::new("ambient.d.ts"),
    name: Arc::from("ambient.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(r#"declare module "dep" { export interface Foo { x: number } }"#),
  });

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
import dep = require("dep");
const y: dep.Foo = { x: 1 };
export const z = y.x;
"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("z").expect("export z");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported z");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn export_import_equals_entity_name_is_exported() {
  let mut host = MemoryHost::new();
  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
namespace Bar { export const Baz = 1 as const; }
export import Foo = Bar.Baz;
export const x = Foo;
"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);

  let foo = exports.get("Foo").expect("export Foo");
  let foo_ty = foo
    .type_id
    .or_else(|| foo.def.map(|def| program.type_of_def(def)))
    .expect("type for exported Foo");
  assert_eq!(program.display_type(foo_ty).to_string(), "1");

  let x = exports.get("x").expect("export x");
  let x_ty = x
    .type_id
    .or_else(|| x.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(x_ty).to_string(), "1");
}

#[test]
fn export_import_equals_require_is_exported() {
  let mut host = MemoryHost::new();
  let dep = FileKey::new("dep.ts");
  host.insert(dep, "export const value: number = 1;");

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"export import Foo = require("./dep"); export const x = Foo.value;"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  assert!(
    exports.contains_key("Foo"),
    "export Foo missing: {exports:?}"
  );

  let x = exports.get("x").expect("export x");
  let x_ty = x
    .type_id
    .or_else(|| x.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn import_equals_entity_name_does_not_make_file_a_module() {
  let mut host = MemoryHost::new();
  let a = FileKey::new("a.ts");
  host.insert(
    a.clone(),
    r#"
namespace N { export const x = 1 as const; }
import Alias = N.x;
"#,
  );
  let b = FileKey::new("b.ts");
  host.insert(b.clone(), r#"export const y = N.x;"#);

  let program = Program::new(host, vec![a, b.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&b).expect("file id for b.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("y").expect("export y");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported y");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn import_equals_entity_name_aliases_namespace_import_member() {
  let mut host = MemoryHost::new();
  let dep = FileKey::new("dep.ts");
  host.insert(dep, "export const Baz = 1 as const;");

  let main = FileKey::new("main.ts");
  host.insert(
    main.clone(),
    r#"
import * as Bar from "./dep";
import Foo = Bar.Baz;
export const x = Foo;
"#,
  );

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("x").expect("export x");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn ambient_modules_in_dts_do_not_make_globals_module_scoped() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;

  let mut host = MemoryHost::with_options(options);
  host.add_lib(LibFile {
    key: FileKey::new("globals.d.ts"),
    name: Arc::from("globals.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare const globalX: string;
declare module "foo" { export const x: number; }
"#,
    ),
  });

  let main = FileKey::new("main.ts");
  host.insert(main.clone(), "export const y = globalX;");

  let program = Program::new(host, vec![main.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&main).expect("file id for main.ts");
  let exports = program.exports_of(file_id);
  let entry = exports.get("y").expect("export y");
  let ty = entry
    .type_id
    .or_else(|| entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported y");
  assert_eq!(program.display_type(ty).to_string(), "string");
}
