use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::lib_support::{CompilerOptions, FileKind};
use typecheck_ts::{FileKey, Host, HostError, Program};

#[derive(Default)]
struct ModuleHost {
  files: HashMap<FileKey, Arc<str>>,
  edges: HashMap<(FileKey, String), FileKey>,
  options: CompilerOptions,
}

impl ModuleHost {
  fn new(options: CompilerOptions) -> Self {
    ModuleHost {
      files: HashMap::new(),
      edges: HashMap::new(),
      options,
    }
  }

  fn insert(&mut self, key: FileKey, text: &str) {
    self.files.insert(key, Arc::from(text));
  }

  fn link(&mut self, from: FileKey, specifier: &str, to: FileKey) {
    self.edges.insert((from, specifier.to_string()), to);
  }
}

impl Host for ModuleHost {
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

  fn file_kind(&self, file: &FileKey) -> FileKind {
    if file.as_str().ends_with(".d.ts") {
      FileKind::Dts
    } else {
      FileKind::Ts
    }
  }
}

#[test]
fn ambient_module_exports_resolve_through_host_module_mapping() {
  let options = CompilerOptions::default();
  // Keep bundled libs enabled so primitives like `number` are available without
  // requiring additional host-provided lib files.

  let entry = FileKey::new("main.ts");
  let ambient = FileKey::new("ambient_mod.d.ts");

  let mut host = ModuleHost::new(options);
  host.insert(
    ambient.clone(),
    r#"
export {};
declare module "pkg" {
  export const x: number;
}
"#,
  );
  host.insert(
    entry.clone(),
    r#"
import { x } from "pkg";
const y = x;
"#,
  );
  // Allow `declare module "pkg"` to augment the resolved module.
  host.link(entry.clone(), "pkg", ambient.clone());
  host.link(ambient.clone(), "pkg", ambient.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics when importing from ambient module: {diagnostics:?}"
  );

  let entry_id = program.file_id(&entry).expect("main.ts id");
  let y_def = program
    .definitions_in_file(entry_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("y"))
    .expect("definition for y");

  let rendered = program.display_type(program.type_of_def(y_def)).to_string();
  assert_eq!(rendered, "number");
}

#[test]
fn import_equals_require_resolves_namespace_members_through_host_mapped_ambient_export_assignment()
{
  let options = CompilerOptions::default();
  // Keep bundled libs enabled so primitives like `number` are available without
  // requiring additional host-provided lib files.

  let entry = FileKey::new("main.ts");
  let ambient = FileKey::new("ambient_mod.d.ts");

  let mut host = ModuleHost::new(options);
  host.insert(
    ambient.clone(),
    r#"
export {};
declare module "pkg" {
  declare function Foo(): 1;
  declare namespace Foo {
    export interface Bar {
      x: number;
    }
  }
  export = Foo;
}
"#,
  );
  host.insert(
    entry.clone(),
    r#"
import Foo = require("pkg");
const y: Foo.Bar = { x: 123 };
export const z = y.x;
"#,
  );
  // Allow `declare module "pkg"` to augment the resolved module.
  host.link(entry.clone(), "pkg", ambient.clone());
  host.link(ambient.clone(), "pkg", ambient.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&entry).expect("main.ts id");
  let exports = program.exports_of(entry_id);
  let z_entry = exports.get("z").expect("export z");
  let z_ty = z_entry
    .type_id
    .or_else(|| z_entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported z");
  assert_eq!(program.display_type(z_ty).to_string(), "number");
}

#[test]
fn import_equals_require_resolves_ambient_export_assignment_through_host_module_mapping() {
  let options = CompilerOptions::default();
  // Keep bundled libs enabled so primitives like literal types are available without
  // requiring additional host-provided lib files.

  let entry = FileKey::new("main.ts");
  let ambient = FileKey::new("ambient_mod.d.ts");

  let mut host = ModuleHost::new(options);
  host.insert(
    ambient.clone(),
    r#"
export {};
declare module "pkg" {
  declare const foo: 1;
  export = foo;
}
"#,
  );
  host.insert(
    entry.clone(),
    r#"
import foo = require("pkg");
export const x: 1 = foo;
"#,
  );
  // Allow `declare module "pkg"` to augment the resolved module.
  host.link(entry.clone(), "pkg", ambient.clone());
  host.link(ambient.clone(), "pkg", ambient.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics when importing an ambient export assignment: {diagnostics:?}"
  );

  let entry_id = program.file_id(&entry).expect("main.ts id");
  let exports = program.exports_of(entry_id);
  let x_entry = exports.get("x").expect("export x");
  let x_ty = x_entry
    .type_id
    .or_else(|| x_entry.def.map(|def| program.type_of_def(def)))
    .expect("type for exported x");
  assert_eq!(program.display_type(x_ty).to_string(), "1");
}
