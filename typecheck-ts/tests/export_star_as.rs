use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn export_star_as_namespace_is_typed_and_resolves_through_imports() {
  let mut host = MemoryHost::new();

  let dep_key = FileKey::new("dep.ts");
  host.insert(
    dep_key.clone(),
    "export const value: number = 1;\nexport interface Foo { x: number; }\n",
  );

  let root_key = FileKey::new("root.ts");
  host.insert(root_key.clone(), "export * as ns from \"./dep\";\n");

  let entry_key = FileKey::new("entry.ts");
  host.insert(
    entry_key.clone(),
    "import { ns } from \"./root\";\n\
     export const v = ns.value;\n\
     export const typed: ns.Foo = { x: 1 };\n\
     export const x = typed.x;\n",
  );

  let program = Program::new(host, vec![entry_key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let root_id = program.file_id(&root_key).expect("root.ts file id");
  let entry_id = program.file_id(&entry_key).expect("entry.ts file id");

  let exports_root = program.exports_of(root_id);
  let ns_entry = exports_root.get("ns").expect("ns export in root.ts");
  let ns_ty = ns_entry.type_id.expect("type for ns export");
  assert_eq!(
    program.display_type(ns_ty).to_string(),
    "{ readonly value: number }",
    "ns should be typed as a module namespace object with value exports"
  );

  let exports_entry = program.exports_of(entry_id);
  let v_ty = exports_entry
    .get("v")
    .and_then(|entry| entry.type_id)
    .expect("type for v export");
  assert_eq!(program.display_type(v_ty).to_string(), "number");

  let x_ty = exports_entry
    .get("x")
    .and_then(|entry| entry.type_id)
    .expect("type for x export");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn export_star_as_namespace_supports_string_literal_aliases() {
  let mut host = MemoryHost::new();

  let dep_key = FileKey::new("dep.ts");
  host.insert(
    dep_key.clone(),
    "export const value: number = 1;\nexport interface Foo { x: number; }\n",
  );

  let root_key = FileKey::new("root.ts");
  host.insert(
    root_key.clone(),
    "export * as \"ns-name\" from \"./dep\";\n",
  );

  let entry_key = FileKey::new("entry.ts");
  host.insert(
    entry_key.clone(),
    "import { \"ns-name\" as ns } from \"./root\";\n\
     export const v = ns.value;\n\
     export const typed: ns.Foo = { x: 1 };\n\
     export const x = typed.x;\n",
  );

  let program = Program::new(host, vec![entry_key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let root_id = program.file_id(&root_key).expect("root.ts file id");
  let entry_id = program.file_id(&entry_key).expect("entry.ts file id");

  let exports_root = program.exports_of(root_id);
  let ns_entry = exports_root
    .get("ns-name")
    .expect("ns-name export in root.ts");
  let ns_ty = ns_entry.type_id.expect("type for ns-name export");
  assert_eq!(
    program.display_type(ns_ty).to_string(),
    "{ readonly value: number }",
    "ns-name should be typed as a module namespace object with value exports"
  );

  let exports_entry = program.exports_of(entry_id);
  let v_ty = exports_entry
    .get("v")
    .and_then(|entry| entry.type_id)
    .expect("type for v export");
  assert_eq!(program.display_type(v_ty).to_string(), "number");

  let x_ty = exports_entry
    .get("x")
    .and_then(|entry| entry.type_id)
    .expect("type for x export");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn export_type_star_as_namespace_supports_string_literal_aliases() {
  let mut host = MemoryHost::new();

  let dep_key = FileKey::new("dep.ts");
  host.insert(dep_key.clone(), "export interface Foo { x: number; }\n");

  let root_key = FileKey::new("root.ts");
  host.insert(
    root_key.clone(),
    "export type * as \"ns-name\" from \"./dep\";\n",
  );

  let entry_key = FileKey::new("entry.ts");
  host.insert(
    entry_key.clone(),
    "import type { \"ns-name\" as ns } from \"./root\";\n\
     export const typed: ns.Foo = { x: 1 };\n\
     export const x = typed.x;\n",
  );

  let program = Program::new(host, vec![entry_key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&entry_key).expect("entry.ts file id");
  let exports_entry = program.exports_of(entry_id);
  let x_ty = exports_entry
    .get("x")
    .and_then(|entry| entry.type_id)
    .expect("type for x export");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}

#[test]
fn type_only_reexport_of_namespace_export_preserves_namespace_slot() {
  let mut host = MemoryHost::new();

  let dep_key = FileKey::new("dep.ts");
  host.insert(dep_key.clone(), "export interface Foo { x: number; }\n");

  let root_key = FileKey::new("root.ts");
  host.insert(
    root_key.clone(),
    "export * as \"ns-name\" from \"./dep\";\n",
  );

  let mid_key = FileKey::new("mid.ts");
  host.insert(
    mid_key.clone(),
    "export type { \"ns-name\" as ns } from \"./root\";\n",
  );

  let entry_key = FileKey::new("entry.ts");
  host.insert(
    entry_key.clone(),
    "import type { ns } from \"./mid\";\n\
     export const typed: ns.Foo = { x: 1 };\n\
     export const x = typed.x;\n",
  );

  let program = Program::new(host, vec![entry_key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&entry_key).expect("entry.ts file id");
  let exports_entry = program.exports_of(entry_id);
  let x_ty = exports_entry
    .get("x")
    .and_then(|entry| entry.type_id)
    .expect("type for x export");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}
