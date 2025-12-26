use std::sync::Arc;
use typecheck_ts::codes;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn exports_follow_reexport_chain() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  let file_c = FileKey::new("c.ts");
  host.insert(file_a.clone(), Arc::from("export const foo: number = 1;"));
  host.insert(file_b.clone(), Arc::from("export { foo as bar } from \"./a\";"));
  host.insert(file_c.clone(), Arc::from("export * from \"./b\";"));
  host.link(file_b.clone(), "./a", file_a.clone());
  host.link(file_c.clone(), "./b", file_b.clone());

  let program = Program::new(host, vec![file_c.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let id_a = program.file_id(&file_a).unwrap();
  let id_b = program.file_id(&file_b).unwrap();
  let id_c = program.file_id(&file_c).unwrap();
  let exports_b = program.exports_of(id_b);
  let bar_entry_b = exports_b.get("bar").expect("bar export in module b");
  assert!(bar_entry_b.def.is_none());
  let bar_type_b = bar_entry_b.type_id.expect("type for bar in module b");
  assert_eq!(program.display_type(bar_type_b).to_string(), "number");

  let exports_c = program.exports_of(id_c);
  let bar_entry_c = exports_c.get("bar").expect("bar export in module c");
  assert!(bar_entry_c.def.is_none());
  let bar_type_c = bar_entry_c.type_id.expect("type for bar in module c");
  assert_eq!(program.display_type(bar_type_c).to_string(), "number");

  let exports_a = program.exports_of(id_a);
  let foo_entry = exports_a.get("foo").expect("foo export in module a");
  assert!(foo_entry.def.is_some());
  let foo_type = foo_entry.type_id.expect("type for foo");
  assert_eq!(program.display_type(foo_type).to_string(), "number");
}

#[test]
fn default_export_has_type() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("default.ts");
  host.insert(file.clone(), Arc::from("export default 42;"));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).unwrap();
  let exports = program.exports_of(file_id);
  let default_entry = exports.get("default").expect("default export");
  assert!(default_entry.def.is_some());
  let ty = default_entry.type_id.expect("type for default");
  assert_eq!(program.display_type(ty).to_string(), "42");
}

#[test]
fn type_only_exports_filtered() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("type_only.ts");
  host.insert(
    file.clone(),
    Arc::from("export type Foo = { a: string };\nexport const value = 1;"),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).unwrap();
  let exports = program.exports_of(file_id);
  assert!(
    exports.get("Foo").is_none(),
    "type-only export should be filtered"
  );
  let value_entry = exports.get("value").expect("value export");
  let ty = value_entry.type_id.expect("type for value");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn missing_reexport_emits_diagnostic() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(file_a.clone(), Arc::from("export const foo = 1;"));
  host.insert(file_b.clone(), Arc::from("export { bar } from \"./a\";"));
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b.clone()]);
  let file_b_id = program.file_id(&file_b).unwrap();
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1, "expected a single diagnostic");
  assert_eq!(diagnostics[0].code.as_str(), codes::UNKNOWN_EXPORT.as_str());
  assert_eq!(diagnostics[0].primary.file, file_b_id);
  assert!(
    diagnostics[0].primary.range.len() > 0,
    "diagnostic should point at the invalid specifier"
  );

  let exports = program.exports_of(file_b_id);
  assert!(
    exports.get("bar").is_none(),
    "invalid re-export should be absent"
  );
}

#[test]
fn type_only_reexports_filtered() {
  let mut host = MemoryHost::default();
  let file_types = FileKey::new("types.ts");
  let file_entry = FileKey::new("entry.ts");
  host.insert(file_types.clone(), Arc::from("export type Foo = { a: string };"));
  host.insert(
    file_entry.clone(),
    Arc::from("export { Foo } from \"./types\";\nexport const value = 1;"),
  );
  host.link(file_entry.clone(), "./types", file_types.clone());

  let program = Program::new(host, vec![file_entry.clone()]);
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1, "expected missing export diagnostic");
  assert_eq!(diagnostics[0].code.as_str(), codes::UNKNOWN_EXPORT.as_str());

  let file_entry_id = program.file_id(&file_entry).unwrap();
  let exports = program.exports_of(file_entry_id);
  assert!(
    exports.get("Foo").is_none(),
    "type-only re-export should be ignored"
  );
  let value = exports.get("value").expect("value export present");
  let ty = value.type_id.expect("type for value");
  assert_eq!(program.display_type(ty).to_string(), "1");
}

#[test]
fn export_namespace_all_reports_diagnostic() {
  let mut host = MemoryHost::default();
  let file_a = FileKey::new("a.ts");
  let file_b = FileKey::new("b.ts");
  host.insert(file_a.clone(), Arc::from("export const a = 1;"));
  host.insert(file_b.clone(), Arc::from("export * as ns from \"./a\";"));
  host.link(file_b.clone(), "./a", file_a.clone());

  let program = Program::new(host, vec![file_b]);
  let diagnostics = program.check();
  assert_eq!(
    diagnostics.len(),
    1,
    "expected unsupported pattern diagnostic"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::UNSUPPORTED_PATTERN.as_str()
  );
}

#[test]
fn interned_type_for_exported_function() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("add.ts");
  host.insert(
    file.clone(),
    Arc::from("export function add(a: number, b: number): number { return a + b; }"),
  );

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let def = program
    .definitions_in_file(program.file_id(&file).unwrap())
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("add"))
    .expect("add definition");
  let ty = program.type_of_def(def);
  assert_eq!(
    program.display_type(ty).to_string(),
    "(number, number) => number"
  );
}

#[test]
fn recursive_type_alias_produces_ref() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("node.ts");
  host.insert(file.clone(), Arc::from("type Node = Node;"));

  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let def = program
    .definitions_in_file(program.file_id(&file).unwrap())
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Node"))
    .expect("Node alias");
  let ty = program.type_of_def(def);
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("Node"),
    "expected recursive alias to render as Node, got {rendered}"
  );
}
