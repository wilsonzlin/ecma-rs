use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts::{codes, FileKey, Host, HostError, Program, TextRange};

fn fk(id: u32) -> FileKey {
  FileKey::new(format!("file{id}.ts"))
}

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
  edges: HashMap<(FileKey, String), FileKey>,
}

impl MemoryHost {
  fn insert(&mut self, key: FileKey, source: &str) {
    self.files.insert(key, Arc::from(source.to_string()));
  }

  fn link(&mut self, from: FileKey, specifier: &str, to: FileKey) {
    self.edges.insert((from, specifier.to_string()), to);
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, spec: &str) -> Option<FileKey> {
    self.edges.get(&(from.clone(), spec.to_string())).cloned()
  }
}

#[test]
fn value_exports_follow_reexport_chain() {
  let mut host = MemoryHost::default();
  let key_a = fk(0);
  let key_b = fk(1);
  let key_c = fk(2);
  host.insert(key_a.clone(), "export const foo: number = 1;");
  host.insert(key_b.clone(), "export { foo as bar } from \"./a\";");
  host.insert(key_c.clone(), "export * from \"./b\";");
  host.link(key_b.clone(), "./a", key_a.clone());
  host.link(key_c.clone(), "./b", key_b.clone());

  let program = Program::new(host, vec![key_c.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_a = program.file_id(&key_a).expect("file a");
  let file_b = program.file_id(&key_b).expect("file b");
  let file_c = program.file_id(&key_c).expect("file c");

  let exports_b = program.exports_of(file_b);
  let bar_entry_b = exports_b.get("bar").expect("bar export in module b");
  assert!(bar_entry_b.def.is_none());
  let bar_type_b = bar_entry_b.type_id.expect("type for bar in module b");
  assert_eq!(program.display_type(bar_type_b).to_string(), "number");

  let exports_c = program.exports_of(file_c);
  let bar_entry_c = exports_c.get("bar").expect("bar export in module c");
  assert!(bar_entry_c.def.is_none());
  let bar_type_c = bar_entry_c.type_id.expect("type for bar in module c");
  assert_eq!(program.display_type(bar_type_c).to_string(), "number");

  let exports_a = program.exports_of(file_a);
  let foo_entry = exports_a.get("foo").expect("foo export in module a");
  assert!(foo_entry.def.is_some());
  let foo_type = foo_entry.type_id.expect("type for foo");
  assert_eq!(program.display_type(foo_type).to_string(), "number");
}

#[test]
fn default_export_has_type() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("default.ts");
  host.insert(key.clone(), "export default 42;");

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
  let default_entry = exports.get("default").expect("default export");
  assert!(default_entry.def.is_some());
  let ty = default_entry.type_id.expect("type for default");
  assert_eq!(program.display_type(ty).to_string(), "42");
}

#[test]
fn type_exports_propagate_through_reexports() {
  let mut host = MemoryHost::default();
  let key_types = fk(20);
  let key_entry = fk(21);
  host.insert(key_types.clone(), "export type Foo = { a: string };");
  host.insert(key_entry.clone(), "export type { Foo } from \"./types\";");
  host.link(key_entry.clone(), "./types", key_types.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&key_entry).expect("entry id");
  let exports_types = program.exports_of(entry_id);
  let foo = exports_types.get("Foo").expect("Foo type export");
  assert!(foo.def.is_none(), "re-export should not point to local def");
  let foo_ty = foo.type_id.expect("type for Foo");
  let rendered = program.display_type(foo_ty).to_string();
  assert!(
    rendered.contains("a: string"),
    "expected object type, got {rendered}"
  );
}

#[test]
fn export_star_cycle_reaches_fixpoint() {
  let mut host = MemoryHost::default();
  let key_a = fk(210);
  let key_b = fk(211);
  let key_c = fk(212);
  host.insert(
    key_a.clone(),
    "export * from \"./b\";\nexport * from \"./c\";",
  );
  host.insert(key_b.clone(), "export * from \"./a\";");
  host.insert(key_c.clone(), "export const shared = 1;");
  host.link(key_a.clone(), "./b", key_b.clone());
  host.link(key_a.clone(), "./c", key_c.clone());
  host.link(key_b.clone(), "./a", key_a.clone());

  let program = Program::new(host, vec![key_a.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  for key in [key_a, key_b, key_c] {
    let file = program.file_id(&key).expect("file id");
    let exports = program.exports_of(file);
    let shared = exports.get("shared").expect("shared export present");
    let ty = shared.type_id.expect("type for shared");
    assert_eq!(program.display_type(ty).to_string(), "1");
  }
}

#[test]
fn export_star_skips_default() {
  let mut host = MemoryHost::default();
  let key_a = fk(220);
  let key_b = fk(221);
  host.insert(key_a.clone(), "export default 1;\nexport const named = 2;");
  host.insert(key_b.clone(), "export * from \"./a\";");
  host.link(key_b.clone(), "./a", key_a.clone());

  let program = Program::new(host, vec![key_b.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_b = program.file_id(&key_b).expect("file id");
  let exports = program.exports_of(file_b);
  assert!(
    exports.get("default").is_none(),
    "default should not be re-exported"
  );
  let named = exports.get("named").expect("named export propagated");
  let ty = named.type_id.expect("type for named");
  assert_eq!(program.display_type(ty).to_string(), "2");
}

#[test]
fn duplicate_export_reports_conflict() {
  let mut host = MemoryHost::default();
  let key_a = fk(230);
  let key_b = fk(231);
  let key_c = fk(232);
  host.insert(key_a.clone(), "export const foo = 1;");
  host.insert(key_b.clone(), "export function foo(): number { return 2; }");
  host.insert(
    key_c.clone(),
    "export * from \"./a\";\nexport { foo } from \"./b\";",
  );
  host.link(key_c.clone(), "./a", key_a.clone());
  host.link(key_c.clone(), "./b", key_b.clone());

  let program = Program::new(host, vec![key_c.clone()]);
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1, "expected a conflict diagnostic");
  assert_eq!(diagnostics[0].code.as_str(), "BIND1001");
  let file_c = program.file_id(&key_c).expect("file c");
  assert_eq!(diagnostics[0].primary.file, file_c);
}

#[test]
fn namespace_exports_include_namespace_slot() {
  let mut host = MemoryHost::default();
  let key = fk(30);
  host.insert(
    key.clone(),
    "export function foo() { return 1; }\nexport namespace foo { }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);
  let value_entry = exports.get("foo").expect("value export foo");
  assert!(
    value_entry.type_id.is_some(),
    "merged namespace/value should carry a type"
  );
}

#[test]
fn export_star_conflict_reports_diagnostic() {
  let mut host = MemoryHost::default();
  let key_one = fk(100);
  let key_two = fk(101);
  let key_entry = fk(102);
  host.insert(key_one.clone(), "export const dup = 1;");
  host.insert(key_two.clone(), "export const dup = 2;");
  host.insert(
    key_entry.clone(),
    "export * from \"./one\";\nexport * from \"./two\";",
  );
  host.link(key_entry.clone(), "./one", key_one.clone());
  host.link(key_entry.clone(), "./two", key_two.clone());

  let program = Program::new(host, vec![key_entry.clone()]);
  let diagnostics = program.check();
  assert_eq!(diagnostics.len(), 1, "expected conflict diagnostic");
  assert_eq!(diagnostics[0].code.as_str(), "BIND1001");
}

#[test]
fn export_namespace_all_reports_diagnostic() {
  let mut host = MemoryHost::default();
  let key_a = fk(300);
  let key_b = fk(301);
  host.insert(key_a.clone(), "export const a = 1;");
  host.insert(key_b.clone(), "export * as ns from \"./a\";");
  host.link(key_b.clone(), "./a", key_a.clone());

  let program = Program::new(host, vec![key_b.clone()]);
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
fn unresolved_export_points_at_specifier() {
  let mut host = MemoryHost::default();
  let source = r#"export * from "./missing";"#;
  let key = fk(350);
  host.insert(key.clone(), source);

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert_eq!(
    diagnostics.len(),
    1,
    "expected unresolved module diagnostic"
  );
  let diag = &diagnostics[0];
  assert_eq!(diag.code.as_str(), codes::UNRESOLVED_MODULE.as_str());
  let file_id = program.file_id(&key).expect("file id");
  assert_eq!(diag.primary.file, file_id);

  let specifier = "\"./missing\"";
  let start = source.find(specifier).expect("missing specifier in source") as u32;
  let end = start + specifier.len() as u32;
  let expected_span = TextRange::new(start, end);
  assert!(
    diag.primary.range.start <= expected_span.start && diag.primary.range.end >= expected_span.end,
    "diagnostic span {:?} should cover specifier {:?}",
    diag.primary.range,
    expected_span
  );
}

#[test]
fn interned_type_for_exported_function() {
  let mut host = MemoryHost::default();
  let key = fk(50);
  host.insert(
    key.clone(),
    "export function add(a: number, b: number): number { return a + b; }",
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
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
  let key = fk(40);
  host.insert(key.clone(), "type Node = Node;");

  let program = Program::new(host, vec![key.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&key).expect("file id");
  let def = program
    .definitions_in_file(file_id)
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
