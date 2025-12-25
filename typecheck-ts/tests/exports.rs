use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts::{FileId, Host, HostError, Program};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileId, Arc<str>>,
  edges: HashMap<(FileId, String), FileId>,
}

impl MemoryHost {
  fn insert(&mut self, id: FileId, source: &str) {
    self.files.insert(id, Arc::from(source.to_string()));
  }

  fn link(&mut self, from: FileId, specifier: &str, to: FileId) {
    self.edges.insert((from, specifier.to_string()), to);
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: FileId, spec: &str) -> Option<FileId> {
    self.edges.get(&(from, spec.to_string())).copied()
  }
}

#[test]
fn exports_follow_reexport_chain() {
  let mut host = MemoryHost::default();
  host.insert(FileId(0), "export const foo: number = 1;");
  host.insert(FileId(1), "export { foo as bar } from \"./a\";");
  host.insert(FileId(2), "export * from \"./b\";");
  host.link(FileId(1), "./a", FileId(0));
  host.link(FileId(2), "./b", FileId(1));

  let program = Program::new(host, vec![FileId(2)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let exports_b = program.exports_of(FileId(1));
  let bar_entry_b = exports_b.get("bar").expect("bar export in module b");
  assert!(bar_entry_b.def.is_none());
  let bar_type_b = bar_entry_b.type_id.expect("type for bar in module b");
  assert_eq!(program.display_type(bar_type_b).to_string(), "number");

  let exports_c = program.exports_of(FileId(2));
  let bar_entry_c = exports_c.get("bar").expect("bar export in module c");
  assert!(bar_entry_c.def.is_none());
  let bar_type_c = bar_entry_c.type_id.expect("type for bar in module c");
  assert_eq!(program.display_type(bar_type_c).to_string(), "number");

  let exports_a = program.exports_of(FileId(0));
  let foo_entry = exports_a.get("foo").expect("foo export in module a");
  assert!(foo_entry.def.is_some());
  let foo_type = foo_entry.type_id.expect("type for foo");
  assert_eq!(program.display_type(foo_type).to_string(), "number");
}

#[test]
fn default_export_has_type() {
  let mut host = MemoryHost::default();
  host.insert(FileId(10), "export default 42;");

  let program = Program::new(host, vec![FileId(10)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let exports = program.exports_of(FileId(10));
  let default_entry = exports.get("default").expect("default export");
  assert!(default_entry.def.is_some());
  let ty = default_entry.type_id.expect("type for default");
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn type_only_exports_filtered() {
  let mut host = MemoryHost::default();
  host.insert(
    FileId(20),
    "export type Foo = { a: string };\nexport const value = 1;",
  );

  let program = Program::new(host, vec![FileId(20)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let exports = program.exports_of(FileId(20));
  assert!(
    exports.get("Foo").is_none(),
    "type-only export should be filtered"
  );
  let value_entry = exports.get("value").expect("value export");
  let ty = value_entry.type_id.expect("type for value");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
