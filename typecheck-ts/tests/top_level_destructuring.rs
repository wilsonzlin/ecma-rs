use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{FileKey, Host, HostError, Program};

#[derive(Default)]
struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
  edges: HashMap<(FileKey, String), FileKey>,
}

impl MemoryHost {
  fn insert(&mut self, key: FileKey, source: &str) {
    self.files.insert(key, Arc::from(source.to_string()));
  }

  #[allow(dead_code)]
  fn link(&mut self, from: FileKey, specifier: &str, to: FileKey) {
    self.edges.insert((from, specifier.to_string()), to);
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, spec: &str) -> Option<FileKey> {
    self.edges.get(&(from.clone(), spec.to_string())).cloned()
  }
}

#[test]
fn export_const_object_destructuring_uses_pattern_types() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("object_destructuring.ts");
  host.insert(
    key.clone(),
    r#"
      type Value = { a: number; b: { c: string } };
      const value: Value = { a: 1, b: { c: "hi" } };
      export const { a, b: { c } } = value;
    "#,
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);

  let a = exports.get("a").expect("a export");
  let a_type = a.type_id.expect("a type");
  assert_eq!(program.display_type(a_type).to_string(), "number");

  let c = exports.get("c").expect("c export");
  let c_type = c.type_id.expect("c type");
  assert_eq!(program.display_type(c_type).to_string(), "string");
}

#[test]
fn export_list_after_array_destructuring_exports_bound_names() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("array_destructuring.ts");
  host.insert(
    key.clone(),
    r#"
      const tuple: [number, string] = [1, "two"];
      const [x, y] = tuple;
      export { x, y };
    "#,
  );

  let program = Program::new(host, vec![key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&key).expect("file id");
  let exports = program.exports_of(file_id);

  let x = exports.get("x").expect("x export");
  let x_type = x.type_id.expect("x type");
  assert_eq!(program.display_type(x_type).to_string(), "number");

  let y = exports.get("y").expect("y export");
  let y_type = y.type_id.expect("y type");
  assert_eq!(program.display_type(y_type).to_string(), "string");
}

