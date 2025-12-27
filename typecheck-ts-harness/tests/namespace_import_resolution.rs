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
fn resolves_qualified_types_through_namespace_imports() {
  let mut host = MemoryHost::default();
  let key_m = FileKey::new("m.ts");
  let key_re = FileKey::new("re.ts");
  let key_a = FileKey::new("a.ts");

  host.insert(
    key_m.clone(),
    "export interface Foo {\n  x: number;\n}\n",
  );
  host.insert(key_re.clone(), "export * from \"./m\";\n");
  host.insert(
    key_a.clone(),
    "import * as NS from \"./re\";\nlet v: NS.Foo;\nv.x;\n",
  );
  host.link(key_re.clone(), "./m", key_m.clone());
  host.link(key_a.clone(), "./re", key_re.clone());

  let program = Program::new(host, vec![key_a.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_a = program.file_id(&key_a).expect("file id for a.ts");
  let src = program.file_text(file_a).expect("source for a.ts");
  let offset = src.find("v.x").expect("member expression offset") as u32 + 2;
  let ty = program
    .type_at(file_a, offset)
    .expect("type for v.x expression");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
