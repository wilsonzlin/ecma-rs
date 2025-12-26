use std::collections::HashMap;
use std::sync::Arc;

use serde_json;
use typecheck_ts::{FileId, Host, HostError, Program, ProgramSnapshot};

#[derive(Clone, Default)]
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
fn snapshot_roundtrips_queries() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let exports = program.exports_of(FileId(0));
  let total_entry = exports.values.get("total").expect("total export present");
  let total_def = total_entry.def.expect("total def");
  let total_type = total_entry.type_id.expect("total type");
  let total_body = program.body_of_def(total_def).expect("body for total");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let type_at_call = program
    .type_at(FileId(0), call_offset)
    .expect("type at call");

  let snapshot = program.snapshot();
  let serialized = serde_json::to_string_pretty(&snapshot).expect("serialize snapshot");
  let restored_snapshot: ProgramSnapshot =
    serde_json::from_str(&serialized).expect("deserialize snapshot");
  let restored = Program::from_snapshot(host, restored_snapshot);

  assert_eq!(restored.check(), diagnostics);

  let restored_exports = restored.exports_of(FileId(0));
  let restored_total = restored_exports
    .values
    .get("total")
    .expect("restored total export");
  assert_eq!(restored_total.type_id, Some(total_type));
  let restored_body = restored.body_of_def(total_def).expect("restored body");
  assert_eq!(restored_body, total_body);
  let restored_type_at = restored
    .type_at(FileId(0), call_offset)
    .expect("restored type");
  assert_eq!(restored_type_at, type_at_call);
}

#[test]
fn snapshot_serialization_is_deterministic() {
  let mut host = MemoryHost::default();
  host.insert(FileId(10), "export const value = 1 + 2;");

  let program = Program::new(host, vec![FileId(10)]);
  program.check();

  let snap_a = program.snapshot();
  let snap_b = program.snapshot();

  let json_a = serde_json::to_string_pretty(&snap_a).expect("serialize snapshot");
  let json_b = serde_json::to_string_pretty(&snap_b).expect("serialize snapshot");

  assert_eq!(json_a, json_b, "snapshots must be byte-stable");
}
