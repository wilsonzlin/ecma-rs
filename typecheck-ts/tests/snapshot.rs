use std::sync::Arc;

use serde_json;
use typecheck_ts::{FileKey, MemoryHost, Program, ProgramSnapshot};

#[test]
fn snapshot_roundtrips_queries() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  let entry = FileKey::new("entry.ts");
  let math = FileKey::new("math.ts");
  host.insert(entry.clone(), Arc::from(entry_source.to_string()));
  host.insert(math.clone(), Arc::from(math_source.to_string()));
  host.link(entry.clone(), "./math", math.clone());

  let program = Program::new(host.clone(), vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&entry).unwrap();
  let _math_id = program.file_id(&math).unwrap();
  let exports = program.exports_of(entry_id);
  let total_entry = exports.get("total").expect("total export present");
  let total_def = total_entry.def.expect("total def");
  let total_type = total_entry.type_id.expect("total type");
  let total_body = program.body_of_def(total_def).expect("body for total");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let type_at_call = program
    .type_at(entry_id, call_offset)
    .expect("type at call");

  let snapshot = program.snapshot();
  let serialized = serde_json::to_string_pretty(&snapshot).expect("serialize snapshot");
  let restored_snapshot: ProgramSnapshot =
    serde_json::from_str(&serialized).expect("deserialize snapshot");
  let restored = Program::from_snapshot(host, restored_snapshot);

  assert_eq!(restored.check(), diagnostics);

  let restored_entry_id = restored.file_id(&entry).unwrap();
  let restored_exports = restored.exports_of(restored_entry_id);
  let restored_total = restored_exports
    .get("total")
    .expect("restored total export");
  assert_eq!(restored_total.type_id, Some(total_type));
  let restored_body = restored.body_of_def(total_def).expect("restored body");
  assert_eq!(restored_body, total_body);
  let restored_type_at = restored
    .type_at(restored_entry_id, call_offset)
    .expect("restored type");
  assert_eq!(restored_type_at, type_at_call);
}

#[test]
fn snapshot_serialization_is_deterministic() {
  let mut host = MemoryHost::default();
  let key = FileKey::new("file.ts");
  host.insert(key.clone(), Arc::from("export const value = 1 + 2;"));

  let program = Program::new(host, vec![key]);
  program.check();

  let snap_a = program.snapshot();
  let snap_b = program.snapshot();

  let json_a = serde_json::to_string_pretty(&snap_a).expect("serialize snapshot");
  let json_b = serde_json::to_string_pretty(&snap_b).expect("serialize snapshot");

  assert_eq!(json_a, json_b, "snapshots must be byte-stable");
}
