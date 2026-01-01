use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn snapshot_roundtrip_preserves_export_star_as_namespace() {
  let mut host = MemoryHost::new();

  let dep_key = FileKey::new("dep.ts");
  host.insert(dep_key.clone(), "export const value: number = 1;\n");

  let root_key = FileKey::new("root.ts");
  host.insert(root_key.clone(), "export * as ns from \"./dep\";\n");

  let program = Program::new(host.clone(), vec![root_key.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let snapshot = program.snapshot();
  let restored = Program::from_snapshot(host, snapshot);

  let root_id = restored.file_id(&root_key).expect("root.ts file id");
  let exports = restored.exports_of(root_id);
  let ns_entry = exports.get("ns").expect("ns export preserved in snapshot");
  let ns_ty = ns_entry.type_id.expect("type for ns export");

  assert_eq!(
    restored.display_type(ns_ty).to_string(),
    "{ readonly value: number }"
  );
}

#[test]
fn export_star_as_namespace_is_cycle_safe() {
  let mut host = MemoryHost::new();

  let a_key = FileKey::new("a.ts");
  host.insert(a_key.clone(), "export * as ns from \"./b\";\n");

  let b_key = FileKey::new("b.ts");
  host.insert(b_key.clone(), "export * as ns from \"./a\";\n");

  let program = Program::new(host, vec![a_key.clone()]);
  let _ = program.check();

  let a_id = program.file_id(&a_key).expect("a.ts file id");
  let b_id = program.file_id(&b_key).expect("b.ts file id");

  let ns_a_1 = program
    .exports_of(a_id)
    .get("ns")
    .and_then(|entry| entry.type_id)
    .expect("ns export and type in a.ts");
  let ns_a_2 = program
    .exports_of(a_id)
    .get("ns")
    .and_then(|entry| entry.type_id)
    .expect("ns export and type in a.ts (repeat)");
  assert_eq!(ns_a_1, ns_a_2, "a.ts namespace type must be deterministic");

  let ns_b_1 = program
    .exports_of(b_id)
    .get("ns")
    .and_then(|entry| entry.type_id)
    .expect("ns export and type in b.ts");
  let ns_b_2 = program
    .exports_of(b_id)
    .get("ns")
    .and_then(|entry| entry.type_id)
    .expect("ns export and type in b.ts (repeat)");
  assert_eq!(ns_b_1, ns_b_2, "b.ts namespace type must be deterministic");

  // Ensure the types can be rendered without re-entering module namespace typing.
  let display_a = program.display_type(ns_a_1).to_string();
  let display_b = program.display_type(ns_b_1).to_string();
  assert!(
    !display_a.is_empty() && !display_b.is_empty(),
    "namespace exports should render to a non-empty type"
  );
}
