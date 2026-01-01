use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn inferred_return_preserves_object_destructuring_params() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "export function f({x}: {x: number}) { return x + 1; }",
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let entry = exports.get("f").expect("export f");
  let ty = entry.type_id.expect("type for f");
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1, "expected single call signature");
  assert_eq!(sigs[0].signature.params.len(), 1);
  assert_eq!(
    program.display_type(sigs[0].signature.ret).to_string(),
    "number"
  );
}

#[test]
fn inferred_return_preserves_array_destructuring_params() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "export function g([x, y]: [number, string]) { return y; }",
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let exports = program.exports_of(file_id);
  let entry = exports.get("g").expect("export g");
  let ty = entry.type_id.expect("type for g");
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1, "expected single call signature");
  assert_eq!(sigs[0].signature.params.len(), 1);
  assert_eq!(
    program.display_type(sigs[0].signature.ret).to_string(),
    "string"
  );
}
