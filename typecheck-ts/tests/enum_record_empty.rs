use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn empty_object_to_record_enum_is_ts2741() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
enum E { A }
let foo: Record<E, any> = {}
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.to_string()).collect();
  assert!(
    codes.iter().any(|c| c == "TS2741"),
    "expected TS2741 for empty object vs Record<E,any>, got {diags:?}"
  );
}

#[test]
fn empty_object_to_record_string_key_is_ts2741() {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
let foo: Record<"a", any> = {}
"#,
  );
  let program = Program::new(host, vec![file]);
  let diags = program.check();
  let codes: Vec<_> = diags.iter().map(|d| d.code.to_string()).collect();
  assert!(
    codes.iter().any(|c| c == "TS2741"),
    "expected TS2741 for empty object vs Record<\"a\",any>, got {diags:?}"
  );
}
