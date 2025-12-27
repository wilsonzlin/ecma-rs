use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn class_value_static_property_type() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("a.ts");
  let src = r#"class C { static x: number = 1; }
const y = C.x;
"#;
  host.insert(file.clone(), src);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id");
  let offset = src.find("C.x").expect("offset for C.x") as u32 + 2;
  let ty = program.type_at(file_id, offset).expect("type at C.x");
  assert_eq!(program.display_type(ty).to_string(), "number");
}
