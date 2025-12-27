use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn value_binding_type_id_used_for_builtins() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("a.ts");
  let src = "const x = undefined;";
  host.insert(file.clone(), src);

  let program = Program::new(host, vec![file.clone()]);
  let globals = program.global_bindings();
  let undefined_binding = globals
    .get("undefined")
    .expect("undefined binding available globally");
  let undefined_ty = undefined_binding.type_id.expect("undefined binding type");
  assert_eq!(program.display_type(undefined_ty).to_string(), "undefined");

  let file_id = program.file_id(&file).expect("file id");
  let body = program.file_body(file_id).expect("top-level body");

  let result = program.check_body(body);
  assert!(
    result.diagnostics().is_empty(),
    "unexpected diagnostics: {:?}",
    result.diagnostics()
  );
  let offset = src.find("undefined").expect("offset for undefined") as u32;
  let ty = program.type_at(file_id, offset).expect("type at undefined");
  assert_eq!(program.display_type(ty).to_string(), "undefined");
}
