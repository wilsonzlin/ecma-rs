use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn const_type_annotation_overrides_literal_initializer() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let source = r#"
const init: string = "";
export const result = init;
"#;
  host.insert(file.clone(), source);

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");

  let init_defs: Vec<_> = program
    .definitions_in_file(file_id)
    .into_iter()
    .filter(|d| program.def_name(*d) == Some("init".to_string()))
    .collect();
  assert_eq!(
    init_defs.len(),
    1,
    "expected exactly one `init` definition, got {init_defs:?}"
  );
  let init_ty = program.type_of_def(init_defs[0]);
  assert_eq!(
    program.display_type(init_ty).to_string(),
    "string",
    "`init` should be widened to its annotation"
  );

  let exports = program.exports_of(file_id);
  let result_def = exports
    .get("result")
    .and_then(|e| e.def)
    .expect("result export def");

  let init_offset = source
    .find("result = init")
    .map(|idx| idx as u32 + "result = ".len() as u32)
    .expect("offset for init usage");
  let init_use_ty = program
    .type_at(file_id, init_offset)
    .expect("type at init usage");
  assert_eq!(
    program.display_type(init_use_ty).to_string(),
    "string",
    "`init` usage should have type `string`"
  );

  let ty = program.type_of_def(result_def);
  assert_eq!(
    program.display_type(ty).to_string(),
    "string",
    "const initializer should be widened to the declared annotation"
  );
}
