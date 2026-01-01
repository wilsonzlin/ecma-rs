use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn initializer_body_can_capture_function_param() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file0.ts");
  let source = "function f(x: number) { const y = x; return y; }";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id");
  let y_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("y"))
    .expect("expected `y` definition");
  let y_body = program
    .body_of_def(y_def)
    .expect("expected initializer body for `y`");

  let result = program.check_body(y_body);
  assert!(
    result.diagnostics().is_empty(),
    "initializer diagnostics: {:?}",
    result.diagnostics()
  );

  let x_offset =
    u32::try_from(source.find("= x").expect("`= x` in source") + 2).expect("offset fits in u32");
  let (_, x_ty) = result
    .expr_at(x_offset)
    .expect("expected `x` expr in initializer");
  assert_eq!(program.display_type(x_ty).to_string(), "number");
}
