use std::sync::Arc;

use hir_js::LocalKind;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn body_local_var_can_capture_function_param() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("file0.ts");
  let source = "function f(x: number) { const y = x; return y; }";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(diagnostics.is_empty(), "diagnostics: {diagnostics:?}");

  let file_id = program.file_id(&file).expect("file id");
  // Body-local `y` is LocalId-only; init expr lives in the function body.
  assert!(
    program
      .definitions_in_file(file_id)
      .into_iter()
      .all(|def| program.def_name(def).as_deref() != Some("y")),
    "body-local y must not allocate a DefId"
  );

  let f_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("f"))
    .expect("function f");
  let f_body = program.body_of_def(f_def).expect("f body");
  let result = program.check_body(f_body);
  assert!(
    result.diagnostics().is_empty(),
    "body diagnostics: {:?}",
    result.diagnostics()
  );

  let x_offset =
    u32::try_from(source.find("= x").expect("`= x` in source") + 2).expect("offset fits in u32");
  let (_, x_ty) = result
    .expr_at(x_offset)
    .expect("expected `x` expr in function body");
  assert_eq!(program.display_type(x_ty).to_string(), "number");

  let lowered = program.hir_lowered(file_id).expect("hir");
  let body = lowered.body(f_body).expect("hir body");
  let (y_local, _) = body
    .locals_with_kind(LocalKind::Var)
    .find(|(_, local)| lowered.names.resolve(local.name) == Some("y"))
    .expect("y local");
  let y_ty = program.type_of_local(f_body, y_local);
  assert_eq!(program.display_type(y_ty).to_string(), "number");
}
