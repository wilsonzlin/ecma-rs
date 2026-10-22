use std::sync::Arc;

use hir_js::LocalKind;
use typecheck_ts::codes;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn destructured_object_params_are_typed() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let source: Arc<str> = Arc::from("export function f({x}: {x: number}) { return x; }");
  host.insert(file.clone(), Arc::clone(&source));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::UNSUPPORTED_PARAM_PATTERN.as_str()),
    "unexpected unsupported parameter pattern diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let offset =
    source.rfind("return x").expect("x in return statement") as u32 + "return ".len() as u32;
  let ty = program.type_at(file_id, offset).expect("type at x");
  assert_eq!(program.display_type(ty).to_string(), "number");

  // Params are LocalId-only: query via type_of_local.
  let lowered = program.hir_lowered(file_id).expect("hir");
  let f_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("f"))
    .expect("function f");
  let body_id = program.body_of_def(f_def).expect("body");
  let body = lowered.body(body_id).expect("hir body");
  let (x_local_id, _) = body
    .locals_with_kind(LocalKind::Param)
    .find(|(_, local)| lowered.names.resolve(local.name) == Some("x"))
    .expect("x param local");
  let ty = program.type_of_local(body_id, x_local_id);
  assert_eq!(program.display_type(ty).to_string(), "number");
}

#[test]
fn destructured_array_params_are_typed() {
  let mut host = MemoryHost::default();
  let file = FileKey::new("main.ts");
  let source: Arc<str> = Arc::from("export function g([x, y]: [number, string]) { return y; }");
  host.insert(file.clone(), Arc::clone(&source));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::UNSUPPORTED_PARAM_PATTERN.as_str()),
    "unexpected unsupported parameter pattern diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let offset =
    source.rfind("return y").expect("y in return statement") as u32 + "return ".len() as u32;
  let ty = program.type_at(file_id, offset).expect("type at y");
  assert_eq!(program.display_type(ty).to_string(), "string");

  let lowered = program.hir_lowered(file_id).expect("hir");
  let g_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("g"))
    .expect("function g");
  let body_id = program.body_of_def(g_def).expect("body");
  let body = lowered.body(body_id).expect("hir body");

  let mut by_name = std::collections::BTreeMap::new();
  for (local_id, local) in body.locals_with_kind(LocalKind::Param) {
    let name = lowered.names.resolve(local.name).unwrap().to_string();
    let ty = program.type_of_local(body_id, local_id);
    by_name.insert(name, program.display_type(ty).to_string());
  }
  assert_eq!(by_name.get("x").map(String::as_str), Some("number"));
  assert_eq!(by_name.get("y").map(String::as_str), Some("string"));
}
