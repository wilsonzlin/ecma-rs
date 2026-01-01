use std::sync::Arc;

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

  let defs = program.definitions_in_file(file_id);
  let x_defs: Vec<_> = defs
    .into_iter()
    .filter(|def| program.def_name(*def).as_deref() == Some("x"))
    .collect();
  assert!(!x_defs.is_empty(), "expected x parameter def");
  for def in x_defs {
    let ty = program.type_of_def(def);
    assert_ne!(program.display_type(ty).to_string(), "unknown");
  }
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

  let defs = program.definitions_in_file(file_id);
  let x_def = defs
    .iter()
    .copied()
    .find(|def| program.def_name(*def).as_deref() == Some("x"))
    .expect("x parameter def");
  let y_def = defs
    .iter()
    .copied()
    .find(|def| program.def_name(*def).as_deref() == Some("y"))
    .expect("y parameter def");

  assert_eq!(
    program.display_type(program.type_of_def(x_def)).to_string(),
    "number"
  );
  assert_eq!(
    program.display_type(program.type_of_def(y_def)).to_string(),
    "string"
  );
}
