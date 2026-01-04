use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

fn def_by_name(program: &Program, file: FileKey, name: &str) -> typecheck_ts::DefId {
  let file_id = program.file_id(&file).expect("file id");
  program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("definition {name} not found"))
}

#[test]
fn type_param_constraint_makes_value_callable() {
  let mut host = MemoryHost::default();
  let source = r#"
function takes<T extends (x: { kind: "a" }) => 1>(f: T) {
  return f({ kind: "a" });
}

const fn: (x: { kind: "a" }) => 1 = (x) => 1;
export const r = takes(fn);
"#;
  let file = FileKey::new("input.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );

  let file_id = program.file_id(&file).expect("file id");
  let call_offset = source
    .find("f({ kind: \"a\" })")
    .expect("call expression offset") as u32
    + 1;
  let call_ty = program
    .type_at(file_id, call_offset)
    .expect("call expression type");
  assert_eq!(program.display_type(call_ty).to_string(), "1");

  let r_def = def_by_name(&program, file.clone(), "r");
  let r_ty = program.type_of_def_interned(r_def);
  assert_eq!(program.display_type(r_ty).to_string(), "number");
}

#[test]
fn type_param_constraint_makes_value_constructable() {
  let mut host = MemoryHost::default();
  let source = r#"
function make<T extends { new (x: { kind: "a" }): 1 }>(C: T) {
  return new C({ kind: "a" });
}

declare const C: { new (x: { kind: "a" }): 1 };
export const r = make(C);
"#;
  let file = FileKey::new("input.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {:?}",
    diagnostics
  );

  let file_id = program.file_id(&file).expect("file id");
  let new_offset = source
    .find("new C({ kind: \"a\" })")
    .expect("new expression offset") as u32;
  let new_ty = program
    .type_at(file_id, new_offset)
    .expect("new expression type");
  assert_eq!(program.display_type(new_ty).to_string(), "1");

  let r_def = def_by_name(&program, file.clone(), "r");
  let r_ty = program.type_of_def_interned(r_def);
  assert_eq!(program.display_type(r_ty).to_string(), "number");
}
