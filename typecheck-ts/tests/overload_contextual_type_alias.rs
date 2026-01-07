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
fn overload_contextual_typing_works_through_type_alias() {
  let mut host = MemoryHost::default();
  let source = r#"
type F = {
  (x: { kind: "a" }): 1;
  (x: { kind: string }): 2;
};

declare const f: F;
export const r = f({ kind: "a" });
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

  let r_def = def_by_name(&program, file.clone(), "r");
  let r_ty = program.type_of_def_interned(r_def);
  assert_eq!(program.display_type(r_ty).to_string(), "1");
}

#[test]
fn construct_overload_contextual_typing_works_through_type_alias() {
  let mut host = MemoryHost::default();
  let source = r#"
type Ctor = {
  new (x: { kind: "a" }): 1;
  new (x: { kind: string }): 2;
};

declare const C: Ctor;
export const r = new C({ kind: "a" });
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

  let r_def = def_by_name(&program, file.clone(), "r");
  let r_ty = program.type_of_def_interned(r_def);
  assert_eq!(program.display_type(r_ty).to_string(), "1");
}
