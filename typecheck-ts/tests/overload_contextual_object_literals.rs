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
fn overload_resolution_uses_contextual_object_literal_types() {
  let mut host = MemoryHost::default();
  let source = r#"
declare function f(x: { kind: "a" }): 1;
declare function f(x: { kind: "b" }): 2;
declare function f(x: { kind: string }): 3;

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
