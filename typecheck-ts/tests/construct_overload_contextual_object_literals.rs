use std::sync::Arc;

mod common;

use typecheck_ts::lib_support::CompilerOptions;
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
fn construct_overload_resolution_uses_contextual_object_literal_types() {
  let mut host = MemoryHost::with_options(CompilerOptions {
    no_default_lib: true,
    ..CompilerOptions::default()
  });
  host.add_lib(common::core_globals_lib());
  let source = r#"
declare const C: {
  new (x: { kind: "a" }): 1;
  new (x: { kind: "b" }): 2;
  new (x: { kind: string }): 3;
};

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
