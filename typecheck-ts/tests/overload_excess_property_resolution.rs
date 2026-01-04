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
fn overload_resolution_skips_signatures_with_excess_properties() {
  let mut host = MemoryHost::default();
  let source = r#"
declare function f(x: { a: number }): 1;
declare function f(x: { a: number; b: number }): 2;

export const r = f({ a: 1, b: 2 });
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
  assert_eq!(program.display_type(r_ty).to_string(), "2");
}

#[test]
fn overload_resolution_skips_signatures_with_nested_excess_properties() {
  let mut host = MemoryHost::default();
  let source = r#"
declare function f(x: { nested: { a: number } }): 1;
declare function f(x: { nested: { a: number; b: number } }): 2;

export const r = f({ nested: { a: 1, b: 2 } });
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
  assert_eq!(program.display_type(r_ty).to_string(), "2");
}

#[test]
fn overload_resolution_skips_signatures_with_array_element_excess_properties() {
  let mut host = MemoryHost::default();
  let source = r#"
declare function f(xs: { a: number }[]): 1;
declare function f(xs: { a: number; b: number }[]): 2;

export const r = f([{ a: 1, b: 2 }]);
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
  assert_eq!(program.display_type(r_ty).to_string(), "2");
}

#[test]
fn overload_resolution_skips_signatures_with_excess_properties_when_spread_is_present() {
  let mut host = MemoryHost::default();
  let source = r#"
declare function f(x: { a: number }, ...rest: any[]): 1;
declare function f(x: { a: number; b: number }, ...rest: any[]): 2;

const rest: any[] = [];
export const r = f({ a: 1, b: 2 }, ...rest);
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
  assert_eq!(program.display_type(r_ty).to_string(), "2");
}
