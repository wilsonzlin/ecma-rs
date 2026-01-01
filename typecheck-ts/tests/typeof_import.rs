use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program, TypeKindSummary};

#[test]
fn typeof_import_qualifier_resolves_exported_value_type() {
  let mut host = MemoryHost::new();
  let entry = FileKey::new("entry.ts");
  let dep = FileKey::new("dep.ts");
  host.insert(
    entry.clone(),
    Arc::from(r#"type T = typeof import("./dep").value;"#),
  );
  host.insert(dep.clone(), Arc::from("export const value: number = 1;"));
  host.link(entry.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id for entry");
  let t_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("T"))
    .expect("type alias T");
  let ty = program.type_of_def(t_def);
  assert_eq!(program.type_kind(ty), TypeKindSummary::Number);
}

#[test]
fn typeof_import_module_namespace_exposes_exports() {
  let mut host = MemoryHost::new();
  let entry = FileKey::new("entry.ts");
  let dep = FileKey::new("dep.ts");
  host.insert(
    entry.clone(),
    Arc::from(
      r#"
type M = typeof import("./dep");
type U = M["value"];
"#,
    ),
  );
  host.insert(dep.clone(), Arc::from("export const value: number = 1;"));
  host.link(entry.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let file_id = program.file_id(&entry).expect("file id for entry");
  let u_def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some("U"))
    .expect("type alias U");
  let ty = program.type_of_def(u_def);
  assert_eq!(program.type_kind(ty), TypeKindSummary::Number);
}
