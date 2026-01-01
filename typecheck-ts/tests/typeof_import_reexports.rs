use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program, TypeKindSummary};

fn type_alias_kind(program: &Program, entry: &FileKey, name: &str) -> TypeKindSummary {
  let file_id = program.file_id(entry).expect("file id for entry");
  let def = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|def| program.def_name(*def).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("type alias {name}"));
  program.type_kind(program.type_of_def(def))
}

#[test]
fn typeof_import_module_namespace_includes_reexports() {
  let mut host = MemoryHost::new();
  let entry = FileKey::new("entry.ts");
  let root = FileKey::new("root.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(root.clone(), Arc::from(r#"export { value } from "./dep";"#));
  host.insert(dep.clone(), Arc::from("export const value: number = 1;"));
  host.insert(
    entry.clone(),
    Arc::from(
      r#"
type M = typeof import("./root");
type U = M["value"];
"#,
    ),
  );
  host.link(entry.clone(), "./root", root.clone());
  host.link(root.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  assert_eq!(
    type_alias_kind(&program, &entry, "U"),
    TypeKindSummary::Number
  );
}

#[test]
fn typeof_import_module_namespace_includes_export_star_as_alias() {
  let mut host = MemoryHost::new();
  let entry = FileKey::new("entry.ts");
  let root = FileKey::new("root.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(root.clone(), Arc::from(r#"export * as ns from "./dep";"#));
  host.insert(dep.clone(), Arc::from("export const value: number = 1;"));
  host.insert(
    entry.clone(),
    Arc::from(
      r#"
type M = typeof import("./root");
type U = M["ns"]["value"];
"#,
    ),
  );
  host.link(entry.clone(), "./root", root.clone());
  host.link(root.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  assert_eq!(
    type_alias_kind(&program, &entry, "U"),
    TypeKindSummary::Number
  );
}

#[test]
fn typeof_import_dot_access_resolves_export_star_as_alias_namespace() {
  let mut host = MemoryHost::new();
  let entry = FileKey::new("entry.ts");
  let root = FileKey::new("root.ts");
  let dep = FileKey::new("dep.ts");

  host.insert(root.clone(), Arc::from(r#"export * as ns from "./dep";"#));
  host.insert(dep.clone(), Arc::from("export const value: number = 1;"));
  host.insert(
    entry.clone(),
    Arc::from(
      r#"
type Ns = typeof import("./root").ns;
type U = Ns["value"];
"#,
    ),
  );
  host.link(entry.clone(), "./root", root.clone());
  host.link(root.clone(), "./dep", dep.clone());

  let program = Program::new(host, vec![entry.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  assert_eq!(
    type_alias_kind(&program, &entry, "U"),
    TypeKindSummary::Number
  );
}
