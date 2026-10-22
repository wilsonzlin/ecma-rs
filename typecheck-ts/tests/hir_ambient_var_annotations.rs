//! HIR-only binder slice: ambient / `declare` var annotations are consumed from
//! `hir_js::DefData::declared_type` (not binder AST `type_from_type_expr`).
//!
//! Binder leaves `VarData.typ` unset when HIR is present; `type_of_def` lowers
//! via `hir_declared_type_for_def`.

use typecheck_ts::{FileKey, MemoryHost, Program};
use types_ts_interned::TypeKind;

#[test]
fn declare_var_annotation_from_hir() {
  let file = FileKey::new("globals.d.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    "declare var VERSION: string; declare let COUNT: number;",
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let version = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("VERSION"))
    .expect("VERSION");
  let count = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("COUNT"))
    .expect("COUNT");

  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(version)),
      TypeKind::String
    ),
    "VERSION should be string from HIR declared_type"
  );
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(count)),
      TypeKind::Number
    ),
    "COUNT should be number from HIR declared_type"
  );
}

#[test]
fn ambient_module_exported_var_annotation_from_hir() {
  let file = FileKey::new("ambient.d.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      declare module "pkg" {
        export const flag: boolean;
        export var name: string;
      }
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let flag = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("flag"))
    .expect("flag");
  let name = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("name"))
    .expect("name");

  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(flag)),
      TypeKind::Boolean
    ),
    "flag should be boolean from HIR declared_type"
  );
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(name)),
      TypeKind::String
    ),
    "name should be string from HIR declared_type"
  );
}

#[test]
fn namespace_ambient_var_annotation_from_hir() {
  // Namespace-nested declare vars are outside the top-level collect paths;
  // type_of_def must still lower annotations from HIR.
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(
    file.clone(),
    r#"
      namespace N {
        export declare const id: string;
        export declare let n: number;
      }
    "#,
  );
  let program = Program::new(host, vec![file.clone()]);
  let _ = program.check();

  let file_id = program.file_id(&file).expect("file id");
  let id = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("id"))
    .expect("id");
  let n = program
    .definitions_in_file(file_id)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("n"))
    .expect("n");

  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(id)),
      TypeKind::String
    ),
    "id should be string from HIR declared_type"
  );
  assert!(
    matches!(
      program.interned_type_kind(program.type_of_def(n)),
      TypeKind::Number
    ),
    "n should be number from HIR declared_type"
  );
}
