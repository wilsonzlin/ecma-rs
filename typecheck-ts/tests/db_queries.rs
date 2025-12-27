use std::sync::Arc;

use diagnostics::FileId;
use typecheck_ts::db::TypecheckDb;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{FileKey, FileOrigin};

fn def_by_name<'a>(lowered: &'a hir_js::LowerResult, name: &str) -> &'a hir_js::DefData {
  lowered
    .defs
    .iter()
    .find(|def| lowered.names.resolve(def.name) == Some(name))
    .expect("definition present")
}

#[test]
fn nested_function_body_parent_and_file_lookup() {
  let mut db = TypecheckDb::default();
  let file = FileId(0);
  let key = FileKey::new("main.ts");
  let source = "function outer() { function inner() { return 1; } return inner(); }";
  db.set_file(
    file,
    key.clone(),
    FileKind::Ts,
    Arc::from(source),
    FileOrigin::Source,
  );
  db.set_roots(Arc::from([key]));

  let lowered = db.lower_hir(file).lowered.expect("lowered HIR");
  let outer = def_by_name(&lowered, "outer");
  let inner = def_by_name(&lowered, "inner");
  let outer_body = outer.body.expect("outer has a body");
  let inner_body = inner.body.expect("inner has a body");

  assert_eq!(db.body_file(inner_body), Some(file));
  assert_eq!(db.body_file(outer_body), Some(file));
  assert_eq!(db.body_parent(inner_body), Some(outer_body));
}

#[test]
fn indices_are_deterministic_across_root_order() {
  let file_a = FileId(0);
  let key_a = FileKey::new("a.ts");
  let file_b = FileId(1);
  let key_b = FileKey::new("b.ts");

  let mut db_ordered = TypecheckDb::default();
  db_ordered.set_file(
    file_a,
    key_a.clone(),
    FileKind::Ts,
    Arc::from("export function a() {}"),
    FileOrigin::Source,
  );
  db_ordered.set_file(
    file_b,
    key_b.clone(),
    FileKind::Ts,
    Arc::from("export function b() {}"),
    FileOrigin::Source,
  );
  db_ordered.set_roots(Arc::from([key_a.clone(), key_b.clone()]));

  let mut db_reversed = TypecheckDb::default();
  db_reversed.set_file(
    file_a,
    key_a.clone(),
    FileKind::Ts,
    Arc::from("export function a() {}"),
    FileOrigin::Source,
  );
  db_reversed.set_file(
    file_b,
    key_b.clone(),
    FileKind::Ts,
    Arc::from("export function b() {}"),
    FileOrigin::Source,
  );
  db_reversed.set_roots(Arc::from([key_b, key_a]));

  let ordered_defs = db_ordered.def_to_file();
  let ordered_bodies = db_ordered.body_to_file();
  let reversed_defs = db_reversed.def_to_file();
  let reversed_bodies = db_reversed.body_to_file();

  assert_eq!(*ordered_defs, *reversed_defs);
  assert_eq!(*ordered_bodies, *reversed_bodies);
}
