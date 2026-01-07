use std::sync::Arc;

use diagnostics::FileId;
use typecheck_ts::db::TypecheckDb;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{decl_types_call_count, reset_decl_types_call_count, FileKey, FileOrigin};

#[test]
fn decl_types_query_is_incremental_per_file() {
  reset_decl_types_call_count();
  let mut db = TypecheckDb::default();
  let file_a = FileId(0);
  let key_a = FileKey::new("a.ts");
  let file_b = FileId(1);
  let key_b = FileKey::new("b.ts");
  db.set_file(
    file_a,
    key_a.clone(),
    FileKind::Ts,
    Arc::from("type A = number;"),
    FileOrigin::Source,
  );
  db.set_file(
    file_b,
    key_b.clone(),
    FileKind::Ts,
    Arc::from("type B = string;"),
    FileOrigin::Source,
  );
  db.set_roots(Arc::from([key_a.clone(), key_b.clone()]));

  let _ = db.decl_types(file_a);
  let _ = db.decl_types(file_b);
  assert_eq!(decl_types_call_count(), 2);

  db.set_file_text(file_a, Arc::from("type A = number | boolean;"));
  let _ = db.decl_types(file_a);
  let _ = db.decl_types(file_b);
  assert_eq!(decl_types_call_count(), 3);
}
