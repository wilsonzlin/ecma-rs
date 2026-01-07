use std::sync::Arc;

use diagnostics::FileId;
use typecheck_ts::db::Database;
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{parse_call_count, reset_parse_call_count, FileKey, FileOrigin};

#[test]
fn parse_query_uses_cache() {
  let mut db = Database::default();
  let file = FileId(0);
  let key = FileKey::new("entry.ts");
  db.set_file(
    file,
    key,
    FileKind::Ts,
    Arc::from("export const value = 1;"),
    FileOrigin::Source,
  );

  reset_parse_call_count();

  let first = db.parse(file);
  assert!(
    first.diagnostics.is_empty(),
    "parsing should succeed without diagnostics"
  );

  let after_first = parse_call_count();
  assert_eq!(
    after_first, 1,
    "parsing should increment the counter exactly once"
  );
  let second = db.parse(file);

  assert_eq!(
    after_first,
    parse_call_count(),
    "cached query should not re-run the parse implementation"
  );
  let shared_ast = first
    .ast
    .as_ref()
    .zip(second.ast.as_ref())
    .map(|(a, b)| Arc::ptr_eq(a, b))
    .unwrap_or(false);
  assert!(shared_ast, "cached query results should be shared");
}

#[test]
fn parse_query_only_recomputes_changed_files() {
  let mut db = Database::default();
  let file0 = FileId(0);
  let file1 = FileId(1);
  db.set_file(
    file0,
    FileKey::new("file0.ts"),
    FileKind::Ts,
    Arc::from("export const a = 1;"),
    FileOrigin::Source,
  );
  db.set_file(
    file1,
    FileKey::new("file1.ts"),
    FileKind::Ts,
    Arc::from("export const b = 2;"),
    FileOrigin::Source,
  );

  reset_parse_call_count();
  let _ = db.parse(file0);
  let _ = db.parse(file1);
  assert_eq!(
    parse_call_count(),
    2,
    "expected both files to be parsed once"
  );

  reset_parse_call_count();
  db.set_file_text(file0, Arc::from("export const a: string = 1;"));
  let _ = db.parse(file0);
  let _ = db.parse(file1);
  assert_eq!(
    parse_call_count(),
    1,
    "only the changed file should be reparsed"
  );
}
