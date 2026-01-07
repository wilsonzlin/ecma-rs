use std::sync::Arc;

use diagnostics::FileId;
use typecheck_ts::db::{local_symbol_info, symbol_occurrences, Database};
use typecheck_ts::lib_support::FileKind;
use typecheck_ts::{parse_call_count, reset_parse_call_count, FileKey, FileOrigin};

#[test]
fn symbol_queries_reuse_cached_parse() {
  let mut db = Database::default();
  let file = FileId(0);
  let key = FileKey::new("symbols.ts");
  db.set_file(
    file,
    key.clone(),
    FileKind::Ts,
    Arc::from("export function foo() { const x = 1; return x; }"),
    FileOrigin::Source,
  );
  db.set_roots(Arc::from([key].as_slice()));

  reset_parse_call_count();
  let parsed = db.parse(file);
  assert!(parsed.ast.is_some(), "test input should parse successfully");

  let parses_after_parse = parse_call_count();
  let occs = symbol_occurrences(&db, file);
  assert!(!occs.is_empty(), "symbol occurrences should be populated");
  let locals = local_symbol_info(&db, file);
  assert!(
    !locals.is_empty(),
    "local symbol info should include nested bindings"
  );

  assert_eq!(
    parse_call_count(),
    parses_after_parse,
    "symbol queries should not require reparsing once the AST is cached"
  );
}
