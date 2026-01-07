use std::sync::Arc;

use typecheck_ts::{FileKey, MemoryHost, Program};

fn positions_of(source: &str, needle: &str) -> Vec<u32> {
  source
    .match_indices(needle)
    .map(|(idx, _)| idx as u32)
    .collect()
}

#[test]
fn script_ts_file_hoists_block_function_decls() {
  let mut host = MemoryHost::default();
  let source = "function outer(){ if(true){ function foo(){} foo; } foo; }";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");

  let positions = positions_of(source, "foo");
  assert_eq!(positions.len(), 3, "expected 3 foo occurrences");

  let decl_symbol = program
    .symbol_at(file_id, positions[0])
    .expect("foo declaration symbol");
  let inner_use_symbol = program
    .symbol_at(file_id, positions[1])
    .expect("inner foo reference");
  let outer_use_symbol = program
    .symbol_at(file_id, positions[2])
    .expect("outer foo reference");

  assert_eq!(
    decl_symbol, inner_use_symbol,
    "block-local foo reference should resolve to the declaration"
  );
  assert_eq!(
    decl_symbol, outer_use_symbol,
    "script semantics should hoist block-level function declarations"
  );
}

#[test]
fn module_ts_file_keeps_block_function_decls_scoped() {
  let mut host = MemoryHost::default();
  let source = "export {};\nfunction outer(){ if(true){ function foo(){} foo; } foo; }";
  let file = FileKey::new("file.ts");
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");

  let positions = positions_of(source, "foo");
  assert_eq!(positions.len(), 3, "expected 3 foo occurrences");

  let decl_symbol = program
    .symbol_at(file_id, positions[0])
    .expect("foo declaration symbol");
  let inner_use_symbol = program
    .symbol_at(file_id, positions[1])
    .expect("inner foo reference");
  let outer_use_symbol = program.symbol_at(file_id, positions[2]);

  assert_eq!(
    decl_symbol, inner_use_symbol,
    "block-local foo reference should resolve to the declaration"
  );
  assert!(
    outer_use_symbol.is_none(),
    "module semantics should not hoist block-level function declarations"
  );
}
