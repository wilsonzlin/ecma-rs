#![cfg(feature = "serde")]

use std::sync::Arc;

use semantic_js as semjs;
use semjs::ts as sem_ts;
use serde_json;
use typecheck_ts::semantic_js as public_semantic_js;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn symbol_id_roundtrips_without_truncation() {
  let semantic = sem_ts::SymbolId(u64::MAX - 42);
  let public: public_semantic_js::SymbolId = semantic.into();
  assert_eq!(public.0, semantic.0, "public SymbolId must keep full range");

  let roundtrip: sem_ts::SymbolId = public.into();
  assert_eq!(roundtrip.0, semantic.0, "conversion back must be lossless");

  let serialized = serde_json::to_string(&public).expect("serialize symbol id");
  let decoded: public_semantic_js::SymbolId =
    serde_json::from_str(&serialized).expect("deserialize symbol id");
  assert_eq!(
    decoded, public,
    "serde should preserve the full 64-bit symbol id"
  );
}

#[test]
fn snapshot_preserves_symbol_ids() {
  let mut host = MemoryHost::new();
  let file = FileKey::new("file.ts");
  let source = "export const value = 1; const use = value;";
  host.insert(file.clone(), Arc::from(source.to_string()));

  let program = Program::new(host.clone(), vec![file.clone()]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_id = program.file_id(&file).expect("file id");
  let decl_offset = source.find("value").expect("decl offset") as u32;
  let use_offset = source.rfind("value").expect("use offset") as u32;
  let decl_symbol = program
    .symbol_at(file_id, decl_offset)
    .expect("declaration symbol");
  let use_symbol = program.symbol_at(file_id, use_offset).expect("use symbol");
  assert_eq!(
    decl_symbol, use_symbol,
    "symbol ids should match before snapshot"
  );

  let snapshot = program.snapshot();
  let restored = Program::from_snapshot(host, snapshot);
  let restored_file = restored.file_id(&file).expect("restored file id");
  let restored_decl = restored
    .symbol_at(restored_file, decl_offset)
    .expect("restored decl symbol");
  let restored_use = restored
    .symbol_at(restored_file, use_offset)
    .expect("restored use symbol");

  assert_eq!(
    restored_decl, decl_symbol,
    "decl symbol should persist in snapshot"
  );
  assert_eq!(
    restored_use, use_symbol,
    "use symbol should persist in snapshot"
  );
}
