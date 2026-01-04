use std::collections::HashMap;
use std::sync::Arc;

use serde_json;
use typecheck_ts::{
  lib_support::CompilerOptions, parse_call_count, reset_parse_call_count, FileId, FileKey, Host,
  HostError, Program, ProgramSnapshot, QueryKind,
};

fn key(id: FileId) -> FileKey {
  FileKey::new(format!("file{}.ts", id.0))
}

#[derive(Clone, Default)]
struct MemoryHost {
  files: HashMap<FileKey, Arc<str>>,
  edges: HashMap<(FileKey, String), FileKey>,
  options: CompilerOptions,
}

impl MemoryHost {
  fn insert(&mut self, id: FileId, source: &str) {
    self.files.insert(key(id), Arc::from(source.to_string()));
  }

  fn link(&mut self, from: FileId, specifier: &str, to: FileId) {
    self
      .edges
      .insert((key(from), specifier.to_string()), key(to));
  }
}

impl Host for MemoryHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, spec: &str) -> Option<FileKey> {
    self.edges.get(&(from.clone(), spec.to_string())).cloned()
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }
}

#[test]
fn snapshot_roundtrips_queries() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_entry = program.file_id(&key(FileId(0))).expect("entry id");
  let exports = program.exports_of(file_entry);
  let total_entry = exports.get("total").expect("total export present");
  let total_def = total_entry.def.expect("total def");
  let total_type = total_entry.type_id.expect("total type");
  let total_body = program.body_of_def(total_def).expect("body for total");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let type_at_call = program
    .type_at(file_entry, call_offset)
    .expect("type at call");

  let snapshot = program.snapshot();
  let serialized = serde_json::to_string_pretty(&snapshot).expect("serialize snapshot");
  let restored_snapshot: ProgramSnapshot =
    serde_json::from_str(&serialized).expect("deserialize snapshot");
  let restored = Program::from_snapshot(host, restored_snapshot);

  assert_eq!(restored.check(), diagnostics);

  let restored_entry = restored.file_id(&key(FileId(0))).expect("restored entry");
  let restored_exports = restored.exports_of(restored_entry);
  let restored_total = restored_exports
    .get("total")
    .expect("restored total export");
  assert_eq!(restored_total.type_id, Some(total_type));
  let restored_body = restored.body_of_def(total_def).expect("restored body");
  assert_eq!(restored_body, total_body);
  let restored_type_at = restored
    .type_at(restored_entry, call_offset)
    .expect("restored type");
  if restored_type_at != type_at_call {
    panic!(
      "snapshot type mismatch: original {:?} restored {:?}",
      type_at_call, restored_type_at
    );
  }
}

#[test]
fn snapshot_roundtrips_type_package_roots() {
  let mut host = MemoryHost::default();
  host.options.types = vec!["example".to_string()];
  let entry_source = "const value = example;";
  let types_source = "declare const example: string;";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), types_source);
  host.link(FileId(0), "example", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&key(FileId(0))).expect("entry id");
  let types_id = program.file_id(&key(FileId(1))).expect("types id");
  let reachable = program.reachable_files();
  assert!(
    reachable.contains(&types_id),
    "reachable files should include type package root: {reachable:?}"
  );

  let snapshot = program.snapshot();
  let restored = Program::from_snapshot(host, snapshot);
  assert_eq!(restored.check(), diagnostics);

  let restored_entry = restored.file_id(&key(FileId(0))).expect("restored entry");
  let restored_types = restored.file_id(&key(FileId(1))).expect("restored types");
  assert_eq!(restored_entry, entry_id);
  assert_eq!(restored_types, types_id);

  let restored_reachable = restored.reachable_files();
  assert!(
    restored_reachable.contains(&restored_types),
    "restored reachable files should include type package root: {restored_reachable:?}"
  );
}

#[test]
fn snapshot_restoration_loads_missing_source_text_from_host() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
  let file_entry = program.file_id(&key(FileId(0))).expect("entry id");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let type_at_call = program
    .type_at(file_entry, call_offset)
    .expect("type at call");

  let mut snapshot = program.snapshot();
  for file in snapshot.files.iter_mut() {
    if !file.is_lib {
      file.text = None;
    }
  }
  let restored = Program::from_snapshot(host, snapshot);

  assert_eq!(restored.check(), diagnostics);
  let restored_entry = restored.file_id(&key(FileId(0))).expect("restored entry");
  assert_eq!(
    restored.file_text(restored_entry).as_deref(),
    Some(entry_source)
  );
  assert_eq!(
    restored.type_at(restored_entry, call_offset),
    Some(type_at_call),
    "snapshot restoration should load host text for missing sources"
  );
}

#[test]
fn snapshot_restoration_reachable_files_does_not_reparse() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let snapshot = program.snapshot();
  reset_parse_call_count();
  let restored = Program::from_snapshot(host, snapshot);

  let parses_before = parse_call_count();
  let reachable = restored.reachable_files();
  let parses_after = parse_call_count();

  let math_id = restored.file_id(&key(FileId(1))).expect("math id");
  assert!(
    reachable.contains(&math_id),
    "restored reachable files should include dependencies: {reachable:?}"
  );
  assert_eq!(
    parses_after.saturating_sub(parses_before),
    0,
    "reachable_files should not trigger salsa parsing when restored from snapshot"
  );
}

#[test]
fn snapshot_restoration_supports_symbol_queries_without_source_text() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );
  let entry_id = program.file_id(&key(FileId(0))).expect("entry id");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let symbol = program
    .symbol_at(entry_id, call_offset)
    .expect("symbol at call");
  let info = program.symbol_info(symbol).expect("symbol info");

  let mut snapshot = program.snapshot();
  for file in snapshot.files.iter_mut() {
    if !file.is_lib {
      file.text = None;
    }
  }

  let mut missing_text_host = host.clone();
  missing_text_host.files.clear();

  reset_parse_call_count();
  let restored = Program::from_snapshot(missing_text_host, snapshot);

  let restored_entry = restored
    .file_id(&key(FileId(0)))
    .expect("restored entry id");
  let restored_symbol = restored.symbol_at(restored_entry, call_offset);
  assert_eq!(restored_symbol, Some(symbol));
  assert_eq!(restored.symbol_info(symbol), Some(info));

  let parses_before = parse_call_count();
  let reachable = restored.reachable_files();
  let parses_after = parse_call_count();
  let math_id = restored.file_id(&key(FileId(1))).expect("math id");
  assert!(
    reachable.contains(&math_id),
    "restored reachable files should include dependencies: {reachable:?}"
  );
  assert_eq!(
    parses_after.saturating_sub(parses_before),
    0,
    "reachable_files should not trigger salsa parsing when source text is missing"
  );
}

#[test]
fn snapshot_restoration_span_queries_do_not_reparse() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&key(FileId(0))).expect("entry id");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let (body, expr) = program
    .expr_at(entry_id, call_offset)
    .expect("expr at call");
  let total_def = program
    .exports_of(entry_id)
    .get("total")
    .and_then(|entry| entry.def)
    .expect("total def");

  let snapshot = program.snapshot();
  reset_parse_call_count();
  let restored = Program::from_snapshot(host, snapshot);

  let restored_entry = restored
    .file_id(&key(FileId(0)))
    .expect("restored entry id");
  let (restored_body, restored_expr) = restored
    .expr_at(restored_entry, call_offset)
    .expect("restored expr at call");
  assert_eq!(restored_body, body);
  assert_eq!(restored_expr, expr);

  let parses_before = parse_call_count();
  assert!(restored.span_of_def(total_def).is_some());
  assert!(restored
    .span_of_expr(restored_body, restored_expr)
    .is_some());
  let parses_after = parse_call_count();
  assert_eq!(
    parses_after.saturating_sub(parses_before),
    0,
    "span queries should not trigger salsa parsing when restored from snapshot"
  );
}

#[test]
fn snapshot_restoration_preserves_pat_span_queries() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let entry_id = program.file_id(&key(FileId(0))).expect("entry id");
  let top_body = program.file_body(entry_id).expect("top-level body");
  let result = program.check_body(top_body);
  let total_start = entry_source.find("total").expect("total offset") as u32;
  let total_end = total_start + "total".len() as u32;
  let expected = typecheck_ts::TextRange::new(total_start, total_end);
  let pat_index = result
    .pat_spans()
    .iter()
    .position(|span| *span == expected)
    .expect("pat span for total");
  let pat_id = typecheck_ts::PatId(pat_index as u32);

  let span = program.pat_span(top_body, pat_id).expect("pat span");
  assert_eq!(span.file, entry_id);
  assert_eq!(span.range, expected);

  let snapshot = program.snapshot();
  let restored = Program::from_snapshot(host, snapshot);

  let restored_entry = restored.file_id(&key(FileId(0))).expect("restored entry");
  let restored_body = restored
    .file_body(restored_entry)
    .expect("restored top body");
  assert_eq!(restored_body, top_body);
  let restored_span = restored
    .pat_span(restored_body, pat_id)
    .expect("restored pat span");
  assert_eq!(restored_span.file, restored_entry);
  assert_eq!(restored_span.range, expected);
}

#[test]
fn snapshot_serialization_is_deterministic() {
  let mut host = MemoryHost::default();
  let key = key(FileId(10));
  host.insert(FileId(10), "export const value = 1 + 2;");

  let program = Program::new(host, vec![key.clone()]);
  program.check();

  let snap_a = program.snapshot();
  let snap_b = program.snapshot();

  let json_a = serde_json::to_string_pretty(&snap_a).expect("serialize snapshot");
  let json_b = serde_json::to_string_pretty(&snap_b).expect("serialize snapshot");

  assert_eq!(json_a, json_b, "snapshots must be byte-stable");
}

#[test]
fn snapshot_restoration_reuses_cached_body_for_type_at() {
  let mut host = MemoryHost::default();
  let entry_source = "import { add } from \"./math\";\nexport const total = add(1, 2);";
  let math_source = "export function add(a: number, b: number) { return a + b; }";
  host.insert(FileId(0), entry_source);
  host.insert(FileId(1), math_source);
  host.link(FileId(0), "./math", FileId(1));

  let program = Program::new(host.clone(), vec![key(FileId(0))]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "unexpected diagnostics: {diagnostics:?}"
  );

  let file_entry = program.file_id(&key(FileId(0))).expect("entry id");
  let call_offset = entry_source.find("add(1, 2)").unwrap() as u32;
  let original_type = program
    .type_at(file_entry, call_offset)
    .expect("type at call");

  let snapshot = program.snapshot();
  reset_parse_call_count();
  let restored = Program::from_snapshot(host, snapshot);

  let restored_entry = restored.file_id(&key(FileId(0))).expect("restored entry");
  let stats_before = restored.query_stats();
  let parses_before = parse_call_count();
  let restored_type = restored
    .type_at(restored_entry, call_offset)
    .expect("restored type");
  let stats_after = restored.query_stats();
  let parses_after = parse_call_count();

  let before = stats_before
    .queries
    .get(&QueryKind::CheckBody)
    .cloned()
    .unwrap_or_default();
  let after = stats_after
    .queries
    .get(&QueryKind::CheckBody)
    .cloned()
    .unwrap_or_default();

  assert_eq!(restored_type, original_type);
  assert_eq!(
    after.total.saturating_sub(before.total),
    1,
    "type_at should reuse the cached body result instead of re-checking"
  );
  assert_eq!(
    after.cache_misses.saturating_sub(before.cache_misses),
    0,
    "cached body should not register misses when restored from snapshot"
  );
  assert_eq!(
    after.cache_hits.saturating_sub(before.cache_hits),
    1,
    "restored body should register a cache hit when queried"
  );
  assert_eq!(
    parses_after.saturating_sub(parses_before),
    0,
    "restored snapshot should not trigger re-parsing"
  );
}
