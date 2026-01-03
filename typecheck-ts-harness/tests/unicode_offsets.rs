#![cfg(feature = "with-node")]

mod common;

use serde_json::Map;
use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts_harness::tsc::{TscRequest, TypeQuery};

#[test]
fn diagnostics_report_utf8_byte_offsets() {
  let mut runner = match common::runner_or_skip("tsc unicode offset tests") {
    Some(runner) => runner,
    None => return,
  };

  let source = "const s = \"💩\";\nnotDefined;\n".to_string();
  let expected_start = source.find("notDefined").expect("expected marker to exist") as u32;
  let expected_end = expected_start + "notDefined".len() as u32;

  let name: Arc<str> = Arc::from("main.ts");
  let mut files = HashMap::new();
  files.insert(Arc::clone(&name), Arc::from(source));

  let request = TscRequest {
    root_names: vec![name],
    files,
    options: Map::new(),
    diagnostics_only: true,
    type_queries: Vec::new(),
  };

  let output = runner.check(request).expect("tsc output");
  let diag = output
    .diagnostics
    .iter()
    .find(|diag| matches!(diag.code, 2304 | 2552))
    .expect("expected TS2304/TS2552 diagnostic for unknown identifier");
  assert_eq!(diag.file.as_deref(), Some("main.ts"));
  assert_eq!((diag.start, diag.end), (expected_start, expected_end));
}

#[test]
fn auto_scanned_type_queries_use_utf8_byte_offsets() {
  let mut runner = match common::runner_or_skip("tsc unicode offset tests") {
    Some(runner) => runner,
    None => return,
  };

  let source = "let s = \"💩\";\nconst t = s;\n//        ^?\n".to_string();
  let expected_offset =
    source.find("const t = ").expect("expected const usage") + "const t = ".len();

  let name: Arc<str> = Arc::from("main.ts");
  let mut files = HashMap::new();
  files.insert(Arc::clone(&name), Arc::from(source));

  let request = TscRequest {
    root_names: vec![name],
    files,
    options: Map::new(),
    diagnostics_only: false,
    type_queries: Vec::new(),
  };

  let output = runner.check(request).expect("tsc output");
  let facts = output.type_facts.expect("expected type facts");
  assert_eq!(facts.markers.len(), 1);
  let marker = &facts.markers[0];
  assert_eq!(marker.file, "main.ts");
  assert_eq!(marker.offset, expected_offset as u32);
  assert_eq!(marker.type_str, "string");
}

#[test]
fn provided_type_queries_convert_utf8_offsets_for_typescript() {
  let mut runner = match common::runner_or_skip("tsc unicode offset tests") {
    Some(runner) => runner,
    None => return,
  };

  let emojis = "💩".repeat(20);
  let source = format!("let s = \"{emojis}\";\nlet a = 1;\nconst b = s;\n");
  let expected_offset = source.find("let a").expect("expected let a") + "let ".len();

  let name: Arc<str> = Arc::from("main.ts");
  let mut files = HashMap::new();
  files.insert(Arc::clone(&name), Arc::from(source));

  let request = TscRequest {
    root_names: vec![name],
    files,
    options: Map::new(),
    diagnostics_only: false,
    type_queries: vec![TypeQuery {
      file: "main.ts".to_string(),
      offset: expected_offset as u32,
      line: None,
      column: None,
    }],
  };

  let output = runner.check(request).expect("tsc output");
  let facts = output.type_facts.expect("expected type facts");
  assert_eq!(facts.markers.len(), 1);
  let marker = &facts.markers[0];
  assert_eq!(marker.file, "main.ts");
  assert_eq!(marker.offset, expected_offset as u32);
  assert_eq!(marker.type_str, "number");
}
