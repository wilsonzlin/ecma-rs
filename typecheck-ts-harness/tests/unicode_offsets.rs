#![cfg(feature = "with-node")]

use serde_json::Map;
use std::collections::HashMap;
use std::path::PathBuf;
use typecheck_ts_harness::tsc::{node_available, typescript_available, TscRequest, TscRunner, TypeQuery};

fn runner_or_skip() -> Option<TscRunner> {
  let node_path = PathBuf::from("node");

  if !node_available(&node_path) {
    eprintln!("skipping tsc unicode offset tests: node not available");
    return None;
  }

  if !typescript_available(&node_path) {
    eprintln!("skipping tsc unicode offset tests: typescript not available (run `cd typecheck-ts-harness && npm ci`)");
    return None;
  }

  match TscRunner::new(node_path) {
    Ok(runner) => Some(runner),
    Err(err) => {
      eprintln!("skipping tsc unicode offset tests: {err}");
      None
    }
  }
}

#[test]
fn diagnostics_report_utf8_byte_offsets() {
  let mut runner = match runner_or_skip() {
    Some(runner) => runner,
    None => return,
  };

  let source = "const s = \"💩\";\nnotDefined;\n".to_string();
  let expected_start = source
    .find("notDefined")
    .expect("expected marker to exist") as u32;
  let expected_end = expected_start + "notDefined".len() as u32;

  let mut files = HashMap::new();
  files.insert("main.ts".to_string(), source);

  let request = TscRequest {
    root_names: vec!["main.ts".to_string()],
    files,
    options: Map::new(),
    type_queries: Vec::new(),
  };

  let output = runner.check(request).expect("tsc output");
  let diag = output
    .diagnostics
    .iter()
    .find(|diag| diag.code == 2304)
    .expect("expected TS2304 diagnostic for unknown identifier");
  assert_eq!(diag.file.as_deref(), Some("main.ts"));
  assert_eq!((diag.start, diag.end), (expected_start, expected_end));
}

#[test]
fn auto_scanned_type_queries_use_utf8_byte_offsets() {
  let mut runner = match runner_or_skip() {
    Some(runner) => runner,
    None => return,
  };

  let source = "let s = \"💩\";\nconst t = s;\n//        ^?\n".to_string();
  let expected_offset =
    source.find("const t = ").expect("expected const usage") + "const t = ".len();

  let mut files = HashMap::new();
  files.insert("main.ts".to_string(), source);

  let request = TscRequest {
    root_names: vec!["main.ts".to_string()],
    files,
    options: Map::new(),
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
  let mut runner = match runner_or_skip() {
    Some(runner) => runner,
    None => return,
  };

  let emojis = "💩".repeat(20);
  let source = format!("let s = \"{emojis}\";\nlet a = 1;\nconst b = s;\n");
  let expected_offset = source.find("let a").expect("expected let a") + "let ".len();

  let mut files = HashMap::new();
  files.insert("main.ts".to_string(), source);

  let request = TscRequest {
    root_names: vec!["main.ts".to_string()],
    files,
    options: Map::new(),
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

