#![cfg(feature = "with-node")]

mod common;

use serde_json::Map;
use std::collections::HashMap;
use std::sync::Arc;
use typecheck_ts_harness::tsc::TscRequest;

#[test]
fn reports_single_file_error() {
  let mut runner = match common::runner_or_skip("tsc runner tests") {
    Some(runner) => runner,
    None => return,
  };

  let mut files = HashMap::new();
  files.insert("main.ts".to_string(), Arc::from("const value: string = 1;"));

  let request = TscRequest {
    root_names: vec!["main.ts".to_string()],
    files,
    options: Map::new(),
    diagnostics_only: true,
    type_queries: Vec::new(),
  };

  let output = runner.check(request).expect("tsc output");
  assert_eq!(output.diagnostics.len(), 1);
  assert!(
    output.type_facts.is_none(),
    "expected no type facts when diagnostics_only is enabled"
  );
  let diag = &output.diagnostics[0];
  assert_eq!(diag.code, 2322);
  assert_eq!(diag.file.as_deref(), Some("main.ts"));
  assert_eq!((diag.start, diag.end), (6, 11));
}

#[test]
fn resolves_relative_imports_across_files() {
  let mut runner = match common::runner_or_skip("tsc runner tests") {
    Some(runner) => runner,
    None => return,
  };

  let mut files = HashMap::new();
  files.insert(
    "a.ts".to_string(),
    Arc::from("export const value: number = 1;"),
  );
  files.insert(
    "b.ts".to_string(),
    Arc::from("import { value } from './a';\nconst str: string = value;\n"),
  );

  let request = TscRequest {
    root_names: vec!["a.ts".to_string(), "b.ts".to_string()],
    files,
    options: Map::new(),
    diagnostics_only: true,
    type_queries: Vec::new(),
  };

  let output = runner.check(request).expect("tsc output");
  assert_eq!(output.diagnostics.len(), 1);
  assert!(
    output.type_facts.is_none(),
    "expected no type facts when diagnostics_only is enabled"
  );
  let diag = &output.diagnostics[0];
  assert_eq!(diag.code, 2322);
  assert_eq!(diag.file.as_deref(), Some("b.ts"));
  assert_eq!((diag.start, diag.end), (35, 38));
}
