#![cfg(feature = "with-node")]

use serde_json::Map;
use std::collections::HashMap;
use std::path::PathBuf;
use typecheck_ts_harness::tsc::TscRequest;
use typecheck_ts_harness::tsc::TscRunner;
use typecheck_ts_harness::tsc::{node_available, typescript_available};

fn runner_or_skip() -> Option<TscRunner> {
  let node_path = PathBuf::from("node");

  if !node_available(&node_path) {
    eprintln!("skipping tsc runner tests: node not available");
    return None;
  }

  if !typescript_available(&node_path) {
    eprintln!("skipping tsc runner tests: typescript not available (run `cd typecheck-ts-harness && npm ci`)");
    return None;
  }

  match TscRunner::new(node_path) {
    Ok(runner) => Some(runner),
    Err(err) => {
      eprintln!("skipping tsc runner tests: {err}");
      None
    }
  }
}

#[test]
fn reports_single_file_error() {
  let mut runner = match runner_or_skip() {
    Some(runner) => runner,
    None => return,
  };

  let mut files = HashMap::new();
  files.insert(
    "main.ts".to_string(),
    "const value: string = 1;".to_string(),
  );

  let request = TscRequest {
    root_names: vec!["main.ts".to_string()],
    files,
    options: Map::new(),
    diagnostics_only: true,
    type_queries: Vec::new(),
  };

  let output = runner.check(request).expect("tsc output");
  assert_eq!(output.diagnostics.len(), 1);
  let diag = &output.diagnostics[0];
  assert_eq!(diag.code, 2322);
  assert_eq!(diag.file.as_deref(), Some("main.ts"));
  assert_eq!((diag.start, diag.end), (6, 11));
}

#[test]
fn resolves_relative_imports_across_files() {
  let mut runner = match runner_or_skip() {
    Some(runner) => runner,
    None => return,
  };

  let mut files = HashMap::new();
  files.insert(
    "a.ts".to_string(),
    "export const value: number = 1;".to_string(),
  );
  files.insert(
    "b.ts".to_string(),
    "import { value } from './a';\nconst str: string = value;\n".to_string(),
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
  let diag = &output.diagnostics[0];
  assert_eq!(diag.code, 2322);
  assert_eq!(diag.file.as_deref(), Some("b.ts"));
  assert_eq!((diag.start, diag.end), (35, 38));
}
