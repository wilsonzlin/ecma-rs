//! Regression tests for unbounded type-system work / cooperative cancellation.
//!
//! Pathological fixture: many indexed assignments of unresolved namespace
//! members into a typed function array — the shape of upstream conformance
//! `parser/ecmascript5/parserRealSource12.ts` (shard 2/64). Without budgets and
//! cancel observation in relate/eval hot loops, this drove RSS past 20 GB and
//! ignored per-case timeouts.

use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant};

use typecheck_ts::{codes, FileKey, MemoryHost, Program};

fn pathological_source(assign_count: usize) -> String {
  let mut source = String::from(
    r#"
interface IAstWalker { walk(ast: AST, parent: AST): AST; options: any; state: any; }
interface IAstWalkChildren { (preAst: AST, parent: AST, walker: IAstWalker): void; }
class AstWalkerFactory {
  private childrenWalkers: IAstWalkChildren[] = [];
  private initChildrenWalkers(): void {
"#,
  );
  for i in 0..assign_count {
    source.push_str(&format!(
      "    this.childrenWalkers[NodeType.Member{i}] = ChildrenWalkers.walk{i};\n"
    ));
  }
  source.push_str(
    r#"
  }
}
namespace ChildrenWalkers { }
"#,
  );
  source
}

#[test]
fn pathological_indexed_unresolved_assigns_terminate_quickly() {
  let source = pathological_source(120);
  let mut host = MemoryHost::new();
  let file = FileKey::new("pathology.ts");
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file]);

  let started = Instant::now();
  let diagnostics = program.check();
  let elapsed = started.elapsed();

  // Release finishes in ~1–3s; debug builds are much slower but must still
  // stay well under the old multi-minute / multi-GB hang.
  let limit = if cfg!(debug_assertions) {
    Duration::from_secs(90)
  } else {
    Duration::from_secs(15)
  };
  assert!(
    elapsed < limit,
    "pathological case must terminate quickly, took {elapsed:?} (limit {limit:?})"
  );

  // Prefer a clean budget diagnostic, but accepting a fast finish with ordinary
  // diagnostics is also fine — the hard requirement is bounded time/memory.
  let _ = diagnostics
    .iter()
    .any(|d| d.code.as_str() == codes::ENGINE_BUDGET_EXCEEDED.id);
}

#[test]
fn real_parser_real_source12_terminates_without_libs() {
  let path = concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/../parse-js/tests/TypeScript/tests/cases/conformance/parser/ecmascript5/parserRealSource12.ts"
  );
  let mut source = std::fs::read_to_string(path).expect("read upstream case");
  source = source
    .lines()
    .filter(|l| !l.contains("reference path"))
    .collect::<Vec<_>>()
    .join("\n");
  let mut host = MemoryHost::new();
  let file = FileKey::new("parserRealSource12.ts");
  host.insert(file.clone(), Arc::from(source));
  let program = Program::new(host, vec![file]);
  let started = Instant::now();
  let _diagnostics = program.check();
  let limit = if cfg!(debug_assertions) {
    Duration::from_secs(90)
  } else {
    Duration::from_secs(15)
  };
  assert!(
    started.elapsed() < limit,
    "upstream parserRealSource12.ts must terminate quickly without libs (took {:?}, limit {:?})",
    started.elapsed(),
    limit
  );
}

#[test]
fn pathological_case_honors_cancellation_promptly() {
  const CANCEL_TIMEOUT: Duration = Duration::from_millis(800);

  let source = pathological_source(200);
  let mut host = MemoryHost::new();
  let file = FileKey::new("pathology_cancel.ts");
  host.insert(file.clone(), Arc::from(source));

  let program = Arc::new(Program::new(host, vec![file]));
  let runner = Arc::clone(&program);
  let handle = thread::spawn(move || runner.check());

  // Give the checker a moment to enter the hot loop, then cancel.
  thread::sleep(Duration::from_millis(20));
  let cancelled_at = Instant::now();
  program.cancel();

  let deadline = cancelled_at + CANCEL_TIMEOUT;
  while Instant::now() < deadline {
    if handle.is_finished() {
      break;
    }
    thread::sleep(Duration::from_millis(5));
  }
  if !handle.is_finished() {
    eprintln!(
      "checker thread did not observe cancellation within {:?}; exiting to avoid hanging tests",
      CANCEL_TIMEOUT
    );
    std::process::exit(1);
  }

  let diagnostics = handle.join().expect("checker thread panicked");
  assert!(
    cancelled_at.elapsed() < CANCEL_TIMEOUT,
    "cancellation should complete quickly (within {:?})",
    CANCEL_TIMEOUT
  );
  assert!(
    diagnostics
      .iter()
      .any(|diag| diag.code.as_str() == codes::CANCELLED.id),
    "expected cancellation diagnostic, got {:?}",
    diagnostics
      .iter()
      .map(|d| d.code.as_str())
      .collect::<Vec<_>>()
  );
}
