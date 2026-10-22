//! Context-sensitive bodies against uninstantiated generic signatures (tsc):
//! when a lambda is checked against a call parameter whose signature mentions
//! unresolved type params, the body binds those params as `unknown` (tsc's
//! fallback for unresolved inference) — checks against them pass trivially,
//! and the post-resolution refine phase re-checks the body against the
//! instantiated signature (authoritative).
//!
//! `new Promise((resolve) => { resolve({}) })` against a free `T`
//! (`es6/modules/defaultExportInAwaitExpression01.ts`) must not error while
//! `T` is unresolved; `new Promise<number>((resolve) => { resolve("s") })`
//! must still error.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::new();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  out.sort();
  out
}

#[test]
fn unresolved_promise_executor_accepts_any_value() {
  let src = "const x = new Promise((resolve, reject) => { resolve({}); });\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn unresolved_promise_executor_accepts_primitives() {
  let src = "const x = new Promise((resolve, reject) => { resolve(1); });\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn explicit_type_arg_still_checks_executor() {
  // tsc: `new Promise<number>((resolve) => { resolve("s") })` errors TS2345.
  let src = "const x = new Promise<number>((resolve) => { resolve(\"s\"); });\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2345"),
    "explicit type arg must still check the executor body: {c:?}"
  );
}

#[test]
fn inferred_type_arg_checks_executor() {
  // tsc: T infers to `string` from "s"; calling `y(1)` inside the body is
  // TS2349 (uncallable), which our TC2000 family covers.
  let src = "declare function g<T>(x: T, cb: (y: T) => void): void;\ng(\"s\", (y) => { y(1); });\n";
  let c = codes(src);
  assert!(
    c.iter()
      .any(|x| x == "TC2000" || x == "TS2349" || x == "TS2345"),
    "inferred T must still check the body (tsc TS2349): {c:?}"
  );
}
