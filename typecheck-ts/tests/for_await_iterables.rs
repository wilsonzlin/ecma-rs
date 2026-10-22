//! `for await…of` iterates the async protocol (`[Symbol.asyncIterator]`) when
//! present, else the sync protocol, and *awaits* the element
//! (`types.forAwait.es2018.1.ts`): `AsyncIterable<number>` and
//! `Iterable<Promise<number>>` both iterate as `number`.

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut options = CompilerOptions::default();
  options.target = ScriptTarget::EsNext;
  let mut host = MemoryHost::with_options(options);
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
fn for_await_over_async_iterable() {
  let src = "declare const asyncIterable: AsyncIterable<number>;\nasync function f() {\n    let y: number;\n    for await (const x of asyncIterable) {\n    }\n    for await (y of asyncIterable) {\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn for_await_awaits_promise_elements() {
  let src = "declare const iterableOfPromise: Iterable<Promise<number>>;\nasync function f() {\n    let y: number;\n    for await (const x of iterableOfPromise) {\n    }\n    for await (y of iterableOfPromise) {\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn for_await_hand_written_async_iterator() {
  let src = "class AIter {\n    next() { return { value: 1, done: false }; }\n    [Symbol.asyncIterator]() { return this; }\n}\nasync function f() {\n    let y: number;\n    for await (y of new AIter) {\n    }\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn for_await_wrong_element_still_errors() {
  let src = "declare const asyncIterable: AsyncIterable<string>;\nasync function f() {\n    let y: number;\n    for await (y of asyncIterable) {\n    }\n}\n";
  assert_eq!(codes(src), ["TS2322"]);
}
