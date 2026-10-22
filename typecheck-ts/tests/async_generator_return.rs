//! Generator/async-generator `return` statements check against the generator
//! type's `TReturn` argument — not the generator object itself:
//! `async function* f(): AsyncGenerator<T, T, T> { return a }` checks `a`
//! against `Awaited<T>` (`asyncGeneratorGenericNonWrappedReturn.ts`).

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
fn async_generator_generic_return_allowed() {
  let src = "export async function* test<T>(a: T): AsyncGenerator<T, T, T> {\n  return a\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn async_generator_concrete_return_allowed() {
  let src = "export async function* test(a: number): AsyncGenerator<number, number, number> {\n  return a\n}\n";
  assert!(codes(src).is_empty());
}

#[test]
fn async_generator_wrong_return_still_errors() {
  let src = "export async function* test(a: string): AsyncGenerator<number, number, number> {\n  return a\n}\n";
  assert_eq!(codes(src), ["TS2322"]);
}

#[test]
fn sync_generator_return_uses_treturn() {
  let src = "export function* test(a: string): Generator<number, number, number> {\n  yield 1;\n  return a;\n}\n";
  assert_eq!(codes(src), ["TS2322"]);
}
