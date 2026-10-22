//! Generator return-type inference aggregates the body's yield union and
//! checks it against the contextual return type (tsc
//! `getReturnTypeOfSignature` for generators): mismatched yields must surface
//! TS2322 at the function instead of silently adopting the contextual
//! `Iterable<Foo>` (`generatorTypeCheck25.ts`). Compatible yields and the
//! `generatorTypeCheck45.ts` generic-inference path keep working.

use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(src: &str) -> Vec<String> {
  let mut host = MemoryHost::default();
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
fn mismatched_yields_fail_contextual_generator_assignment() {
  let src = r#"class Foo { x: number }
class Bar extends Foo { y: string }
class Baz { z: number }
var g3: () => Iterable<Foo> = function* () {
    yield;
    yield new Bar;
    yield new Baz;
    yield *[new Bar];
    yield *[new Baz];
}"#;
  assert_eq!(codes(src), ["TS2322"]);
}

#[test]
fn compatible_yields_check_cleanly() {
  let src = r#"class Foo { x: number }
class Bar extends Foo { y: string }
var g: () => Iterable<Foo> = function* () {
    yield new Bar;
    yield *[new Bar];
}"#;
  assert!(codes(src).is_empty());
}

#[test]
fn generator_inference_through_generic_call_still_works() {
  // `generatorTypeCheck45.ts`: T=string is fixed by the first argument, so the
  // generator yields `(x: string) => number` and only the final argument
  // mismatches (undefined is not string).
  let src = "declare function foo<T, U>(x: T, fun: () => Iterator<(x: T) => U>, fun2: (y: U) => T): T;\nfoo(\"\", function* () { yield x => x.length }, p => undefined);";
  assert_eq!(codes(src), ["TS2322"]);
}
