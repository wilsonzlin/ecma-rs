//! Generator function declarations type as `Generator<Y, R, N>` (async:
//! `AsyncGenerator`) built from the body's yield union — never `() => void`.
//! `function* gen() { yield 1; }` is `() => Generator<number, void, unknown>`,
//! so spreads and for-of get the precise element type without a contextual
//! type present (the shard-36 contextual path covers only annotated lambdas).

use typecheck_ts::lib_support::{CompilerOptions, ScriptTarget};
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes_with(target: ScriptTarget, src: &str) -> Vec<String> {
  let mut options = CompilerOptions::default();
  options.target = target;
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

fn codes(src: &str) -> Vec<String> {
  codes_with(ScriptTarget::Es2015, src)
}

#[test]
fn generator_spread_uses_yield_union() {
  assert_eq!(
    codes("function* gen() { yield 1; }\nvar good: number[] = [...gen()];\nvar bad: string[] = [...gen()];\n"),
    ["TS2322"]
  );
}

#[test]
fn generator_for_of_uses_yield_union() {
  assert_eq!(
    codes("function* gen() { yield 1; }\nfor (const s of gen()) { var q: string = s; }\n"),
    ["TS2322"]
  );
}

#[test]
fn generator_type_annotation_assignment() {
  assert!(
    codes("function* gen2() { yield 1; yield 'a'; return true; }\nvar g2: Generator<string | number, boolean, unknown> = gen2();\n")
      .is_empty()
  );
}

#[test]
fn async_generator_declaration_type() {
  assert!(codes_with(
    ScriptTarget::EsNext,
    "async function* gen() { yield 1; }\nvar g: AsyncGenerator<number, void, unknown> = gen();\n"
  )
  .is_empty());
}
