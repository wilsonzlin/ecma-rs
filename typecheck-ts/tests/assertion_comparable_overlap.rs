//! Type-assertion overlap uses tsc's *comparable* relation, not assignability
//! (tsc `optionalProperties01.ts`): an optional source property may satisfy a
//! required target property when the target is compared against the source
//! for assertion validity.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  let mut host = MemoryHost::with_options(opts);
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
fn assertion_allows_optional_source_for_required_target() {
  let src = r#"
interface Foo {
  required1: string;
  required2: string;
  optional?: string;
}

const foo1 = { required1: "hello" } as Foo;
const foo2 = { required1: "hello", optional: "bar" } as Foo;
"#;
  assert_eq!(codes(CompilerOptions::default(), src), Vec::<String>::new());
}

#[test]
fn genuinely_non_overlapping_assertion_still_reports_ts2352() {
  let src = r#"
interface A { a: string }
interface B { b: number }
declare const a: A;
const b = a as B;
"#;
  assert_eq!(codes(CompilerOptions::default(), src), vec!["TS2352"]);
}
