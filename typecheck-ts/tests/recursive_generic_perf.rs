//! Regression coverage for the `forStatementsMultipleInvalidDecl` saga:
//!
//! - **Recursive-generic expansion** — `new D<string>()` on
//!   `class D<T> { wrapped: D<D<T>> }` must not explode evaluation (was
//!   ~56s; the relate of the instantiated vs generic ctor signature
//!   descended the nested instantiation chain with quadratic eager arg
//!   evaluation). The thread-local def-level deferral in
//!   `TypeEvaluator::evaluate_ref` keeps nested same-def expansions as
//!   substituted references (tsc's laziness) — expansion completes in
//!   normal time and `var a: D<string> = new D<string>()` still relates.
//! - **TS2403 in `for` chains** — every subsequent `var` in a sequence of
//!   `for( var x = …;;){}` statements is checked (tsc keeps the FIRST
//!   declaration's type for the merged binding; seeded file bindings must
//!   not clobber it with the LAST declaration's).
//! - **Explicit type args** — non-generic overloads are silently excluded
//!   when explicit type args are provided (`new Array<number>()` skips
//!   lib `ArrayConstructor`'s `new (arrayLength?): any[]`); when every
//!   signature is non-generic, TS2558 fires once and checking continues.

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

const RECURSIVE_D: &str = "class D<T> { source: T; wrapped: D<D<T>> }\n";

#[test]
fn recursive_generic_constructs_and_relates() {
  let src = format!(
    "{RECURSIVE_D}var a = new D<string>();\nvar b: D<string> = new D<string>();\nlet s: string = b.source;\n"
  );
  assert_eq!(codes(&src), Vec::<String>::new());
}

#[test]
fn recursive_generic_mismatch_still_errors() {
  let src = format!("{RECURSIVE_D}var a: D<number> = new D<string>();\n");
  let c = codes(&src);
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "D<number> vs D<string> must error: {c:?}"
  );
}

#[test]
fn recursive_generic_member_chain_resolves() {
  let src = format!("{RECURSIVE_D}declare const a: D<string>;\nlet d: D<D<string>> = a.wrapped;\n");
  assert_eq!(codes(&src), Vec::<String>::new());
}

#[test]
fn for_chain_checks_every_subsequent_var() {
  let src = "for( var a: any;;){}\nfor( var a = 1;;){}\nfor( var a = 's';;){}\n";
  let c = codes(src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2403").count(),
    2,
    "both subsequent declarations must be TS2403 (tsc): {c:?}"
  );
}

#[test]
fn for_chain_of_four_checks_three() {
  let src =
    "for( var a: any;;){}\nfor( var a = 1;;){}\nfor( var a = 's';;){}\nfor( var a = true;;){}\n";
  let c = codes(src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2403").count(),
    3,
    "all three subsequent declarations must be TS2403 (tsc): {c:?}"
  );
}

#[test]
fn derived_class_in_for_chain_is_ts2403() {
  let src = "class C { id: number; valid: boolean }\nclass C2 extends C { name: string }\nfor( var b = new C();;){}\nfor( var b = new C2();;){}\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2403"),
    "C2 vs C must be TS2403 (tsc): {c:?}"
  );
}

#[test]
fn new_array_with_explicit_type_arg() {
  let src =
    "var x = new Array<number>();\nlet z: number[] = x;\nvar y = new Array<number>(1, 2);\n";
  assert_eq!(codes(src), Vec::<String>::new());
}

#[test]
fn new_array_with_wrong_arg_count_is_ts2558() {
  let src = "var x = new Array<number, string>();\n";
  let c = codes(src);
  assert!(
    c.iter().any(|x| x == "TS2558"),
    "wrong type-arg count must be TS2558: {c:?}"
  );
}

#[test]
fn explicit_type_args_on_non_generic_is_ts2558_once() {
  let src = "declare function f(x: number): number;\nvar y = f<number>(1);\n";
  let c = codes(src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2558").count(),
    1,
    "tsc reports TS2558 once and continues: {c:?}"
  );
}
