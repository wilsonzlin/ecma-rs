//! Contextual return-type adoption for function expressions: when the body's
//! inferred return is not assignable to the contextual return, the checker
//! normally adopts the contextual type so literal unions like `() => 3 | 4`
//! survive inference widening. But an empty (or `return;`-only) body infers
//! `void`, and adopting a non-void contextual return would silently accept
//! `() => {}` where tsc reports TS2322
//! (`staticMemberAssignsToConstructorFunctionMembers.ts`).

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
fn empty_body_into_nonvoid_return_errors() {
  assert_eq!(codes("const i: () => number = () => { };"), ["TS2322"]);
  assert_eq!(
    codes("const f: () => string = function () { };"),
    ["TS2322"]
  );
}

#[test]
fn empty_body_into_void_or_top_return_ok() {
  assert!(codes("const h: () => void = () => { };").is_empty());
  assert!(codes("const u: () => unknown = () => { };").is_empty());
  assert!(codes("const a: () => any = () => { };").is_empty());
}

#[test]
fn literal_contextual_return_still_adopted() {
  assert!(codes("const f: () => 3 | 4 = () => 3;").is_empty());
  assert!(codes("const k: () => 3 | 4 = () => { return 3; };").is_empty());
}

#[test]
fn static_member_empty_body_assignment_errors() {
  // tsc: only `C.bar = () => { }` errors (TS2322); the other two are fine.
  let src = r#"class C {
    static foo() {
        C.foo = () => { }
    }

    static bar(x: number): number {
        C.bar = () => { }
        C.bar = (x) => x;
        C.bar = (x: number) => 1;
        return 1;
    }
}
"#;
  assert_eq!(codes(src), ["TS2322"]);
}

#[test]
fn generator_empty_body_still_adopts_contextual_return() {
  // A generator with no `return` still produces an Iterator/Generator result,
  // never `void` — the empty-body gate must not fire
  // (`generatorTypeCheck45.ts`): tsc reports only TS2322 on the last argument
  // (`undefined` is not `string`), no TS2345 on the generator argument.
  let src = r#"declare function foo<T, U>(x: T, fun: () => Iterator<(x: T) => U>, fun2: (y: U) => T): T;

foo("", function* () { yield x => x.length }, p => undefined);
"#;
  assert_eq!(codes(src), ["TS2322"]);
}
