//! TS18046 / TS2339 — private-identifier access on `any` / `unknown` / `never`.
//! Mirrors conformance `privateNameAndAny.ts`.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(src: &str) -> Vec<(String, String)> {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| (d.code.as_str().to_string(), d.message.clone()))
    .collect();
  out.sort();
  out
}

#[test]
fn private_on_any_allows_declared_undeclared_is_ts2339() {
  let src = r#"
class A {
  #foo = true;
  static #baz = 10;
  static #m() {}
  method(thing: any) {
    thing.#foo;
    thing.#m();
    thing.#baz;
    thing.#bar;
    thing.#foo();
  }
}
"#;
  let d = diags(src);
  let codes: Vec<_> = d.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(
    codes.iter().filter(|c| **c == "TS2339").count(),
    1,
    "only undeclared #bar on any: {d:?}"
  );
  assert!(
    !codes.iter().any(|c| *c == "TS18046"),
    "any receiver must not emit TS18046: {d:?}"
  );
}

#[test]
fn private_on_unknown_is_ts18046_plus_undeclared_ts2339() {
  let src = r#"
class A {
  #foo = true;
  static #baz = 10;
  static #m() {}
  methodU(thing: unknown) {
    thing.#foo;
    thing.#m();
    thing.#baz;
    thing.#bar;
    thing.#foo();
  }
}
"#;
  let d = diags(src);
  let codes: Vec<_> = d.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(
    codes.iter().filter(|c| **c == "TS18046").count(),
    5,
    "each unknown private access: {d:?}"
  );
  assert_eq!(
    codes.iter().filter(|c| **c == "TS2339").count(),
    1,
    "undeclared #bar still TS2339: {d:?}"
  );
  assert!(
    d.iter()
      .any(|(c, m)| c == "TS18046" && m.contains("'thing'")),
    "TS18046 names the receiver: {d:?}"
  );
}

#[test]
fn private_on_never_is_ts2339_for_all_accesses() {
  let src = r#"
class A {
  #foo = true;
  static #baz = 10;
  static #m() {}
  methodN(thing: never) {
    thing.#foo;
    thing.#m();
    thing.#baz;
    thing.#bar;
    thing.#foo();
  }
}
"#;
  let d = diags(src);
  let codes: Vec<_> = d.iter().map(|(c, _)| c.as_str()).collect();
  assert_eq!(
    codes.iter().filter(|c| **c == "TS2339").count(),
    5,
    "never: all private accesses TS2339: {d:?}"
  );
  assert!(
    !codes.iter().any(|c| *c == "TS18046"),
    "never must not emit TS18046: {d:?}"
  );
}
