//! TS2540 — assign to readonly fields / getter-only accessors.

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

fn strict() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn private_getter_only_accessor_assign_is_ts2540() {
  // Mirrors conformance `privateNameAccessors.ts`.
  let src = r#"
class A1 {
  get #prop() { return ""; }
  set #prop(param: string) { }
  get #roProp() { return ""; }
  constructor(name: string) {
    this.#prop = "";
    this.#roProp = "";
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2540").count(),
    1,
    "only #roProp is readonly: {c:?}"
  );
}

#[test]
fn private_static_getter_only_accessor_assign_is_ts2540() {
  // Mirrors conformance `privateNameStaticAccessors.ts`.
  let src = r#"
class A1 {
  static get #prop() { return ""; }
  static set #prop(param: string) { }
  static get #roProp() { return ""; }
  constructor(name: string) {
    A1.#prop = "";
    A1.#roProp = "";
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2540").count(),
    1,
    "only static #roProp is readonly: {c:?}"
  );
}

#[test]
fn readonly_field_ok_in_ctor_errors_in_method() {
  let src = r#"
class C {
  readonly x: number = 1;
  readonly #px: number = 1;
  constructor() {
    this.x = 2;
    this.#px = 2;
  }
  m() {
    this.x = 3;
    this.#px = 3;
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2540").count(),
    2,
    "readonly fields: ctor ok, method TS2540: {c:?}"
  );
}

#[test]
fn public_getter_only_always_ts2540() {
  let src = r#"
class C {
  get y() { return 1; }
  constructor() {
    this.y = 2;
  }
  m() {
    this.y = 3;
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2540").count(),
    2,
    "getter-only: ctor + method: {c:?}"
  );
}

#[test]
fn getter_setter_pair_is_writable() {
  let src = r#"
class C {
  get a() { return 1; }
  set a(v: number) {}
  get #b() { return 1; }
  set #b(v: number) {}
  m() {
    this.a = 2;
    this.#b = 2;
  }
}
"#;
  let c = codes(strict(), src);
  assert!(
    !c.iter().any(|x| x == "TS2540"),
    "getter+setter must be writable: {c:?}"
  );
}
