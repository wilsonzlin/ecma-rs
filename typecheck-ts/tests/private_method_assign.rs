//! TS2803 — cannot assign to private methods.

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(opts: CompilerOptions, src: &str) -> Vec<(String, u32, u32)> {
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let mut out: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| {
      (
        d.code.as_str().to_string(),
        d.primary.range.start,
        d.primary.range.end,
      )
    })
    .collect();
  out.sort();
  out
}

fn codes(opts: CompilerOptions, src: &str) -> Vec<String> {
  diags(opts, src).into_iter().map(|(c, _, _)| c).collect()
}

fn strict() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn private_method_assignment_is_ts2803() {
  // Mirrors conformance `privateNameMethodAssignment.ts`.
  let src = r#"
class A3 {
  #method() { }
  constructor(a: A3, b: any) {
    this.#method = () => {}
    a.#method = () => {}
    b.#method = () => {} // next line may ASI-call the arrow
    ({ x: this.#method } = { x: () => {} })
    let x = this.#method
    b.#method++
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2803").count(),
    5,
    "five writes to #method: {c:?}"
  );
  assert!(
    !c.iter().any(|x| x == "TC2000"),
    "excess-arg ASI call must not be TC2000: {c:?}"
  );
}

#[test]
fn private_static_method_assignment_is_ts2803() {
  // Mirrors conformance `privateNameStaticMethodAssignment.ts`.
  let src = r#"
class A3 {
  static #method() { }
  constructor(a: typeof A3, b: any) {
    A3.#method = () => {}
    a.#method = () => {}
    b.#method = () => {} // next line may ASI-call the arrow
    ({ x: A3.#method } = { x: () => {} })
    let x = A3.#method
    b.#method++
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2803").count(),
    5,
    "five writes to static #method: {c:?}"
  );
}

#[test]
fn private_method_mistyped_rhs_is_ts2803_and_ts2322() {
  // Mirrors conformance `privateNameReadonly.ts` (both codes).
  let src = r#"
const C = class {
  #bar() {}
  foo() {
    this.#bar = 123
  }
}
"#;
  let c = codes(strict(), src);
  assert!(c.iter().any(|x| x == "TS2803"), "expected TS2803: {c:?}");
  assert!(
    c.iter().any(|x| x == "TS2322"),
    "expected TS2322 alongside TS2803: {c:?}"
  );
}

#[test]
fn private_field_assignment_is_not_ts2803() {
  let src = r#"
class C {
  #f = 1
  m() {
    this.#f = 2
  }
}
"#;
  let c = codes(strict(), src);
  assert!(
    !c.iter().any(|x| x == "TS2803"),
    "private fields are writable: {c:?}"
  );
}

#[test]
fn ts2803_spans_private_identifier() {
  let src = r#"
class C {
  #m() {}
  foo() {
    this.#m = () => {}
  }
}
"#;
  let d = diags(strict(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2803").collect();
  assert_eq!(hits.len(), 1, "{d:?}");
  let (_, start, end) = hits[0];
  let slice = &src[*start as usize..*end as usize];
  assert_eq!(
    slice, "#m",
    "span should be the private name, got {slice:?}"
  );
}

#[test]
fn excess_args_ok() {
  let mut opts = CompilerOptions::default();
  opts.no_implicit_any = false;
  let c = codes(opts, "(() => {})(1); const f = () => {}; f(1, 2);");
  assert!(
    !c.iter().any(|x| *x == "TC2000" || *x == "TS2554"),
    "tsc allows excess args: {c:?}"
  );
}
