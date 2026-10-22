//! TS2806 — read of setter-only private accessors.

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

fn es2015() -> CompilerOptions {
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  opts
}

#[test]
fn private_setter_no_getter_compound_is_ts2806() {
  // Mirrors conformance `privateNameSetterNoGetter.ts`.
  let src = r#"
const C = class {
  set #x(x) {}
  m() {
    this.#x += 2;
  }
}
"#;
  let c = codes(es2015(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2806").count(),
    1,
    "compound read of setter-only #x: {c:?}"
  );
}

#[test]
fn private_write_only_accessor_reads_are_ts2806() {
  // Mirrors conformance `privateWriteOnlyAccessorRead.ts` (subset of sites).
  let src = r#"
class Test {
  set #value(v: { foo: { bar: number } }) {}
  set #valueRest(v: number[]) {}
  set #valueOne(v: number) {}
  set #valueCompound(v: number) {}

  m() {
    const foo = { bar: 1 };
    console.log(this.#value); // error
    this.#value = { foo }; // ok
    this.#value = { foo }; // ok
    this.#value.foo = foo; // error

    ({ o: this.#value } = { o: { foo } }); // ok
    ({ ...this.#value } = { foo }); // ok

    ({ foo: this.#value.foo } = { foo }); // error
    ({
      foo: { ...this.#value.foo },
    } = { foo }); // error

    let r = { o: this.#value }; // error

    [this.#valueOne, ...this.#valueRest] = [1, 2, 3]; // ok
    let arr = [
        this.#valueOne,
        ...this.#valueRest
    ];

    this.#valueCompound += 3; // error
  }
}
"#;
  let c = codes(es2015(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS2806").count(),
    8,
    "expected 8 TS2806 reads; got {c:?}"
  );
}

#[test]
fn private_setter_definite_write_is_ok() {
  let src = r#"
class C {
  set #x(v: number) {}
  m() {
    this.#x = 1;
    ({ o: this.#x } = { o: 2 });
    [this.#x] = [3];
  }
}
"#;
  let c = codes(es2015(), src);
  assert!(
    !c.iter().any(|x| x == "TS2806"),
    "definite writes must not be TS2806: {c:?}"
  );
}

#[test]
fn private_getter_setter_pair_read_ok() {
  let src = r#"
class C {
  get #x() { return 1; }
  set #x(v: number) {}
  m() {
    return this.#x + 1;
  }
}
"#;
  let c = codes(es2015(), src);
  assert!(
    !c.iter().any(|x| x == "TS2806"),
    "getter+setter must be readable: {c:?}"
  );
}

#[test]
fn ts2806_spans_full_member_access() {
  let src = r#"
class C {
  set #x(v: number) {}
  m() {
    return this.#x;
  }
}
"#;
  let d = diags(es2015(), src);
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2806").collect();
  assert_eq!(hits.len(), 1, "{d:?}");
  // `this.#x` — not just `#x`
  let (_, start, end) = hits[0];
  assert!(
    end - start > 2,
    "span should cover full access, got {start}-{end}"
  );
}
