//! TS18011 / TS2790 — `delete` of a private identifier.

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
fn delete_private_field_is_ts18011_and_ts2790() {
  // Mirrors conformance `privateNamesNoDelete.ts`.
  let src = r#"
class A {
  #v = 1;
  constructor() {
    delete this.#v;
  }
}
"#;
  let d = diags(strict(), src);
  let c: Vec<_> = d.iter().map(|(c, _, _)| c.as_str()).collect();
  assert!(c.iter().any(|x| *x == "TS18011"), "expected TS18011: {c:?}");
  assert!(c.iter().any(|x| *x == "TS2790"), "expected TS2790: {c:?}");
  let hits: Vec<_> = d
    .iter()
    .filter(|(c, _, _)| c == "TS18011" || c == "TS2790")
    .collect();
  for (_, start, end) in &hits {
    let slice = &src[*start as usize..*end as usize];
    assert_eq!(
      slice, "this.#v",
      "span should be the full access, got {slice:?}"
    );
  }
}

#[test]
fn delete_optional_private_field_is_only_ts18011() {
  // Optional / `| undefined` private still cannot be deleted (TS18011), but
  // TS2790 stays quiet.
  let src = r#"
class A {
  #v: number | undefined = 1;
  constructor() {
    delete this.#v;
  }
}
"#;
  let c = codes(strict(), src);
  assert_eq!(
    c.iter().filter(|x| *x == "TS18011").count(),
    1,
    "still illegal to delete private: {c:?}"
  );
  assert!(
    !c.iter().any(|x| *x == "TS2790"),
    "optional private must not be TS2790: {c:?}"
  );
}

#[test]
fn delete_public_optional_prop_is_quiet() {
  let src = r#"
class A {
  v?: number = 1;
  constructor() {
    delete this.v;
  }
}
"#;
  let c = codes(strict(), src);
  assert!(
    !c.iter().any(|x| *x == "TS18011" || *x == "TS2790"),
    "optional public delete should be quiet: {c:?}"
  );
}
