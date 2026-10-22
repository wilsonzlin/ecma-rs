//! Undeclared `this.#x` is TS2339 (conformance `privateNameImplicitDeclaration`).

use typecheck_ts::lib_support::CompilerOptions;
use typecheck_ts::{FileKey, MemoryHost, Program};

#[test]
fn undeclared_private_field_on_this_is_ts2339() {
  // Mirrors conformance `privateNameImplicitDeclaration` (JSDoc `@type` is
  // irrelevant; the private name is simply not declared on the class).
  let src = r#"
class C {
  constructor() {
    /** @type {string} */
    this.#x;
  }
}
"#;
  let mut opts = CompilerOptions::default();
  opts.strict_null_checks = true;
  opts.no_implicit_any = false;
  let mut host = MemoryHost::with_options(opts);
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  let d: Vec<_> = program
    .check()
    .into_iter()
    .map(|diag| {
      (
        diag.code.as_str().to_string(),
        diag.primary.range.start,
        diag.primary.range.end,
      )
    })
    .collect();
  let hits: Vec<_> = d.iter().filter(|(c, _, _)| c == "TS2339").collect();
  assert_eq!(hits.len(), 1, "expected one TS2339: {d:?}");
  assert_eq!(&src[hits[0].1 as usize..hits[0].2 as usize], "#x");
}
