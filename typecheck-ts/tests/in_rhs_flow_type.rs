//! tsc `checkInExpression` checks the *flow type* of a reference RHS: after
//! `x !== null` the RHS of `in` no longer includes `null`, so TS18047 must
//! not fire (`privateNameInInExpression.ts`). Bare-identifier RHS checks are
//! owned by the CFA pass; the AST pass still checks non-identifier RHS
//! (assertions like `(v as unknown)` keep TS2571). Unknown bare identifiers
//! are TS18046 ("'{x}' is of type 'unknown'"), not TS2571.

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
fn in_rhs_uses_flow_type_after_null_narrowing() {
  let src = r#"function g(x: object | null) {
  if (x !== null) {
    if ('a' in x) { }
  }
  if ('b' in x) { }
}
"#;
  // Only the post-if use errors (x: object | null there).
  assert_eq!(codes(src), ["TS18047"]);
}

#[test]
fn private_in_rhs_uses_flow_type_after_null_narrowing() {
  // Exact shape of the shard-27 conformance case: four uses after
  // `u !== null` must be clean; only the pre-narrowing use errors.
  let src = r#"class Foo {
  #field = 1;
  #method() {}
  static #staticField = 2;
  static #staticMethod() {}
  flow(u: unknown) {
    if (typeof u === 'object') {
      if (#field in u) { }
      if (u !== null) {
        if (#field in u) { }
        if (#method in u) { }
        if (#staticField in u) { }
        if (#staticMethod in u) { }
      }
    }
  }
}
"#;
  assert_eq!(codes(src), ["TS18047"]);
}

#[test]
fn unknown_bare_ident_in_rhs_is_ts18046() {
  assert_eq!(
    codes("function f(u: unknown) { if ('a' in u) { } }"),
    ["TS18046"]
  );
  assert_eq!(
    codes("class C { #f = 1; m(u: unknown) { if (#f in u) { } } }"),
    ["TS18046"]
  );
}

#[test]
fn non_ident_unknown_in_rhs_keeps_ts2571() {
  assert_eq!(
    codes("class C { #f = 1; m(v: any) { const a = #f in (v as unknown); } }"),
    ["TS2571"]
  );
}

#[test]
fn ambient_declare_const_in_rhs_keeps_declared_type() {
  // `controlFlowInOperator.ts` / `controlFlowWithTemplateLiterals.ts`:
  // module-level `declare const` is a *local* of the top-level body; the flow
  // pass must see the declared type (ambient declarators are erased, not
  // rebound to `unknown`).
  assert!(codes("declare const c: { a: number };\nif ('a' in c) { }").is_empty());
  assert!(codes("declare var c: { a: number } | { b: string };\nif ('a' in c) { }").is_empty());
  assert!(codes("declare const obj: { test: string } | {};\nif (`test` in obj) { }").is_empty());
  // Plain annotated no-init `var` keeps its annotation for the type of the
  // use, but tsc still reports TS2454 (not definitely assigned).
  assert_eq!(
    codes("var c: { a: number };\nif ('a' in c) { }"),
    ["TS2454"]
  );
}

#[test]
fn any_in_rhs_is_clean() {
  assert!(codes("function h(v: any) { if ('a' in v) { } }").is_empty());
}
