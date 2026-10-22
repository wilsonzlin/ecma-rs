//! ECMA-262: optional chains cannot participate in `new`'s MemberExpression, and
//! OptionalChain cannot follow a bare NewExpression (no Arguments).
//!
//! Illegal: `new a?.b`, `new a?.[b]`, `new a?.()`, `new a.b?.c()`.
//! Legal: `new (a?.b)`, `new (a?.())`, `(new a)?.()`, `new a()?.b`,
//! and `new (a?.b).c()` (chain inside PrimaryExpression; further MemberExpression
//! / Arguments attach outside the parentheses).
//!
//! Mirrors TypeScript TS1209 ("Invalid optional chain from new expression").

use parse_js::error::SyntaxErrorType;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn opts(dialect: Dialect) -> ParseOptions {
  ParseOptions {
    dialect,
    source_type: SourceType::Script,
  }
}

fn assert_reject_ps0017(src: &str, dialect: Dialect) {
  let err = parse_with_options(src, opts(dialect)).expect_err(&format!(
    "expected {dialect:?} parse of {src:?} to reject with PS0017"
  ));
  assert_eq!(
    err.typ,
    SyntaxErrorType::InvalidOptionalChainFromNew,
    "expected PS0017 (InvalidOptionalChainFromNew) for {src:?} in {dialect:?}, got {:?}",
    err.typ
  );
  assert_eq!(err.typ.code(), "PS0017");
}

fn assert_accept(src: &str, dialect: Dialect) {
  parse_with_options(src, opts(dialect))
    .unwrap_or_else(|err| panic!("expected {dialect:?} parse of {src:?} to succeed, got {err:?}"));
}

#[test]
fn rejects_optional_chain_in_new_callee_all_dialects() {
  for dialect in [
    Dialect::Ecma,
    Dialect::Js,
    Dialect::Jsx,
    Dialect::Ts,
    Dialect::Tsx,
  ] {
    // Member / computed / call forms feeding `new`.
    assert_reject_ps0017("new a?.b;", dialect);
    assert_reject_ps0017("new a?.[b];", dialect);
    assert_reject_ps0017("new a?.();", dialect);
    // Deeper nesting on the MemberExpression path.
    assert_reject_ps0017("new a.b?.c();", dialect);
    assert_reject_ps0017("new a?.b();", dialect);
    assert_reject_ps0017("new a.b?.();", dialect);
    // Nested bare `new` then optional call.
    assert_reject_ps0017("new new a?.();", dialect);
  }
}

#[test]
fn accepts_parenthesized_optional_chain_with_new() {
  for dialect in [Dialect::Ecma, Dialect::Js, Dialect::Ts] {
    // Chain inside PrimaryExpression — legal MemberExpression for `new`.
    assert_accept("new (a?.b);", dialect);
    assert_accept("new (a?.());", dialect);
    assert_accept("new (a?.[b]);", dialect);
    assert_accept("new (a?.b)();", dialect);
    assert_accept("new (a?.())();", dialect);

    // Optional call on a parenthesized NewExpression — legal OptionalExpression.
    assert_accept("(new a)?.();", dialect);
    assert_accept("(new a)?.b;", dialect);

    // `new MemberExpression Arguments` is a MemberExpression, so OptionalChain may follow.
    assert_accept("new a()?.b;", dialect);
    assert_accept("new a()?.();", dialect);

    // ECMA-262 MemberExpression: PrimaryExpression (`(a?.b)`) then `. IdentifierName`
    // then Arguments. The optional chain stays inside the parenthesized primary.
    assert_accept("new (a?.b).c();", dialect);
  }
}
