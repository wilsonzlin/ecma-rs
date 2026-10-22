//! Cover grammar / assignment-target gaps fixed 2026-07-23 from test262 triage.
//!
//! Spec cites:
//! - CoverInitializedName (ECMA-262 ObjectLiteral cover / ObjectAssignmentPattern)
//! - IsValidSimpleAssignmentTarget of ParenthesizedExpression
//! - AssignmentRestElement : `...` DestructuringAssignmentTarget (nested patterns)
//! - `let` as IdentifierReference in for-in (sloppy)
//! - Directive Prologue Use Strict Directive (unescaped `"use strict"` / `'use strict'` only)
//!
//! Representative test262 IDs (see `test262/manifest.toml` triage entries):
//! - CoverInitializedName: `799fad61dcd88f30`, `0d9f26fe4d91ad07`, `3c895971bd50ea01`
//! - Parenthesized targets: `4789c3375f112cd4`, `e71c1d5f0b6b833c`, `0b4d61559ccce0f9`
//! - Nested rest: `e1820bdb79ebe44b`, `a2781f8227f7f1e6`, `c98889d7d94a0a63`
//! - `for (let in …)`: `9aa93e1e417ce8e3`, `9fe1d41db318afba`
//! - Escaped directive: `06f0deb843fbf358`, `855b8dea36c841ed`

use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

fn ecma_module() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Module,
  }
}

fn accept(src: &str) {
  parse_with_options(src, ecma_script()).unwrap_or_else(|err| {
    panic!("expected accept {src:?}, got {err:?}");
  });
}

fn reject(src: &str) {
  assert!(
    parse_with_options(src, ecma_script()).is_err(),
    "expected reject: {src:?}"
  );
}

fn reject_module(src: &str) {
  assert!(
    parse_with_options(src, ecma_module()).is_err(),
    "expected module reject: {src:?}"
  );
}

#[test]
fn cover_initialized_name_accepted_in_assignment_pattern() {
  // ObjectLiteral cover → ObjectAssignmentPattern
  accept("({a = 1} = obj);");
  accept("({a = 1,} = 2);");
  accept("[{a=1},{a=2}] = 3;");
  accept("[a, {b: {c = 1}}] = d;");
  accept("for ({a = 1} in b);");
  accept("for({a=1} of b);");
  accept("function f({a = 1}) {}");
  accept("({a = 1}) => {};");
  // Assignment LHS inside array literal element list
  accept("[{a=b}=1];");
}

#[test]
fn cover_initialized_name_rejected_as_plain_object_literal() {
  // Early error: CoverInitializedName remaining as ObjectLiteral
  reject("({a = 1});");
  reject("({a = 1,});");
  reject("f({a = 1});");
  reject("x = {a = 1};");
  reject("[{a = 1}];");
}

#[test]
fn parenthesized_simple_assignment_targets_accepted() {
  // IsValidSimpleAssignmentTarget looks through ParenthesizedExpression
  accept("(a) = 1;");
  accept("((b)) = 2;");
  accept("[(a)] = 1;");
  accept("[(a) = 1] = 2;");
  accept("({a:(b)} = 1);");
  accept("({a:(b.c)} = 1);");
  accept("({a:(b) = 1} = 2);");
  accept("() => (a) = 1;");
  accept("([1].a) = 2;");
  accept("for ((a) in []);");
  accept("for ((a) of []);");
  accept("for ((a.b) in []);");
}

#[test]
fn parenthesized_invalid_assignment_targets_rejected() {
  reject("(a + b) = 1;");
  reject("(this) = 1;");
  reject("((a,b)) = 1;");
  reject("([a]) = 1;");
  reject("(({a}) = 1);");
  reject("for (([a]) in []);");
  reject("for (({a}) of []);");
}

#[test]
fn nested_rest_destructuring_accepted() {
  // AssignmentRestElement → DestructuringAssignmentTarget (pattern)
  accept("[...[a]] = 1;");
  accept("[...{a}] = b;");
  accept("[a, ...[b, c]] = d;");
  accept("[a, ...{0: b}] = 1;");
  accept("[...[...a[b]]] = c;");
  accept("let [...[a]] = x;");
  accept("let [...{a}] = x;");
}

#[test]
fn nested_rest_invalid_forms_rejected() {
  reject("[...a = 1] = x;");
  reject("[...[a],] = x;");
  reject("[...a,] = x;");
  // Object rest may not be a nested pattern in assignment
  reject("({...[a]} = x);");
  reject("({...{a}} = x);");
  reject("({...a,} = x);");
}

#[test]
fn let_as_identifier_in_for_in_sloppy_script() {
  // for (let in …): `let` is IdentifierReference, not LexicalDeclaration
  accept("for (let in a) {}");
  accept("for(let in 1);");
  // Still a declaration when followed by a binding name / pattern
  accept("for (let x in a) {}");
  accept("for (let of of a) {}");
}

#[test]
fn let_as_identifier_rejected_in_strict_and_for_of() {
  reject("'use strict'; for (let in a) {}");
  reject_module("for (let in a) {}");
  // for-of may not use IdentifierReference `let`
  reject("for (let of a) {}");
}

#[test]
fn escaped_use_strict_is_not_a_directive() {
  // Escapes mean the prologue entry is not a Use Strict Directive, so `with` is legal.
  accept("'use\\x20strict'; with (a) b = c;");
  accept("\"use\\x20strict\"; with (a) b = c;");
  accept("(function () { 'use\\x20strict'; with (a); }())");
  accept("(function () { 'use\\x20strict'; with (a); })");
  // True directive still enables strict mode
  reject("'use strict'; with (a) {}");
  reject("\"use strict\"; with (a) {}");
}

#[test]
fn string_literal_contains_escapes_marker() {
  use parse_js::ast::expr::Expr;
  use parse_js::ast::node::StringLiteralContainsEscapes;
  use parse_js::ast::stmt::Stmt;

  let escaped = parse_with_options("'use\\x20strict';", ecma_script()).unwrap();
  let Stmt::Expr(stmt) = escaped.stx.body[0].stx.as_ref() else {
    panic!("expected expr stmt");
  };
  let Expr::LitStr(lit) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected string literal");
  };
  assert!(
    lit.assoc.get::<StringLiteralContainsEscapes>().is_some(),
    "escaped literal must carry StringLiteralContainsEscapes"
  );

  let plain = parse_with_options("'use strict';", ecma_script()).unwrap();
  let Stmt::Expr(stmt) = plain.stx.body[0].stx.as_ref() else {
    panic!("expected expr stmt");
  };
  let Expr::LitStr(lit) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected string literal");
  };
  assert!(
    lit.assoc.get::<StringLiteralContainsEscapes>().is_none(),
    "plain directive literal must not carry StringLiteralContainsEscapes"
  );
}
