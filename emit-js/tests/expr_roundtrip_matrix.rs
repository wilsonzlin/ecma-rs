use emit_js::{emit_expr, emit_type_expr};
use parse_js::ast::expr::{CallExpr, ComputedMemberExpr, Expr, IdExpr, MemberExpr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::error::SyntaxErrorType;
use parse_js::lex::Lexer;
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::{AsiContext, ParseCtx, Parser};
use parse_js::token::TT;
use parse_js::{Dialect, ParseOptions, SourceType};

fn parse_expr(src: &str) -> Node<Expr> {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(src), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: false,
      yield_allowed: false,
      await_expr_allowed: true,
      yield_expr_allowed: false,
    },
    top_level: true,
    in_namespace: false,
    asi: AsiContext::Statements,
  };
  let expr = parser.expr(ctx, [TT::EOF]).expect("parse expression");
  parser.require(TT::EOF).expect("exhaust input");
  expr
}

fn try_parse_expr(src: &str) -> Result<Node<Expr>, parse_js::error::SyntaxError> {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(src), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: false,
      yield_allowed: false,
      await_expr_allowed: true,
      yield_expr_allowed: false,
    },
    top_level: true,
    in_namespace: false,
    asi: AsiContext::Statements,
  };
  let expr = parser.expr(ctx, [TT::EOF])?;
  parser.require(TT::EOF)?;
  Ok(expr)
}

fn emit_expr_to_string(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |out: &mut String, ty: &Node<TypeExpr>| emit_type_expr(out, ty);
  emit_expr(&mut out, expr, &mut emit_type).expect("emit expression");
  out
}

fn assert_roundtrip(src: &str, expected: Option<&str>) {
  let original = parse_expr(src);
  let emitted = emit_expr_to_string(&original);

  if let Some(expected) = expected {
    assert_eq!(
      emitted, expected,
      "emitted form should be canonical for `{}`",
      src
    );
  }

  let reparsed = parse_expr(&emitted);
  let left = serde_json::to_value(&original).expect("serialize original AST");
  let right = serde_json::to_value(&reparsed).expect("serialize reparsed AST");
  assert_eq!(
    left, right,
    "roundtrip mismatch for `{}` => `{}`",
    src, emitted
  );
}

fn node<T: derive_visitor::Drive + derive_visitor::DriveMut>(stx: T) -> Node<T> {
  Node::new(Loc(0, 0), stx)
}

fn id_expr(name: &str) -> Node<Expr> {
  node(Expr::Id(node(IdExpr {
    name: name.to_string(),
  })))
}

fn member_expr(left: Node<Expr>, right: &str, optional: bool) -> Node<Expr> {
  node(Expr::Member(node(MemberExpr {
    optional_chaining: optional,
    left,
    right: right.to_string(),
  })))
}

fn computed_member_expr(object: Node<Expr>, member: Node<Expr>, optional: bool) -> Node<Expr> {
  node(Expr::ComputedMember(node(ComputedMemberExpr {
    optional_chaining: optional,
    object,
    member,
  })))
}

fn call_expr(callee: Node<Expr>, optional: bool) -> Node<Expr> {
  node(Expr::Call(node(CallExpr {
    optional_chaining: optional,
    callee,
    arguments: vec![],
  })))
}

fn new_expr(argument: Node<Expr>) -> Node<Expr> {
  node(Expr::Unary(node(UnaryExpr {
    operator: OperatorName::New,
    argument,
  })))
}

/// Emit a synthetic AST that is illegal as source (parse-js rejects it) but that
/// transformers may still construct; assert the defensive parenthesized form.
fn assert_emit_constructed(expr: Node<Expr>, expected: &str) {
  let emitted = emit_expr_to_string(&expr);
  assert_eq!(emitted, expected, "constructed AST emit mismatch");
  // Emitted form must be legal and round-trip to the same shape.
  let reparsed = parse_expr(&emitted);
  let left = serde_json::to_value(&expr).expect("serialize constructed AST");
  let right = serde_json::to_value(&reparsed).expect("serialize reparsed AST");
  assert_eq!(
    left, right,
    "constructed AST roundtrip mismatch: `{}` => `{}`",
    expected, emitted
  );
}

fn assert_parse_rejects_optional_chain_from_new(src: &str) {
  let err = try_parse_expr(src).expect_err(&format!("expected parse reject for {src:?}"));
  assert_eq!(
    err.typ,
    SyntaxErrorType::InvalidOptionalChainFromNew,
    "expected PS0017 for {src:?}, got {:?}",
    err.typ
  );
}

#[test]
fn right_associativity_is_preserved() {
  assert_roundtrip("a=b=c", Some("a = b = c"));
  assert_roundtrip("(a=b)=c", Some("(a = b) = c"));
  assert_roundtrip("a**b**c", Some("a ** b ** c"));
  assert_roundtrip("(a**b)**c", Some("(a ** b) ** c"));
}

#[test]
fn exponentiation_and_unary_operands() {
  assert_roundtrip("(-a)**b", Some("(-a) ** b"));
  assert_roundtrip("(-a)**(b**c)", Some("(-a) ** b ** c"));
}

#[test]
fn parenthesizes_exponentiation_operand_in_unary() {
  assert_roundtrip("-(a**b)", Some("-(a ** b)"));
}

#[test]
fn conditional_nesting_roundtrips() {
  assert_roundtrip("a?b:c?d:e", Some("a ? b : c ? d : e"));
  assert_roundtrip("(a?b:c)?d:e", Some("(a ? b : c) ? d : e"));
}

#[test]
fn nullish_mixing_requires_parentheses() {
  assert_roundtrip("(a??b)||c", Some("(a ?? b) || c"));
  assert_roundtrip("a??(b||c)", Some("a ?? (b || c)"));
  assert_roundtrip("(a??b)&&c", Some("(a ?? b) && c"));
  assert_roundtrip("a??(b&&c)", Some("a ?? (b && c)"));
}

#[test]
fn ts_operator_grouping_is_respected() {
  assert_roundtrip("(a+b) as T + c", Some("(a + b) as T + c"));
  assert_roundtrip("(a+b)!", Some("(a + b)!"));
  assert_roundtrip("a satisfies T", Some("a satisfies T"));
}

// ECMA-262: `new`'s callee is a MemberExpression (or NewExpression without
// Arguments). An OptionalExpression is not a MemberExpression, so
// `new a?.b` / `new a?.()` / `new a?.[b]` are SyntaxErrors (parse-js PS0017)
// unless the optional chain is parenthesized: `new (a?.b)`, `new (a?.())`,
// `new (a?.[b])`.
//
// Separately, OptionalChain may not follow a bare NewExpression:
// `new a?.()` is a SyntaxError; the legal form is `(new a)?.()`. Synthetic
// ASTs that still encode the illegal shapes (from transforms) must emit the
// parenthesized canonical form — covered via constructed-AST asserts below.

#[test]
fn parenthesizes_new_over_optional_chaining_member() {
  // Illegal as source; keep emitter coverage via synthetic AST.
  assert_parse_rejects_optional_chain_from_new("new a?.b");
  assert_emit_constructed(new_expr(member_expr(id_expr("a"), "b", true)), "new (a?.b)");
  assert_roundtrip("new (a?.b)", Some("new (a?.b)"));
}

#[test]
fn parenthesizes_new_over_optional_chaining_call() {
  // Illegal as source (`new a?.()`); synthetic AST is optional-call on `new a`.
  assert_parse_rejects_optional_chain_from_new("new a?.()");
  assert_emit_constructed(call_expr(new_expr(id_expr("a")), true), "(new a)?.()");
  assert_roundtrip("(new a)?.()", Some("(new a)?.()"));
  // True `new` of an optional call requires parens in source already:
  assert_roundtrip("new (a?.())", Some("new (a?.())"));
}

#[test]
fn parenthesizes_new_over_optional_chaining_computed_member() {
  assert_parse_rejects_optional_chain_from_new("new a?.[b]");
  assert_emit_constructed(
    new_expr(computed_member_expr(id_expr("a"), id_expr("b"), true)),
    "new (a?.[b])",
  );
  assert_roundtrip("new (a?.[b])", Some("new (a?.[b])"));
}

#[test]
fn parenthesizes_new_callee_optional_chain_family() {
  // Illegal sources → constructed ASTs for emitter defensive parens.
  assert_parse_rejects_optional_chain_from_new("new a?.b()");
  assert_emit_constructed(
    new_expr(call_expr(member_expr(id_expr("a"), "b", true), false)),
    "new (a?.b)()",
  );
  assert_roundtrip("new (a?.b)()", Some("new (a?.b)()"));

  assert_parse_rejects_optional_chain_from_new("new a?.b.c()");
  assert_emit_constructed(
    new_expr(call_expr(
      member_expr(member_expr(id_expr("a"), "b", true), "c", false),
      false,
    )),
    "new (a?.b.c)()",
  );

  assert_parse_rejects_optional_chain_from_new("new a.b?.c()");
  assert_emit_constructed(
    new_expr(call_expr(
      member_expr(member_expr(id_expr("a"), "b", false), "c", true),
      false,
    )),
    "new (a.b?.c)()",
  );

  // Optional call as callee of `new` (with outer construct args) — legal source.
  assert_roundtrip("new (a?.())()", Some("new (a?.())()"));

  assert_parse_rejects_optional_chain_from_new("new a.b?.()");
  assert_emit_constructed(
    call_expr(new_expr(member_expr(id_expr("a"), "b", false)), true),
    "(new a.b)?.()",
  );
  assert_roundtrip("(new a.b)?.()", Some("(new a.b)?.()"));
  assert_roundtrip("new (a.b?.())", Some("new (a.b?.())"));
}

#[test]
fn parenthesizes_new_callee_call_expression() {
  // CallExpression is not MemberExpression: `new f()()` is `(new f())()`, so
  // `new (f())()` must keep the inner call parenthesized.
  assert_roundtrip("new (f())()", Some("new (f())()"));
}

#[test]
fn parenthesizes_nested_new_with_optional_chain() {
  // Nested construct of an optional-call callee.
  assert_roundtrip("new (new (a?.()))()", Some("new (new (a?.()))()"));
  // Bare `new new a?.()()` is invalid JS; synthetic AST is optional-call on
  // `new (new a)`, then a further call — emitter parenthesizes both `new`s.
  assert_parse_rejects_optional_chain_from_new("new new a?.()()");
  assert_emit_constructed(
    call_expr(call_expr(new_expr(new_expr(id_expr("a"))), true), false),
    "(new (new a))?.()()",
  );
  assert_roundtrip("(new (new a))?.()()", Some("(new (new a))?.()()"));
}

#[test]
fn parenthesizes_new_before_optional_chain_member() {
  // Bare `new` cannot take `?.` without parens; `new F()?.x` (with Arguments)
  // is a MemberExpression and we still parenthesize for AST/HIR parity.
  assert_roundtrip("(new a)?.b", Some("(new a)?.b"));
  assert_roundtrip("new a()?.b", Some("(new a())?.b"));
  assert_roundtrip("(new a())?.b", Some("(new a())?.b"));
}
