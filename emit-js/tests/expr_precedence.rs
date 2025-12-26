use emit_js::{emit_expr, emit_type_expr};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::{ParseCtx, Parser};
use parse_js::token::TT;
use parse_js::{Dialect, ParseOptions, SourceType};
use serde_json::Value;

fn parse_expr(source: &str) -> Node<Expr> {
  let opts = ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(source), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: true,
      yield_allowed: true,
    },
    top_level: true,
    in_namespace: false,
  };
  let expr = parser
    .expr(ctx, [TT::EOF])
    .unwrap_or_else(|err| panic!("failed to parse {source:?}: {err:?}"));
  parser
    .require(TT::EOF)
    .unwrap_or_else(|err| panic!("failed to exhaust input {source:?}: {err:?}"));
  expr
}

fn emit_expr_to_string(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  emit_expr(&mut out, expr, |out, ty| emit_type_expr(out, ty))
    .unwrap_or_else(|err| panic!("failed to emit expression {:?}: {:?}", expr.stx, err));
  out
}

fn assert_roundtrip(source: &str, expected_emitted: Option<&str>) {
  let original = parse_expr(source);
  let emitted = emit_expr_to_string(&original);
  if let Some(expected) = expected_emitted {
    assert_eq!(emitted, expected);
  }
  let reparsed = parse_expr(&emitted);
  let orig_json: Value = serde_json::to_value(&original).unwrap();
  let reparsed_json: Value = serde_json::to_value(&reparsed).unwrap();
  assert_eq!(
    orig_json, reparsed_json,
    "roundtrip AST mismatch for source {source:?} emitted {emitted:?}"
  );
}

#[test]
fn exponentiation_left_associative_operand_parenthesised() {
  assert_roundtrip("(a ** b) ** c", Some("(a ** b) ** c"));
}

#[test]
fn exponentiation_right_associative_operand_no_extra_parens() {
  assert_roundtrip("a ** (b ** c)", Some("a ** b ** c"));
}

#[test]
fn exponentiation_unary_left_operand_requires_parens() {
  assert_roundtrip("(-a) ** b", Some("(-a) ** b"));
  assert_roundtrip("-a ** b", Some("(-a) ** b"));
  assert_roundtrip("-(a ** b)", Some("-(a ** b)"));
}

#[test]
fn nullish_coalescing_mixed_with_logical_ops_requires_parens() {
  assert_roundtrip("a ?? (b || c)", Some("a ?? (b || c)"));
  assert_roundtrip("a ?? (b && c)", Some("a ?? (b && c)"));
  assert_roundtrip("(a || b) ?? c", Some("(a || b) ?? c"));
  assert_roundtrip("(a && b) ?? c", Some("(a && b) ?? c"));
  assert_roundtrip("a || (b ?? c)", Some("a || (b ?? c)"));
  assert_roundtrip("a && (b ?? c)", Some("a && (b ?? c)"));
}

#[test]
fn assignment_and_conditional_associativity_is_preserved() {
  assert_roundtrip("a = b = c", Some("a = b = c"));
  assert_roundtrip("a ? b : c ? d : e", Some("a ? b : c ? d : e"));
  assert_roundtrip("(a ? b : c) ? d : e", Some("(a ? b : c) ? d : e"));
}
