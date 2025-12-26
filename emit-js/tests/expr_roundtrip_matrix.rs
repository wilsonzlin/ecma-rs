use emit_js::{emit_expr, emit_type_expr};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::{ParseCtx, Parser};
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
      await_allowed: true,
      yield_allowed: true,
    },
    top_level: true,
    in_namespace: false,
  };
  let expr = parser.expr(ctx, [TT::EOF]).expect("parse expression");
  parser.require(TT::EOF).expect("exhaust input");
  expr
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

#[test]
fn parenthesizes_new_over_optional_chaining_member() {
  assert_roundtrip("new a?.b", Some("new (a?.b)"));
}

#[test]
fn parenthesizes_new_over_optional_chaining_call() {
  assert_roundtrip("new a?.()", Some("new (a?.())"));
}

#[test]
fn parenthesizes_new_over_optional_chaining_computed_member() {
  assert_roundtrip("new a?.[b]", Some("new (a?.[b])"));
}
