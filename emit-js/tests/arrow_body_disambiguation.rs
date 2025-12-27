use emit_js::emit_expr;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::{AsiContext, ParseCtx, Parser};
use parse_js::token::TT;
use parse_js::{Dialect, ParseOptions, SourceType};

fn parse_expression(input: &str) -> Node<Expr> {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(input), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: true,
      yield_allowed: true,
    },
    top_level: true,
    in_namespace: false,
    asi: AsiContext::Statements,
  };
  let expr = parser.expr(ctx, [TT::EOF]).expect("parse expression");
  parser.require(TT::EOF).expect("exhaust input");
  expr
}

fn emit_expression(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr(&mut out, expr, &mut emit_type).expect("emit expression");
  out
}

fn assert_roundtrip(input: &str, expected: &str) {
  let parsed = parse_expression(input);
  let emitted = emit_expression(&parsed);
  assert_eq!(emitted, expected);

  let reparsed = parse_expression(&emitted);
  let reemitted = emit_expression(&reparsed);
  assert_eq!(reemitted, expected);
}

#[test]
fn parenthesizes_object_literal_bodies() {
  assert_roundtrip("x=>({a:1})", "(x) => ({a: 1})");
}

#[test]
fn parenthesizes_comma_bodies() {
  assert_roundtrip("x=>(a,b)", "(x) => (a, b)");
}

#[test]
fn parenthesizes_arrow_in_member_chain() {
  assert_roundtrip("(x=>({a:1})).prop", "((x) => ({a: 1})).prop");
}

#[test]
fn emits_typed_arrow_parameters() {
  assert_roundtrip("(x:Foo)=>x", "(x: Foo) => x");
}
