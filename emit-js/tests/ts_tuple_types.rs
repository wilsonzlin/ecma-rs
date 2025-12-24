use emit_js::emit_type_expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::ParseCtx;
use parse_js::parse::Parser;
use parse_js::token::TT;

fn parse_type_expr(src: &str) -> Node<TypeExpr> {
  let mut parser = Parser::new(Lexer::new(src));
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: true,
      yield_allowed: true,
    },
  };
  let expr = parser.type_expr(ctx).expect("parse type expression");
  parser.require(TT::EOF).expect("exhaust input");
  expr
}

fn emit_type_expr_to_string(expr: &Node<TypeExpr>) -> String {
  let mut out = String::new();
  emit_type_expr(&mut out, expr).expect("emit type expression");
  out
}

fn assert_roundtrip(input: &str, expected: &str) {
  let parsed = parse_type_expr(input);
  let emitted = emit_type_expr_to_string(&parsed);
  assert_eq!(emitted, expected, "emitted output should be canonical");

  let reparsed = parse_type_expr(&emitted);
  let reemitted = emit_type_expr_to_string(&reparsed);
  assert_eq!(reemitted, emitted, "emission should be stable on re-parse");
}

#[test]
fn emits_tuple_and_array_types() {
  let cases = [
    ("[string,number]", "[string, number]"),
    ("readonly [T, U]", "readonly [T, U]"),
    ("T[]", "T[]"),
    ("readonly T[]", "readonly T[]"),
    ("(A|B)[]", "(A | B)[]"),
    ("readonly (A | B)[]", "readonly (A | B)[]"),
    ("[x:number,y?:string]", "[x: number, y?: string]"),
    ("[string,...number[]]", "[string, ...number[]]"),
    ("[string,number?]", "[string, number?]"),
  ];

  for (input, expected) in cases {
    assert_roundtrip(input, expected);
  }
}

