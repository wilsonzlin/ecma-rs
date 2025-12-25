use emit_js::{ts_type_to_string, EmitMode};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::lex::Lexer;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::ParseCtx;
use parse_js::parse::Parser;
use parse_js::token::TT;
use parse_js::Dialect;
use parse_js::ParseOptions;
use parse_js::SourceType;

fn parse_type_expr(src: &str) -> Node<TypeExpr> {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(src), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: !matches!(opts.source_type, SourceType::Module),
      yield_allowed: true,
    },
    top_level: true,
  };
  let expr = parser.type_expr(ctx).expect("parse type expression");
  parser.require(TT::EOF).expect("exhaust input");
  expr
}

fn emit_type_expr_to_string(expr: &Node<TypeExpr>) -> String {
  ts_type_to_string(expr, EmitMode::Canonical)
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
