use crate::lex::Lexer;
use crate::parse::expr::pat::ParsePatternRules;
use crate::parse::ParseCtx;
use crate::parse::Parser;
use crate::token::TT;
use crate::util::test::evaluate_test_input_files;
use serde_json::Value;

fn parse_expr_and_serialize(input: Vec<u8>) -> Value {
  let mut parser = Parser::new(Lexer::new(&input));
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: true,
      yield_allowed: true,
    },
  };
  let node = parser.expr(ctx, [TT::Semicolon]).unwrap();
  serde_json::to_value(&node).unwrap()
}

#[test]
fn test_parse_expression() {
  evaluate_test_input_files("parse/tests/expr", parse_expr_and_serialize);
}
