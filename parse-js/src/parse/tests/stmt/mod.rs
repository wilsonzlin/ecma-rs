#![cfg(feature = "serde")]

use crate::lex::Lexer;
use crate::parse::expr::pat::ParsePatternRules;
use crate::parse::Parser;
use crate::parse::{AsiContext, ParseCtx};
use crate::util::test::evaluate_test_input_files;
use crate::Dialect;
use crate::ParseOptions;
use crate::SourceType;
use serde_json::Value;

fn parse_stmt_and_serialize(input: String) -> Value {
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Module,
  };
  let mut parser = Parser::new(Lexer::new(&input), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: true,
      yield_allowed: true,
    },
    top_level: true,
    in_namespace: false,
    asi: AsiContext::Statements,
  };
  let node = parser.stmt(ctx).unwrap();
  serde_json::to_value(&node).unwrap()
}

#[test]
fn test_parse_expression() {
  evaluate_test_input_files("parse/tests/stmt", parse_stmt_and_serialize);
}
