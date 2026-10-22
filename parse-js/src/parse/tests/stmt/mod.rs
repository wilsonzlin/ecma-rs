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

// Fixtures named `*.script.js` parse as sloppy scripts (contextual keywords like
// `await`/`let`/`yield` are identifiers); everything else parses as a TS module
// (where those are reserved and `await`-expressions are legal, e.g. for-await).
// One ParseCtx cannot serve both: a spec-correct parser treats `await` as an
// operator in module code and as an identifier in sloppy scripts. Mirrors the
// test262 runner's filename-based mode inference.
fn parse_stmt_and_serialize(name: &str, input: String) -> Value {
  let is_script = name.contains(".script.");
  let opts = ParseOptions {
    dialect: Dialect::Ts,
    source_type: if is_script {
      SourceType::Script
    } else {
      SourceType::Module
    },
  };
  let mut parser = Parser::new(Lexer::new(&input), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: is_script,
      yield_allowed: is_script,
      await_expr_allowed: !is_script,
      yield_expr_allowed: false,
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
