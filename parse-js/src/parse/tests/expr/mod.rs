use crate::ast::expr::Expr;
use crate::ast::node::Node;
use crate::ast::type_expr::TypeEntityName;
use crate::ast::type_expr::TypeExpr;
use crate::lex::Lexer;
use crate::parse::expr::pat::ParsePatternRules;
use crate::parse::ParseCtx;
use crate::parse::Parser;
use crate::token::TT;
use crate::util::test::evaluate_test_input_files;
use crate::Dialect;
use crate::ParseOptions;
use crate::SourceType;
use serde_json::Value;

fn parse_expr_with_options(input: &str, opts: ParseOptions) -> Node<Expr> {
  let mut parser = Parser::new(Lexer::new(input), opts);
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: !matches!(opts.source_type, SourceType::Module),
      yield_allowed: true,
    },
    top_level: true,
  };
  parser.expr(ctx, [TT::Semicolon]).unwrap()
}

fn parse_expr(input: &str) -> Node<Expr> {
  parse_expr_with_options(
    input,
    ParseOptions {
      dialect: Dialect::Tsx,
      source_type: SourceType::Script,
    },
  )
}

fn parse_expr_and_serialize(input: String) -> Value {
  let node = parse_expr(&input);
  serde_json::to_value(&node).unwrap()
}

#[test]
fn test_parse_expression() {
  evaluate_test_input_files("parse/tests/expr", parse_expr_and_serialize);
}

#[test]
fn parses_angle_bracket_type_assertion_expression() {
  let expr = parse_expr_with_options(
    "<Foo>bar;",
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  );

  match *expr.stx {
    Expr::TypeAssertion(ref assertion) => {
      assert!(!assertion.stx.const_assertion);

      let type_annotation = assertion
        .stx
        .type_annotation
        .as_ref()
        .expect("expected type annotation for assertion");
      match *type_annotation.stx {
        TypeExpr::TypeReference(ref type_ref) => match &type_ref.stx.name {
          TypeEntityName::Identifier(name) => assert_eq!(name, "Foo"),
          other => panic!("expected identifier type name, got {:?}", other),
        },
        ref other => panic!("expected type reference, got {:?}", other),
      }

      match *assertion.stx.expression.as_ref().stx {
        Expr::Id(ref id) => assert_eq!(id.stx.name, "bar"),
        ref other => panic!("expected identifier expression, got {:?}", other),
      }
    }
    ref other => panic!("expected type assertion expression, got {:?}", other),
  }
}

#[test]
fn parses_jsx_element_instead_of_type_assertion() {
  let expr = parse_expr_with_options(
    "<foo>bar</foo>;",
    ParseOptions {
      dialect: Dialect::Tsx,
      source_type: SourceType::Module,
    },
  );

  match *expr.stx {
    Expr::JsxElem(_) => {}
    ref other => panic!("expected JSX element, got {:?}", other),
  }
}
