use parse_js::ast::expr::Expr;
use parse_js::error::SyntaxResult;
use parse_js::lex::Lexer;
use parse_js::operator::OperatorName;
use parse_js::parse::expr::pat::ParsePatternRules;
use parse_js::parse::{ParseCtx, ParseDialect, ParseOptions, Parser};
use parse_js::token::TT;

fn parse_expr(
  source: &str,
  dialect: ParseDialect,
) -> SyntaxResult<parse_js::ast::node::Node<Expr>> {
  let mut parser = Parser::new_with_options(Lexer::new(source), ParseOptions { dialect });
  let ctx = ParseCtx {
    rules: ParsePatternRules {
      await_allowed: true,
      yield_allowed: true,
    },
  };
  let expr = parser.expr(ctx, [TT::EOF])?;
  parser.require(TT::EOF)?;
  Ok(expr)
}

#[test]
fn ts_allows_angle_bracket_assertion_tsx_does_not() {
  let expr = parse_expr("(<T>(x))", ParseDialect::TypeScript)
    .expect("ts should allow angle bracket assertion");
  assert!(matches!(*expr.stx, Expr::TypeAssertion(_)));

  assert!(
    parse_expr("(<T>(x))", ParseDialect::Tsx).is_err(),
    "tsx should not allow angle bracket assertions",
  );
}

#[test]
fn tsx_parses_jsx_element() {
  let expr = parse_expr("<div>{x}</div>", ParseDialect::Tsx).expect("tsx should parse JSX");
  assert!(matches!(*expr.stx, Expr::JsxElem(_)));
}

#[test]
fn comparisons_not_treated_as_type_arguments() {
  let expr = parse_expr("a < b, c > d", ParseDialect::TypeScript)
    .expect("should parse comparison expression");

  match expr.stx.as_ref() {
    Expr::Binary(root) => {
      assert_eq!(root.stx.operator, OperatorName::Comma);
      match root.stx.left.stx.as_ref() {
        Expr::Binary(left) => assert_eq!(left.stx.operator, OperatorName::LessThan),
        other => panic!("expected left comparison, got {:?}", other),
      }
      match root.stx.right.stx.as_ref() {
        Expr::Binary(right) => assert_eq!(right.stx.operator, OperatorName::GreaterThan),
        other => panic!("expected right comparison, got {:?}", other),
      }
    }
    other => panic!("expected comma expression, got {:?}", other),
  }
}

#[test]
fn nested_generic_calls_split_tokens() {
  let simple_call =
    parse_expr("foo<T>()", ParseDialect::TypeScript).expect("should parse generic call");
  assert!(matches!(*simple_call.stx, Expr::Call(_)));

  let call = parse_expr("Foo<Bar<Baz>>()", ParseDialect::TypeScript)
    .expect("should parse nested generic call");
  assert!(matches!(*call.stx, Expr::Call(_)));

  let new_expr = parse_expr("new Foo<Bar<Baz>>()", ParseDialect::TypeScript)
    .expect("should parse new with generic arguments");
  match new_expr.stx.as_ref() {
    Expr::Unary(unary) => assert_eq!(unary.stx.operator, OperatorName::New),
    other => panic!("expected unary new expression, got {:?}", other),
  }
}

#[test]
fn nested_generic_type_expression_splits_tokens() {
  parse_js::parse_with_options(
    "type T = Foo<Bar<Baz>>;",
    ParseOptions {
      dialect: ParseDialect::TypeScript,
    },
  )
  .expect("type alias with nested generics should parse");
}
