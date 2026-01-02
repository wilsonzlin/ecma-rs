use parse_js::ast::expr::jsx::JsxElemName;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::error::SyntaxErrorType;
use parse_js::token::TT;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn tsx_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Script,
  }
}

#[test]
fn jsx_namespaced_member_is_syntax_error() {
  let err = parse_with_options("<b:c.x></b:c.x>;", tsx_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("identifier"));
  assert_eq!(err.actual_token, Some(TT::Dot));
}

#[test]
fn jsx_namespaced_uppercase_is_parsed_as_intrinsic_name() {
  let parsed = parse_with_options("<Svg:Path></Svg:Path>;", tsx_opts()).unwrap();
  let elem = match parsed.stx.body.first().unwrap().stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::JsxElem(elem) => elem,
      other => panic!("expected JSX element, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  };
  match &elem.stx.name {
    Some(JsxElemName::Name(name)) => {
      assert_eq!(name.stx.namespace.as_deref(), Some("Svg"));
      assert_eq!(name.stx.name, "Path");
    }
    other => panic!("expected namespaced name, got {:?}", other),
  }
}

#[test]
fn jsx_hyphenated_uppercase_is_parsed_as_intrinsic_name() {
  let parsed = parse_with_options("<My-Tag></My-Tag>;", tsx_opts()).unwrap();
  let elem = match parsed.stx.body.first().unwrap().stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::JsxElem(elem) => elem,
      other => panic!("expected JSX element, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  };
  match &elem.stx.name {
    Some(JsxElemName::Name(name)) => {
      assert!(name.stx.namespace.is_none());
      assert_eq!(name.stx.name, "My-Tag");
    }
    other => panic!("expected hyphenated name, got {:?}", other),
  }
}

#[test]
fn jsx_attribute_missing_value_is_syntax_error() {
  let err = parse_with_options("<div attr= />", tsx_opts()).unwrap_err();
  assert_eq!(
    err.typ,
    SyntaxErrorType::ExpectedSyntax("JSX attribute value")
  );
  assert_eq!(err.actual_token, Some(TT::Slash));
}

#[test]
fn jsx_type_arguments_are_skipped_in_jsx() {
  parse_with_options("<MyComp<Prop> a={10} />", tsx_opts()).unwrap();
}

#[test]
fn jsx_attribute_value_spread_is_syntax_error() {
  let err = parse_with_options("<X a={...props} />", tsx_opts()).unwrap_err();
  assert_eq!(err.typ, SyntaxErrorType::ExpectedSyntax("expression"));
  assert_eq!(err.actual_token, Some(TT::DotDotDot));
}
