use parse_js::ast::expr::jsx::{JsxAttr, JsxAttrVal, JsxElemName};
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn tsx_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Script,
  }
}

#[test]
fn jsx_namespaced_member_allows_dotted_path() {
  let parsed = parse_with_options("<b:c.x></b:c.x>;", tsx_opts()).unwrap();
  let elem = match parsed.stx.body.first().unwrap().stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::JsxElem(elem) => elem,
      other => panic!("expected JSX element, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  };
  match &elem.stx.name {
    Some(JsxElemName::Member(member)) => {
      assert_eq!(member.stx.base.stx.name, "b:c");
      assert_eq!(member.stx.path, vec!["x".to_string()]);
    }
    other => panic!("expected member name, got {:?}", other),
  }
}

#[test]
fn jsx_attribute_missing_value_recovers_as_empty_text() {
  let parsed = parse_with_options("<div attr= />", tsx_opts()).unwrap();
  let elem = match parsed.stx.body.first().unwrap().stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::JsxElem(elem) => elem,
      other => panic!("expected JSX element, got {:?}", other),
    },
    other => panic!("expected expression statement, got {:?}", other),
  };
  let attrs = &elem.stx.attributes;
  assert_eq!(attrs.len(), 1);
  match &attrs[0] {
    JsxAttr::Named { value, .. } => match value {
      Some(JsxAttrVal::Text(text)) => assert_eq!(text.stx.value, ""),
      other => panic!("expected text value, got {:?}", other),
    },
    other => panic!("expected named attribute, got {:?}", other),
  }
}

#[test]
fn jsx_type_arguments_are_skipped_in_jsx() {
  parse_with_options("<MyComp<Prop> a={10} />", tsx_opts()).unwrap();
}

#[test]
fn jsx_attribute_value_allows_spread_recovery() {
  parse_with_options("<X a={...props} />", tsx_opts()).unwrap();
}
