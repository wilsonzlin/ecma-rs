use parse_js::ast::expr::jsx::JsxElemChild;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn tsx_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Tsx,
    source_type: SourceType::Script,
  }
}

fn jsx_text_values(source: &str) -> Vec<String> {
  let parsed = parse_with_options(source, tsx_opts()).expect("parse should succeed");
  let stmt = parsed.stx.body.first().expect("expected a statement");
  let expr = match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
    other => panic!("expected expression statement, got {:?}", other),
  };
  let elem = match expr.stx.as_ref() {
    Expr::JsxElem(elem) => elem,
    other => panic!("expected JSX element, got {:?}", other),
  };

  elem
    .stx
    .children
    .iter()
    .filter_map(|child| match child {
      JsxElemChild::Text(text) => Some(text.stx.value.clone()),
      _ => None,
    })
    .collect()
}

#[test]
fn jsx_text_allows_unescaped_brace_in_text() {
  let texts = jsx_text_values("<div>}</div>");
  assert_eq!(texts, vec!["}"]);
}

#[test]
fn jsx_text_allows_unescaped_gt_in_text() {
  let texts = jsx_text_values("<div>></div>");
  assert_eq!(texts, vec![">"]);
}

#[test]
fn jsx_attribute_string_allows_escaped_quote() {
  let source = "<div attr=\"&#0123;&hellip;&#x7D;\\\"></div>;";
  parse_with_options(source, tsx_opts()).unwrap();
}
