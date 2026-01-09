use parse_js::ast::expr::Expr;
use parse_js::ast::node::template_string_parts;
use parse_js::ast::stmt::Stmt;
use parse_js::parse;

fn template_parts_of_first_expr_statement(source: &str) -> parse_js::ast::node::TemplateStringParts {
  let ast = parse(source).expect("expected parse success");
  let stmt = ast.stx.body.first().expect("expected statement");
  let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
    panic!("expected expression statement, got {:?}", stmt.stx);
  };

  let expr = expr_stmt.stx.expr.stx.as_ref();
  match expr {
    Expr::TaggedTemplate(tagged) => template_string_parts(&tagged.assoc)
      .expect("expected TemplateStringParts assoc data")
      .clone(),
    Expr::LitTemplate(template) => template_string_parts(&template.assoc)
      .expect("expected TemplateStringParts assoc data")
      .clone(),
    other => panic!("expected template expression, got {:?}", other),
  }
}

#[test]
fn tagged_template_invalid_escape_has_undefined_cooked_and_preserves_raw() {
  let parts = template_parts_of_first_expr_statement("tag`\\u{10FFFFF}`");
  assert_eq!(parts.raw.len(), 1);
  let expected_raw: Vec<u16> = "\\u{10FFFFF}".encode_utf16().collect();
  assert_eq!(
    parts.raw[0].as_ref(),
    expected_raw.as_slice()
  );
  assert_eq!(parts.cooked.len(), 1);
  assert!(parts.cooked[0].is_none());
}

#[test]
fn tagged_template_valid_escape_preserves_raw_and_cooked_utf16() {
  let parts = template_parts_of_first_expr_statement("tag`\\u{1F600}`");
  assert_eq!(parts.raw.len(), 1);
  let expected_raw: Vec<u16> = "\\u{1F600}".encode_utf16().collect();
  assert_eq!(
    parts.raw[0].as_ref(),
    expected_raw.as_slice()
  );
  assert_eq!(parts.cooked.len(), 1);
  assert_eq!(
    parts.cooked[0].as_deref(),
    Some(&[0xD83D, 0xDE00][..])
  );
}

#[test]
fn untagged_template_invalid_escape_is_syntax_error() {
  assert!(parse("`\\u{10FFFFF}`").is_err());
}
