use parse_js::ast::expr::Expr;
use parse_js::ast::node::literal_string_code_units;
use parse_js::ast::stmt::Stmt;
use parse_js::parse;

fn code_units_of_first_expr_statement(source: &str) -> Vec<u16> {
  let ast = parse(source).expect("expected parse success");
  let stmt = ast.stx.body.first().expect("expected statement");
  let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
    panic!("expected expression statement, got {:?}", stmt.stx);
  };
  let Expr::LitStr(lit) = expr_stmt.stx.expr.stx.as_ref() else {
    panic!("expected string literal expression, got {:?}", expr_stmt.stx.expr.stx);
  };
  literal_string_code_units(&lit.assoc)
    .expect("expected LiteralStringCodeUnits assoc data")
    .to_vec()
}

#[test]
fn preserves_unpaired_surrogate_code_units_from_u_escape() {
  assert_eq!(
    code_units_of_first_expr_statement("\"\\uD800\""),
    vec![0xD800]
  );
}

#[test]
fn preserves_surrogate_pair_from_two_u_escapes() {
  assert_eq!(
    code_units_of_first_expr_statement("\"\\uD83D\\uDE00\""),
    vec![0xD83D, 0xDE00]
  );
}

#[test]
fn encodes_u_braced_escape_over_bmp_as_surrogate_pair() {
  assert_eq!(
    code_units_of_first_expr_statement("\"\\u{1F600}\""),
    vec![0xD83D, 0xDE00]
  );
}

#[test]
fn preserves_braced_surrogate_code_point_escape_as_single_code_unit() {
  assert_eq!(
    code_units_of_first_expr_statement("\"\\u{D800}\""),
    vec![0xD800]
  );
}

