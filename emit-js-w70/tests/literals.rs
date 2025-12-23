use emit_js::emit;
use emit_js::string;
use emit_js::EmitMode;
use parse_js::ast::expr::lit::LitNumExpr;
use parse_js::ast::expr::lit::LitRegexExpr;
use parse_js::ast::expr::lit::LitStrExpr;
use parse_js::ast::expr::lit::LitTemplateExpr;
use parse_js::ast::expr::lit::LitTemplatePart;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::node::Node;
use parse_js::loc::Loc;
use parse_js::num::JsNumber;

fn render_string_literal(value: &str, mode: EmitMode) -> String {
  let mut out = String::new();
  string::emit_string_literal(&mut out, value, mode).unwrap();
  out
}

fn render_expr(expr: &Node<Expr>, mode: EmitMode) -> String {
  emit(expr, mode)
}

fn expr_node(stx: Expr) -> Node<Expr> {
  Node::new(Loc(0, 0), stx)
}

fn lit_num(value: f64) -> Node<Expr> {
  expr_node(Expr::LitNum(Node::new(Loc(0, 0), LitNumExpr {
    value: JsNumber(value),
  })))
}

fn lit_regex(value: &str) -> Node<Expr> {
  expr_node(Expr::LitRegex(Node::new(Loc(0, 0), LitRegexExpr {
    value: value.to_string(),
  })))
}

fn lit_str(value: &str) -> Node<Expr> {
  expr_node(Expr::LitStr(Node::new(Loc(0, 0), LitStrExpr {
    value: value.to_string(),
  })))
}

fn lit_template(parts: Vec<LitTemplatePart>) -> Node<Expr> {
  expr_node(Expr::LitTemplate(Node::new(Loc(0, 0), LitTemplateExpr {
    parts,
  })))
}

fn member_with_number(value: f64, prop: &str) -> Node<Expr> {
  let left = lit_num(value);
  expr_node(Expr::Member(Node::new(Loc(0, 0), MemberExpr {
    optional_chaining: false,
    left,
    right: prop.to_string(),
  })))
}

#[test]
fn string_literal_quote_selection_and_escaping() {
  let value_with_double = "a\"b";
  assert_eq!(
    render_string_literal(value_with_double, EmitMode::Canonical),
    "\"a\\\"b\""
  );
  assert_eq!(
    render_string_literal(value_with_double, EmitMode::Minified),
    "'a\"b'"
  );

  let value_with_single = "a'b";
  assert_eq!(
    render_string_literal(value_with_single, EmitMode::Minified),
    "\"a'b\""
  );

  let value_with_newline = "line1\nline2\\path";
  assert_eq!(
    render_string_literal(value_with_newline, EmitMode::Canonical),
    "\"line1\\nline2\\\\path\""
  );
}

#[test]
fn template_literal_escapes_backslash_tick_and_dollars() {
  let template = lit_template(vec![LitTemplatePart::String("a`b\\c${d}".to_string())]);

  let rendered = render_expr(&template, EmitMode::Canonical);
  assert_eq!(rendered, "`a\\`b\\\\c\\${d}`");
}

#[test]
fn emits_member_after_integer_literal_with_extra_dot() {
  let expr = member_with_number(1.0, "toString");
  let rendered = render_expr(&expr, EmitMode::Minified);
  assert_eq!(rendered, "1..toString");
}

#[test]
fn emits_member_after_decimal_literal_without_extra_dot() {
  let expr = member_with_number(1.2, "toString");
  let rendered = render_expr(&expr, EmitMode::Minified);
  assert_eq!(rendered, "1.2.toString");
}

#[test]
fn emits_regex_literal_verbatim() {
  let regex = lit_regex("/ab+c/i");
  let rendered = render_expr(&regex, EmitMode::Canonical);
  assert_eq!(rendered, "/ab+c/i");
}

#[test]
fn emits_string_literal_via_expression() {
  let expr = lit_str("\\` and \"quotes\"");
  let rendered = render_expr(&expr, EmitMode::Canonical);
  assert_eq!(rendered, "\"\\\\` and \\\"quotes\\\"\"");
}
