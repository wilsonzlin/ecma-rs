use derive_visitor::{Drive, DriveMut};
use emit_js::asi::{separator_after_last, separator_between, ListEnd, Separator};
use parse_js::ast::expr::lit::{LitArrExpr, LitRegexExpr, LitTemplateExpr, LitTemplatePart};
use parse_js::ast::expr::{Expr, IdExpr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{BlockStmt, EmptyStmt, ExprStmt, Stmt, WhileStmt};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;

fn node<T: Drive + DriveMut>(stx: T) -> Node<T> {
  Node::new(Loc(0, 0), stx)
}

fn id(name: &str) -> Node<Expr> {
  node(Expr::Id(node(IdExpr {
    name: name.to_string(),
  })))
}

fn regex(value: &str) -> Node<Expr> {
  node(Expr::LitRegex(node(LitRegexExpr {
    value: value.to_string(),
  })))
}

fn array_expr() -> Node<Expr> {
  node(Expr::LitArr(node(LitArrExpr { elements: vec![] })))
}

fn unary_expr(operator: OperatorName, argument: Node<Expr>) -> Node<Expr> {
  node(Expr::Unary(node(UnaryExpr { operator, argument })))
}

fn template_expr() -> Node<Expr> {
  node(Expr::LitTemplate(node(LitTemplateExpr {
    parts: vec![LitTemplatePart::String(String::new())],
  })))
}

fn expr_stmt(expr: Node<Expr>) -> Node<Stmt> {
  node(Stmt::Expr(node(ExprStmt { expr })))
}

fn block_stmt(body: Vec<Node<Stmt>>) -> Node<Stmt> {
  node(Stmt::Block(node(BlockStmt { body })))
}

fn empty_stmt() -> Node<Stmt> {
  node(Stmt::Empty(node(EmptyStmt {})))
}

fn while_stmt(condition: Node<Expr>, body: Node<Stmt>) -> Node<Stmt> {
  node(Stmt::While(node(WhileStmt { condition, body })))
}

#[test]
fn expr_stmt_then_regex_requires_semicolon() {
  let prev = expr_stmt(id("a"));
  let next = expr_stmt(regex("/x/"));

  assert_eq!(separator_between(Some(&prev), &next), Separator::Semicolon);
}

#[test]
fn block_leaf_does_not_require_separator_before_hazard() {
  let prev = block_stmt(vec![]);
  let next = expr_stmt(array_expr());

  assert_eq!(separator_between(Some(&prev), &next), Separator::None);
}

#[test]
fn while_with_empty_body_requires_semicolon() {
  let body = empty_stmt();
  let prev = while_stmt(id("x"), body);
  let next = expr_stmt(id("y"));

  assert_eq!(separator_between(Some(&prev), &next), Separator::Semicolon);
}

#[test]
fn empty_leaf_at_end_before_close_brace_needs_semicolon() {
  let stmt = while_stmt(id("x"), empty_stmt());

  assert_eq!(
    separator_after_last(&stmt, ListEnd::CloseBrace),
    Separator::Semicolon
  );
}

#[test]
fn hazardous_starters_upgrade_separator() {
  let prev = expr_stmt(id("value"));
  let hazards = [
    expr_stmt(array_expr()),
    expr_stmt(unary_expr(OperatorName::UnaryPlus, id("x"))),
    expr_stmt(unary_expr(OperatorName::UnaryNegation, id("x"))),
    expr_stmt(template_expr()),
  ];

  for next in hazards {
    assert_eq!(separator_between(Some(&prev), &next), Separator::Semicolon);
  }
}
