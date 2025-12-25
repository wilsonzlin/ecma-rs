use derive_visitor::{Drive, DriveMut};
use emit_js::asi::{separator_after_last, separator_between, ListEnd, Separator};
use parse_js::ast::expr::lit::{
  LitArrExpr,
  LitObjExpr,
  LitRegexExpr,
  LitTemplateExpr,
  LitTemplatePart,
};
use parse_js::ast::expr::{Expr, IdExpr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{
  BlockStmt,
  EmptyStmt,
  ExprStmt,
  ForBody,
  ForTripleStmt,
  ForTripleStmtInit,
  IfStmt,
  LabelStmt,
  Stmt,
  WhileStmt,
};
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

fn object_expr() -> Node<Expr> {
  node(Expr::LitObj(node(LitObjExpr { members: vec![] })))
}

fn expr_stmt(expr: Node<Expr>) -> Node<Stmt> {
  node(Stmt::Expr(node(ExprStmt { expr })))
}

fn block_stmt(body: Vec<Node<Stmt>>) -> Node<Stmt> {
  node(Stmt::Block(node(BlockStmt { body })))
}

fn if_stmt(consequent: Node<Stmt>) -> Node<Stmt> {
  node(Stmt::If(node(IfStmt {
    test: id("x"),
    consequent,
    alternate: None,
  })))
}

fn for_stmt(body: Node<Stmt>) -> Node<Stmt> {
  node(Stmt::ForTriple(node(ForTripleStmt {
    init: ForTripleStmtInit::None,
    cond: None,
    post: None,
    body: node(ForBody { body: vec![body] }),
  })))
}

fn label_stmt(statement: Node<Stmt>) -> Node<Stmt> {
  node(Stmt::Label(node(LabelStmt {
    name: "label".to_string(),
    statement,
  })))
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

#[test]
fn wrapped_leaf_statement_tails_trigger_hazards() {
  let prev_if = if_stmt(expr_stmt(id("a")));
  let prev_for = for_stmt(expr_stmt(id("a")));
  let prev_label = label_stmt(expr_stmt(id("a")));

  assert_eq!(
    separator_between(Some(&prev_if), &expr_stmt(object_expr())),
    Separator::Semicolon
  );
  assert_eq!(
    separator_between(Some(&prev_for), &expr_stmt(array_expr())),
    Separator::Semicolon
  );
  assert_eq!(
    separator_between(Some(&prev_label), &expr_stmt(template_expr())),
    Separator::Semicolon
  );
}

#[test]
fn wrapped_leaf_statement_non_expression_tail_is_not_hazardous() {
  let prev = if_stmt(block_stmt(vec![]));
  let next = expr_stmt(object_expr());
  assert_ne!(separator_between(Some(&prev), &next), Separator::Semicolon);
}
