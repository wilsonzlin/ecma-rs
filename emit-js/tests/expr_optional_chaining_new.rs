use emit_js::emit_expr;
use parse_js::ast::expr::{CallExpr, Expr, IdExpr, MemberExpr, UnaryExpr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::error::SyntaxErrorType;
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;

mod util;

fn parse_expr(source: &str) -> Node<Expr> {
  let parsed = parse_js::parse(source).expect("parse failed");
  let TopLevel { mut body } = *parsed.stx;
  assert_eq!(body.len(), 1, "expected a single statement");
  match *body.pop().unwrap().stx {
    Stmt::Expr(expr_stmt) => expr_stmt.stx.expr,
    other => panic!("unexpected statement: {other:?}"),
  }
}

fn emit_expr_to_string(expr: &Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr(&mut out, expr, &mut emit_type).expect("emit should succeed");
  out
}

fn node<T: derive_visitor::Drive + derive_visitor::DriveMut>(stx: T) -> Node<T> {
  Node::new(Loc(0, 0), stx)
}

fn id_expr(name: &str) -> Node<Expr> {
  node(Expr::Id(node(IdExpr {
    name: name.to_string(),
  })))
}

fn member_expr(left: Node<Expr>, right: &str, optional: bool) -> Node<Expr> {
  node(Expr::Member(node(MemberExpr {
    optional_chaining: optional,
    left,
    right: right.to_string(),
  })))
}

fn call_expr(callee: Node<Expr>) -> Node<Expr> {
  node(Expr::Call(node(CallExpr {
    optional_chaining: false,
    callee,
    arguments: vec![],
  })))
}

fn new_expr(argument: Node<Expr>) -> Node<Expr> {
  node(Expr::Unary(node(UnaryExpr {
    operator: OperatorName::New,
    argument,
  })))
}

fn unary_plus(argument: Node<Expr>) -> Node<Expr> {
  node(Expr::Unary(node(UnaryExpr {
    operator: OperatorName::UnaryPlus,
    argument,
  })))
}

/// Illegal as source (parse-js PS0017); keep emitter coverage via synthetic AST.
fn assert_emit_constructed(expr: Node<Expr>, expected_emitted: &str) {
  let emitted = emit_expr_to_string(&expr);
  assert_eq!(emitted, expected_emitted);

  let reparsed = parse_expr(&format!("{emitted};"));
  assert_eq!(
    util::serialize_without_locs(&expr),
    util::serialize_without_locs(&reparsed),
    "roundtrip mismatch emitted as `{emitted}`"
  );
}

fn assert_parse_rejects(src: &str) {
  let err = parse_js::parse(src).expect_err(&format!("expected parse reject for {src:?}"));
  assert_eq!(
    err.typ,
    SyntaxErrorType::InvalidOptionalChainFromNew,
    "expected PS0017 for {src:?}, got {:?}",
    err.typ
  );
}

#[test]
fn parenthesizes_new_optional_chain_without_args() {
  assert_parse_rejects("new abc?.def;");
  assert_emit_constructed(
    new_expr(member_expr(id_expr("abc"), "def", true)),
    "new (abc?.def)",
  );
}

#[test]
fn parenthesizes_new_optional_chain_with_args() {
  assert_parse_rejects("new abc?.def();");
  assert_emit_constructed(
    new_expr(call_expr(member_expr(id_expr("abc"), "def", true))),
    "new (abc?.def)()",
  );
}

#[test]
fn parenthesizes_new_optional_chain_with_unary_plus() {
  assert_parse_rejects("+new abc?.def();");
  assert_emit_constructed(
    unary_plus(new_expr(call_expr(member_expr(
      id_expr("abc"),
      "def",
      true,
    )))),
    "+new (abc?.def)()",
  );
}
