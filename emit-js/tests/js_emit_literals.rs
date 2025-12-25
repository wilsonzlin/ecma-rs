use emit_js::emit_expr;
use parse_js::ast::expr::lit::{LitBigIntExpr, LitNullExpr, LitRegexExpr};
use parse_js::ast::expr::{Expr, IdExpr, ImportMeta, NewTarget, ThisExpr};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::loc::Loc;

fn node<T: derive_visitor::Drive + derive_visitor::DriveMut>(stx: T) -> Node<T> {
  Node::new(Loc(0, 0), stx)
}

fn emit(expr: Node<Expr>) -> String {
  let mut out = String::new();
  let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
  emit_expr(&mut out, &expr, &mut emit_type).unwrap();
  out
}

#[test]
fn emits_null() {
  let expr = node(Expr::LitNull(node(LitNullExpr {})));
  assert_eq!(emit(expr), "null");
}

#[test]
fn emits_big_int_literal() {
  let expr = node(Expr::LitBigInt(node(LitBigIntExpr {
    value: "123n".to_string(),
  })));
  assert_eq!(emit(expr), "123n");
}

#[test]
fn emits_regex_literal() {
  let expr = node(Expr::LitRegex(node(LitRegexExpr {
    value: "/abc/g".to_string(),
  })));
  assert_eq!(emit(expr), "/abc/g");
}

#[test]
fn emits_this_expression() {
  let expr = node(Expr::This(node(ThisExpr {})));
  assert_eq!(emit(expr), "this");
}

#[test]
fn emits_new_target_expression() {
  let expr = node(Expr::NewTarget(node(NewTarget {})));
  assert_eq!(emit(expr), "new.target");
}

#[test]
fn emits_import_meta_expression() {
  let expr = node(Expr::ImportMeta(node(ImportMeta {})));
  assert_eq!(emit(expr), "import.meta");
}

#[test]
fn emits_undefined_as_void_0() {
  let expr = node(Expr::Id(node(IdExpr {
    name: "undefined".to_string(),
  })));
  assert_eq!(emit(expr), "void 0");
}
