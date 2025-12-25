use emit_js::{emit_stmt, Emitter};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::{ForInOfLhs, ForTripleStmtInit, Stmt};
use parse_js::ast::stx::TopLevel;

fn parse_first_stmt(source: &str) -> Node<Stmt> {
  let parsed = parse_js::parse(source).expect("source should parse");
  let TopLevel { body } = *parsed.stx;
  body.into_iter().next().expect("expected statement")
}

fn emit_and_reparse(stmt: &Node<Stmt>) -> (String, Node<Stmt>) {
  let mut emitter = Emitter::default();
  emit_stmt(&mut emitter, stmt).expect("emit should succeed");
  let out = String::from_utf8(emitter.into_bytes()).expect("utf-8");
  let reparsed = parse_first_stmt(&out);
  (out, reparsed)
}

#[test]
fn triple_for_init_with_contextual_let_stays_expr() {
  let stmt = parse_first_stmt("for ((let[x]=y);;){ }");
  let (_out, reparsed) = emit_and_reparse(&stmt);

  let init = match reparsed.stx.as_ref() {
    Stmt::ForTriple(for_stmt) => &for_stmt.stx.init,
    other => panic!("expected for-triple statement, got {:?}", other),
  };
  assert!(matches!(init, ForTripleStmtInit::Expr(_)));
}

#[test]
fn triple_for_init_with_contextual_using_stays_expr() {
  let stmt = parse_first_stmt("for ((using[x]=y);;){ }");
  let (_out, reparsed) = emit_and_reparse(&stmt);

  let init = match reparsed.stx.as_ref() {
    Stmt::ForTriple(for_stmt) => &for_stmt.stx.init,
    other => panic!("expected for-triple statement, got {:?}", other),
  };
  assert!(matches!(init, ForTripleStmtInit::Expr(_)));
}

#[test]
fn for_in_assign_with_contextual_let_stays_assign() {
  let stmt = parse_first_stmt("for ((let) in obj) {}");
  let (_out, reparsed) = emit_and_reparse(&stmt);

  let lhs = match reparsed.stx.as_ref() {
    Stmt::ForIn(for_stmt) => &for_stmt.stx.lhs,
    other => panic!("expected for-in statement, got {:?}", other),
  };
  assert!(matches!(lhs, ForInOfLhs::Assign(_)));
}

#[test]
fn for_of_assign_with_contextual_let_stays_assign() {
  let stmt = parse_first_stmt("for ((let) of arr) {}");
  let (_out, reparsed) = emit_and_reparse(&stmt);

  let lhs = match reparsed.stx.as_ref() {
    Stmt::ForOf(for_stmt) => &for_stmt.stx.lhs,
    other => panic!("expected for-of statement, got {:?}", other),
  };
  assert!(matches!(lhs, ForInOfLhs::Assign(_)));
}
