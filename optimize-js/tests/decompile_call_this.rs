use optimize_js::compile_source;
use optimize_js::decompile::il::decompile_function;
use optimize_js::TopLevelMode;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;

fn decompile_source(source: &str) -> Vec<parse_js::ast::node::Node<Stmt>> {
  let program = compile_source(source, TopLevelMode::Module, false).expect("compile");
  decompile_function(&program.top_level).expect("decompile")
}

fn first_call(stmts: &[parse_js::ast::node::Node<Stmt>]) -> &parse_js::ast::expr::CallExpr {
  let stmt = stmts.first().expect("stmt");
  match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => match expr_stmt.stx.expr.stx.as_ref() {
      Expr::Call(call) => call.stx.as_ref(),
      other => panic!("expected call expr, got {other:?}"),
    },
    other => panic!("expected expr stmt, got {other:?}"),
  }
}

#[test]
fn method_call_reconstructed() {
  let stmts = decompile_source("obj.m(1);");
  let call = first_call(&stmts);
  match call.callee.stx.as_ref() {
    Expr::Member(member) => {
      let member = member.stx.as_ref();
      match member.left.stx.as_ref() {
        Expr::Id(id) => assert_eq!(id.stx.name, "obj"),
        other => panic!("expected id callee base, got {other:?}"),
      }
      assert_eq!(member.right, "m");
    }
    other => panic!("expected member callee, got {other:?}"),
  }
  assert_eq!(call.arguments.len(), 1);
}

#[test]
fn explicit_call_preserved() {
  let stmts = decompile_source("func.call(obj, 1);");
  let call = first_call(&stmts);
  match call.callee.stx.as_ref() {
    Expr::Member(member) => {
      let member = member.stx.as_ref();
      match member.left.stx.as_ref() {
        Expr::Id(id) => assert_eq!(id.stx.name, "func"),
        other => panic!("expected id callee base, got {other:?}"),
      }
      assert_eq!(member.right, "call");
    }
    other => panic!("expected member callee, got {other:?}"),
  }
  assert_eq!(call.arguments.len(), 2);
  match call.arguments[0].stx.value.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "obj"),
    other => panic!("expected obj as first arg, got {other:?}"),
  }
}
