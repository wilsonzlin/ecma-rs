use parse_js::ast::expr::CallArg;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::type_expr::TypeEntityName;
use parse_js::ast::type_expr::TypeExpr;

#[test]
fn parses_optional_call_with_type_arguments() {
  let ast = parse_js::parse("fn?.<T>(x);").expect("should parse optional call with type args");

  let stmt = ast.stx.body.first().expect("expected one statement");
  let expr = match stmt.stx.as_ref() {
    Stmt::Expr(expr_stmt) => &expr_stmt.stx.expr,
    other => panic!("expected expression statement, got {other:?}"),
  };

  let call = match expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression, got {other:?}"),
  };
  assert!(call.stx.optional_chaining, "call should be optional");

  let inst = match call.stx.callee.stx.as_ref() {
    Expr::Instantiation(inst) => inst,
    other => panic!("expected instantiation callee, got {other:?}"),
  };

  match inst.stx.expression.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "fn"),
    other => panic!("expected identifier callee, got {other:?}"),
  }

  assert_eq!(inst.stx.type_arguments.len(), 1);
  match inst.stx.type_arguments[0].stx.as_ref() {
    TypeExpr::TypeReference(type_ref) => match &type_ref.stx.name {
      TypeEntityName::Identifier(name) => assert_eq!(name, "T"),
      other => panic!("expected identifier type argument, got {other:?}"),
    },
    other => panic!("expected type reference type argument, got {other:?}"),
  }

  assert_eq!(call.stx.arguments.len(), 1);
  match call.stx.arguments[0].stx.as_ref() {
    CallArg { spread: false, value } => match value.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "x"),
      other => panic!("expected id argument, got {other:?}"),
    },
    other => panic!("expected single non-spread argument, got {other:?}"),
  }
}

