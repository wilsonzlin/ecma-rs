use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::parse_with_options;
use parse_js::{Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

#[test]
fn async_call_expression_is_not_an_async_arrow() {
  let parsed = parse_with_options("async()", ecma_script_opts()).expect("expected call expression");
  assert_eq!(parsed.stx.body.len(), 1);
  let Stmt::Expr(expr_stmt) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Call(call) => match call.stx.callee.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected identifier callee, got {other:?}"),
    },
    other => panic!("expected call expression, got {other:?}"),
  }
}

#[test]
fn object_method_named_async_is_not_async() {
  let parsed =
    parse_with_options("({ async(){} })", ecma_script_opts()).expect("expected object literal");
  assert_eq!(parsed.stx.body.len(), 1);
  let Stmt::Expr(expr_stmt) = parsed.stx.body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::LitObj(obj) = expr_stmt.stx.expr.stx.as_ref() else {
    panic!("expected object literal expression");
  };
  assert_eq!(obj.stx.members.len(), 1);
  let member = &obj.stx.members[0].stx;
  let ObjMemberType::Valued { key, val } = &member.typ else {
    panic!("expected valued member");
  };
  match key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "async"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match val {
    ClassOrObjVal::Method(method) => assert!(!method.stx.func.stx.async_),
    other => panic!("expected method value, got {other:?}"),
  }
}
