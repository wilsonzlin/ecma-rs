use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

#[test]
fn class_async_generator_computed_method_parses() {
  let ast = parse_with_options("class C { async *[foo](){ } }", ecma_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 1);

  let member = &members[0].stx;
  let ClassOrObjKey::Computed(expr) = &member.key else {
    panic!("expected computed key");
  };
  match expr.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
    other => panic!("expected IdExpr, got {other:?}"),
  }

  let ClassOrObjVal::Method(method) = &member.val else {
    panic!("expected method value");
  };
  assert!(method.stx.func.stx.async_);
  assert!(method.stx.func.stx.generator);
}

#[test]
fn object_literal_async_generator_computed_method_parses() {
  let ast = parse_with_options("({ async *[foo](){ } })", ecma_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let Stmt::Expr(stmt) = ast.stx.body[0].stx.as_ref() else {
    panic!("expected expression statement");
  };
  let Expr::LitObj(obj) = stmt.stx.expr.stx.as_ref() else {
    panic!("expected object literal expression");
  };
  assert_eq!(obj.stx.members.len(), 1);

  let member = &obj.stx.members[0].stx;
  let ObjMemberType::Valued { key, val } = &member.typ else {
    panic!("expected valued object member");
  };

  let ClassOrObjKey::Computed(expr) = key else {
    panic!("expected computed key");
  };
  match expr.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
    other => panic!("expected IdExpr, got {other:?}"),
  }

  let ClassOrObjVal::Method(method) = val else {
    panic!("expected method value");
  };
  assert!(method.stx.func.stx.async_);
  assert!(method.stx.func.stx.generator);
}

#[test]
fn object_literal_async_generator_computed_method_requires_no_line_terminator() {
  assert!(parse_with_options("({ async\n*[foo](){ } })", ecma_script_opts()).is_err());
}
