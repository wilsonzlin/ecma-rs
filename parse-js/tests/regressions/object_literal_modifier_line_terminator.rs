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
fn object_literal_async_modifier_must_not_cross_line_terminator() {
  assert!(parse_with_options("({ async\nfoo(){} })", ecma_script_opts()).is_err());
}

#[test]
fn object_literal_get_allows_line_terminator_after_keyword() {
  let ast = parse_with_options("({ get\nfoo(){} })", ecma_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let member = match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::LitObj(obj) => &obj.stx.members,
      other => panic!("expected object literal, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  };
  assert_eq!(member.len(), 1);

  let ObjMemberType::Valued { key, val } = &member[0].stx.typ else {
    panic!("expected valued object member");
  };
  match key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  assert!(matches!(val, ClassOrObjVal::Getter(_)));
}

#[test]
fn object_literal_set_allows_line_terminator_after_keyword() {
  let ast = parse_with_options("({ set\nfoo(v){} })", ecma_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let member = match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::LitObj(obj) => &obj.stx.members,
      other => panic!("expected object literal, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  };
  assert_eq!(member.len(), 1);

  let ObjMemberType::Valued { key, val } = &member[0].stx.typ else {
    panic!("expected valued object member");
  };
  match key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  assert!(matches!(val, ClassOrObjVal::Setter(_)));
}

#[test]
fn object_literal_get_computed_allows_line_terminator_after_keyword() {
  let ast = parse_with_options("({ get\n[foo](){} })", ecma_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::LitObj(obj) => &obj.stx.members,
      other => panic!("expected object literal, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  };
  assert_eq!(members.len(), 1);

  let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
    panic!("expected valued object member");
  };
  match key {
    ClassOrObjKey::Computed(expr) => match expr.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected computed key, got {other:?}"),
  }
  assert!(matches!(val, ClassOrObjVal::Getter(_)));
}

#[test]
fn object_literal_set_computed_allows_line_terminator_after_keyword() {
  let ast = parse_with_options("({ set\n[foo](v){} })", ecma_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::LitObj(obj) => &obj.stx.members,
      other => panic!("expected object literal, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  };
  assert_eq!(members.len(), 1);

  let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
    panic!("expected valued object member");
  };
  match key {
    ClassOrObjKey::Computed(expr) => match expr.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected computed key, got {other:?}"),
  }
  assert!(matches!(val, ClassOrObjVal::Setter(_)));
}
