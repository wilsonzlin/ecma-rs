use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

fn ecma_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  }
}

#[test]
fn async_arrow_comment_with_newline_does_not_form_async_arrow() {
  let ast = parse_with_options("async/*\n*/x => x", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 2);

  match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "async"),
      other => panic!("expected IdExpr, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }

  match ast.stx.body[1].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::ArrowFunc(arrow) => {
        assert!(!arrow.stx.func.stx.async_);
        assert_eq!(arrow.stx.func.stx.parameters.len(), 1);
        let param = &arrow.stx.func.stx.parameters[0];
        match param.stx.pattern.stx.pat.stx.as_ref() {
          Pat::Id(id) => assert_eq!(id.stx.name, "x"),
          other => panic!("expected IdPat, got {other:?}"),
        }
      }
      other => panic!("expected arrow function, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  }
}

#[test]
fn class_get_comment_with_newline_is_not_a_modifier() {
  let ast = parse_with_options("class C { get/*\n*/foo(){} }", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 2);

  let first = &members[0].stx;
  match &first.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "get"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &first.val {
    ClassOrObjVal::Prop(init) => assert!(init.is_none()),
    other => panic!("expected field property, got {other:?}"),
  }

  let second = &members[1].stx;
  match &second.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &second.val {
    ClassOrObjVal::Method(_) => {}
    other => panic!("expected method, got {other:?}"),
  }
}

#[test]
fn class_set_comment_with_newline_is_not_a_modifier() {
  let ast = parse_with_options("class C { set/*\n*/foo(v){} }", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 2);

  let first = &members[0].stx;
  match &first.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "set"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &first.val {
    ClassOrObjVal::Prop(init) => assert!(init.is_none()),
    other => panic!("expected field property, got {other:?}"),
  }

  let second = &members[1].stx;
  match &second.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &second.val {
    ClassOrObjVal::Method(_) => {}
    other => panic!("expected method, got {other:?}"),
  }
}

#[test]
fn class_async_comment_with_newline_is_not_a_modifier() {
  let ast = parse_with_options("class C { async/*\n*/foo(){} }", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 2);

  let first = &members[0].stx;
  match &first.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "async"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &first.val {
    ClassOrObjVal::Prop(init) => assert!(init.is_none()),
    other => panic!("expected field property, got {other:?}"),
  }

  let second = &members[1].stx;
  match &second.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &second.val {
    ClassOrObjVal::Method(method) => {
      assert!(!method.stx.func.stx.async_);
    }
    other => panic!("expected method, got {other:?}"),
  }
}

#[test]
fn object_literal_get_comment_with_newline_is_syntax_error() {
  assert!(parse_with_options("({ get/*\n*/foo(){} })", ecma_script_opts()).is_err());
}

#[test]
fn object_literal_set_comment_with_newline_is_syntax_error() {
  assert!(parse_with_options("({ set/*\n*/foo(v){} })", ecma_script_opts()).is_err());
}
