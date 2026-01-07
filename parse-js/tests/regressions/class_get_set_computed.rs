use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
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
fn class_getter_computed_key_parses() {
  let ast = parse_with_options("class C { get [foo](){} }", ecma_script_opts()).unwrap();
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
  assert!(matches!(member.val, ClassOrObjVal::Getter(_)));
}

#[test]
fn class_setter_computed_key_parses() {
  let ast = parse_with_options("class C { set [foo](v){} }", ecma_script_opts()).unwrap();
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
  assert!(matches!(member.val, ClassOrObjVal::Setter(_)));
}

#[test]
fn class_getter_computed_key_line_terminator_is_not_a_modifier() {
  let ast = parse_with_options("class C { get\n[foo](){} }", ecma_script_opts()).unwrap();
  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 2);

  // First member: field `get`
  let first = &members[0].stx;
  match &first.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "get"),
    other => panic!("expected direct key, got {other:?}"),
  }
  assert!(matches!(first.val, ClassOrObjVal::Prop(None)));

  // Second member: non-async method `[foo]`
  let second = &members[1].stx;
  let ClassOrObjKey::Computed(expr) = &second.key else {
    panic!("expected computed key");
  };
  match expr.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
    other => panic!("expected IdExpr, got {other:?}"),
  }
  assert!(matches!(second.val, ClassOrObjVal::Method(_)));
}

#[test]
fn class_setter_computed_key_line_terminator_is_not_a_modifier() {
  let ast = parse_with_options("class C { set\n[foo](v){} }", ecma_script_opts()).unwrap();
  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 2);

  // First member: field `set`
  let first = &members[0].stx;
  match &first.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "set"),
    other => panic!("expected direct key, got {other:?}"),
  }
  assert!(matches!(first.val, ClassOrObjVal::Prop(None)));

  // Second member: non-async method `[foo]`
  let second = &members[1].stx;
  let ClassOrObjKey::Computed(expr) = &second.key else {
    panic!("expected computed key");
  };
  match expr.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "foo"),
    other => panic!("expected IdExpr, got {other:?}"),
  }
  assert!(matches!(second.val, ClassOrObjVal::Method(_)));
}
