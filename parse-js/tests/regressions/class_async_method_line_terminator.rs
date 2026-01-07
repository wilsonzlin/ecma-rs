use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn js_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  }
}

#[test]
fn class_async_method_line_terminator_is_not_a_modifier() {
  let ast = parse_with_options("class C { async\nfoo(){} }", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 2);

  // First member: field `async`
  let first = &members[0].stx;
  match &first.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "async"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &first.val {
    ClassOrObjVal::Prop(init) => assert!(init.is_none()),
    other => panic!("expected field property, got {other:?}"),
  }

  // Second member: non-async method `foo`
  let second = &members[1].stx;
  match &second.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &second.val {
    ClassOrObjVal::Method(method) => assert!(!method.stx.func.stx.async_),
    other => panic!("expected method, got {other:?}"),
  }
}

#[test]
fn class_async_method_without_line_terminator_is_async() {
  let ast = parse_with_options("class C { async foo(){} }", js_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);

  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  assert_eq!(members.len(), 1);

  let member = &members[0].stx;
  match &member.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
    other => panic!("expected direct key, got {other:?}"),
  }
  match &member.val {
    ClassOrObjVal::Method(method) => assert!(method.stx.func.stx.async_),
    other => panic!("expected method, got {other:?}"),
  }
}
