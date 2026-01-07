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
fn class_get_line_terminator_still_forms_getter() {
  let ast = parse_with_options("class C { get\nfoo(){} }", js_script_opts()).unwrap();
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
    ClassOrObjVal::Getter(_) => {}
    other => panic!("expected getter, got {other:?}"),
  }
}

#[test]
fn class_get_without_line_terminator_is_getter() {
  let ast = parse_with_options("class C { get foo(){} }", js_script_opts()).unwrap();
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
    ClassOrObjVal::Getter(_) => {}
    other => panic!("expected getter, got {other:?}"),
  }
}

#[test]
fn class_set_line_terminator_still_forms_setter() {
  let ast = parse_with_options("class C { set\nfoo(v){} }", js_script_opts()).unwrap();
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
    ClassOrObjVal::Setter(_) => {}
    other => panic!("expected setter, got {other:?}"),
  }
}

#[test]
fn class_set_without_line_terminator_is_setter() {
  let ast = parse_with_options("class C { set foo(v){} }", js_script_opts()).unwrap();
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
    ClassOrObjVal::Setter(_) => {}
    other => panic!("expected setter, got {other:?}"),
  }
}
