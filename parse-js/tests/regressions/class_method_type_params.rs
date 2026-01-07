use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ts_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

fn with_class_members<
  F: FnOnce(&[parse_js::ast::node::Node<parse_js::ast::class_or_object::ClassMember>]),
>(
  src: &str,
  f: F,
) {
  let ast = parse_with_options(src, ts_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);
  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => &decl.stx.members,
    other => panic!("expected class declaration, got {other:?}"),
  };
  f(members);
}

#[test]
fn class_async_method_can_have_type_parameters() {
  with_class_members("class C { async foo<T>(x: T) { return x } }", |members| {
    assert_eq!(members.len(), 1);

    let member = &members[0].stx;
    match &member.key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = &member.val else {
      panic!("expected method");
    };
    assert!(method.stx.func.stx.async_);
    assert!(!method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn class_generator_method_can_have_type_parameters() {
  with_class_members("class C { *foo<T>() { } }", |members| {
    assert_eq!(members.len(), 1);

    let member = &members[0].stx;
    match &member.key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = &member.val else {
      panic!("expected method");
    };
    assert!(!method.stx.func.stx.async_);
    assert!(method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn class_async_generator_method_can_have_type_parameters() {
  with_class_members("class C { async *foo<T>() { } }", |members| {
    assert_eq!(members.len(), 1);

    let member = &members[0].stx;
    match &member.key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = &member.val else {
      panic!("expected method");
    };
    assert!(method.stx.func.stx.async_);
    assert!(method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn class_method_named_async_can_have_type_parameters() {
  with_class_members("class C { async<T>(x: T) { return x } }", |members| {
    assert_eq!(members.len(), 1);

    let member = &members[0].stx;
    match &member.key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "async"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = &member.val else {
      panic!("expected method");
    };
    assert!(!method.stx.func.stx.async_);
    assert!(!method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}
