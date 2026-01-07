use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::Expr;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

fn ts_script_opts() -> ParseOptions {
  ParseOptions {
    dialect: Dialect::Ts,
    source_type: SourceType::Script,
  }
}

fn with_object_members<F: FnOnce(&[parse_js::ast::node::Node<parse_js::ast::class_or_object::ObjMember>])>(
  src: &str,
  f: F,
) {
  let ast = parse_with_options(src, ts_script_opts()).unwrap();
  assert_eq!(ast.stx.body.len(), 1);
  let members = match ast.stx.body[0].stx.as_ref() {
    Stmt::Expr(stmt) => match stmt.stx.expr.stx.as_ref() {
      Expr::LitObj(obj) => &obj.stx.members,
      other => panic!("expected object literal, got {other:?}"),
    },
    other => panic!("expected expression statement, got {other:?}"),
  };
  f(members);
}

#[test]
fn object_literal_method_named_async_can_have_type_parameters() {
  with_object_members("({ async<T>(x: T) { return x } })", |members| {
    assert_eq!(members.len(), 1);

    let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
      panic!("expected valued object member");
    };
    match key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "async"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = val else {
      panic!("expected method");
    };
    assert!(!method.stx.func.stx.async_);
    assert!(!method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn object_literal_async_method_can_have_type_parameters() {
  with_object_members("({ async foo<T>(x: T) { return x } })", |members| {
    assert_eq!(members.len(), 1);

    let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
      panic!("expected valued object member");
    };
    match key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = val else {
      panic!("expected method");
    };
    assert!(method.stx.func.stx.async_);
    assert!(!method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn object_literal_generator_method_can_have_type_parameters() {
  with_object_members("({ *foo<T>() {} })", |members| {
    assert_eq!(members.len(), 1);

    let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
      panic!("expected valued object member");
    };
    match key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = val else {
      panic!("expected method");
    };
    assert!(!method.stx.func.stx.async_);
    assert!(method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn object_literal_async_generator_method_can_have_type_parameters() {
  with_object_members("({ async *foo<T>() {} })", |members| {
    assert_eq!(members.len(), 1);

    let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
      panic!("expected valued object member");
    };
    match key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "foo"),
      other => panic!("expected direct key, got {other:?}"),
    }
    let ClassOrObjVal::Method(method) = val else {
      panic!("expected method");
    };
    assert!(method.stx.func.stx.async_);
    assert!(method.stx.func.stx.generator);
    assert!(method.stx.func.stx.type_parameters.is_some());
  });
}

#[test]
fn object_literal_method_named_get_can_have_type_parameters() {
  with_object_members("({ get<T>(x: T) { return x } })", |members| {
    assert_eq!(members.len(), 1);

    let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
      panic!("expected valued object member");
    };
    match key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "get"),
      other => panic!("expected direct key, got {other:?}"),
    }
    assert!(matches!(val, ClassOrObjVal::Method(_)));
  });
}

#[test]
fn object_literal_method_named_set_can_have_type_parameters() {
  with_object_members("({ set<T>(x: T) { return x } })", |members| {
    assert_eq!(members.len(), 1);

    let ObjMemberType::Valued { key, val } = &members[0].stx.typ else {
      panic!("expected valued object member");
    };
    match key {
      ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "set"),
      other => panic!("expected direct key, got {other:?}"),
    }
    assert!(matches!(val, ClassOrObjVal::Method(_)));
  });
}
