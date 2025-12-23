use typecheck_ts_const18::check::FreshContext;
use typecheck_ts_const18::check::InferOptions;
use typecheck_ts_const18::check::VarKind;
use typecheck_ts_const18::diagnostic::DiagnosticKind;
use typecheck_ts_const18::Checker;
use typecheck_ts_const18::Expr;
use typecheck_ts_const18::IndexSignature;
use typecheck_ts_const18::ObjectField;
use typecheck_ts_const18::ObjectType;
use typecheck_ts_const18::Property;
use typecheck_ts_const18::Span;
use typecheck_ts_const18::TupleType;
use typecheck_ts_const18::Type;

fn object_type(props: Vec<(&str, Type)>) -> Type {
  Type::Object(Box::new(ObjectType {
    properties: props
      .into_iter()
      .map(|(name, typ)| Property {
        name: name.to_string(),
        typ,
        optional: false,
        readonly: false,
      })
      .collect(),
    index_signature: None,
  }))
}

fn object_with_index(props: Vec<(&str, Type)>, value: Type) -> Type {
  Type::Object(Box::new(ObjectType {
    properties: props
      .into_iter()
      .map(|(name, typ)| Property {
        name: name.to_string(),
        typ,
        optional: false,
        readonly: false,
      })
      .collect(),
    index_signature: Some(Box::new(IndexSignature {
      value: Box::new(value),
    })),
  }))
}

fn field(name: &str, expr: Expr) -> ObjectField {
  ObjectField::new(name, expr)
}

#[test]
fn const_preserves_literal_primitive() {
  let mut checker = Checker::new();
  let ty = checker.declare("x", VarKind::Const, Expr::Number(1.0), None);
  assert_eq!(ty, Type::LiteralNumber(1));
  assert!(checker.diagnostics.is_empty());
}

#[test]
fn let_widens_literal() {
  let mut checker = Checker::new();
  let ty = checker.declare("x", VarKind::Let, Expr::String("hi".into()), None);
  assert_eq!(ty, Type::String);
}

#[test]
fn contextual_typing_prevents_widening() {
  let mut checker = Checker::new();
  let contextual = Type::union(vec![
    Type::LiteralString("a".into()),
    Type::LiteralString("b".into()),
  ]);
  let typed = checker.infer_expr(
    &Expr::String("a".into()),
    Some(&contextual),
    InferOptions::for_binding(VarKind::Let),
    FreshContext::Direct,
  );
  assert_eq!(typed.ty, Type::LiteralString("a".into()));
}

#[test]
fn const_object_properties_keep_literals() {
  let mut checker = Checker::new();
  let ty = checker.declare(
    "obj",
    VarKind::Const,
    Expr::Object(vec![field("a", Expr::Number(1.0))]),
    None,
  );
  if let Type::Object(obj) = ty {
    assert_eq!(obj.properties.len(), 1);
    assert_eq!(obj.properties[0].typ, Type::LiteralNumber(1));
  } else {
    panic!("expected object type");
  }
}

#[test]
fn let_object_properties_widen() {
  let mut checker = Checker::new();
  let ty = checker.declare(
    "obj",
    VarKind::Let,
    Expr::Object(vec![field("a", Expr::Number(1.0))]),
    None,
  );
  if let Type::Object(obj) = ty {
    assert_eq!(obj.properties[0].typ, Type::Number);
  } else {
    panic!("expected object type");
  }
}

#[test]
fn const_assertion_on_array_creates_readonly_tuple() {
  let mut checker = Checker::new();
  let expr = Expr::ConstAssertion(Box::new(Expr::Array(vec![
    Expr::Number(1.0),
    Expr::Number(2.0),
  ])));
  let typed = checker.infer_expr(
    &expr,
    None,
    InferOptions::for_binding(VarKind::Const),
    FreshContext::Direct,
  );
  assert_eq!(
    typed.ty,
    Type::Tuple(TupleType {
      elements: vec![Type::LiteralNumber(1), Type::LiteralNumber(2)],
      readonly: true,
    })
  );
}

#[test]
fn const_assertion_on_object_is_deep_literal_readonly() {
  let mut checker = Checker::new();
  let expr = Expr::ConstAssertion(Box::new(Expr::Object(vec![field(
    "outer",
    Expr::Object(vec![field("inner", Expr::String("v".into()))]),
  )])));
  let typed = checker.infer_expr(
    &expr,
    None,
    InferOptions::for_binding(VarKind::Const),
    FreshContext::Direct,
  );
  if let Type::Object(obj) = typed.ty {
    assert_eq!(obj.properties.len(), 1);
    let outer = &obj.properties[0];
    assert!(outer.readonly);
    if let Type::Object(inner_obj) = &outer.typ {
      let inner = &inner_obj.properties[0];
      assert!(inner.readonly);
      assert_eq!(inner.typ, Type::LiteralString("v".into()));
    } else {
      panic!("expected nested object");
    }
  } else {
    panic!("expected object type");
  }
}

#[test]
fn const_assertion_misuse_emits_diagnostic() {
  let mut checker = Checker::new();
  let expr = Expr::ConstAssertion(Box::new(Expr::Identifier("x".into())));
  checker.infer_expr(
    &expr,
    None,
    InferOptions::for_binding(VarKind::Const),
    FreshContext::Direct,
  );
  assert!(checker
    .diagnostics
    .iter()
    .any(|d| matches!(d.kind, DiagnosticKind::ConstAssertionNotLiteral)));
}

#[test]
fn excess_property_error_with_span() {
  let mut checker = Checker::new();
  let target = object_type(vec![("foo", Type::Number)]);
  let expr = Expr::Object(vec![
    field("foo", Expr::Number(1.0)),
    field("bar", Expr::Number(2.0)).with_span(Span::new(4, 7)),
  ]);
  checker.declare("val", VarKind::Let, expr, Some(target));
  assert_eq!(checker.diagnostics.len(), 1);
  let diag = &checker.diagnostics[0];
  assert!(matches!(
      diag.kind,
      DiagnosticKind::ExcessProperty { ref property } if property == "bar"
  ));
  assert_eq!(diag.span, Some(Span::new(4, 7)));
}

#[test]
fn index_signature_suppresses_excess_property_error() {
  let mut checker = Checker::new();
  let target = object_with_index(vec![], Type::Number);
  let expr = Expr::Object(vec![
    field("foo", Expr::Number(1.0)),
    field("bar", Expr::Number(2.0)),
  ]);
  checker.declare("val", VarKind::Const, expr, Some(target));
  assert!(checker.diagnostics.is_empty());
}

#[test]
fn non_fresh_object_through_variable_has_no_excess_check() {
  let mut checker = Checker::new();
  checker.declare(
    "tmp",
    VarKind::Const,
    Expr::Object(vec![
      field("foo", Expr::Number(1.0)),
      field("bar", Expr::Number(2.0)),
    ]),
    None,
  );
  let target = object_type(vec![("foo", Type::Number)]);
  let tmp_expr = checker.infer_expr(
    &Expr::Identifier("tmp".into()),
    Some(&target),
    InferOptions::for_binding(VarKind::Let),
    FreshContext::Direct,
  );
  checker.check_assignable(&tmp_expr, &target);
  assert!(checker.diagnostics.is_empty());
}

#[test]
fn type_assertion_suppresses_excess_property_check() {
  let mut checker = Checker::new();
  let target = object_type(vec![("foo", Type::Number)]);
  let expr = Expr::TypeAssertion {
    expr: Box::new(Expr::Object(vec![
      field("foo", Expr::Number(1.0)),
      field("bar", Expr::Number(2.0)),
    ])),
    typ: target.clone(),
  };
  let typed = checker.infer_expr(
    &expr,
    Some(&target),
    InferOptions::for_binding(VarKind::Let),
    FreshContext::Direct,
  );
  checker.check_assignable(&typed, &target);
  assert!(checker.diagnostics.is_empty());
}

#[test]
fn call_argument_runs_excess_property_check() {
  let mut checker = Checker::new();
  let target = object_type(vec![("foo", Type::Number)]);
  checker.call(&[target], vec![Expr::Object(vec![
    field("foo", Expr::Number(1.0)),
    field("extra", Expr::Boolean(true)),
  ])]);
  assert_eq!(checker.diagnostics.len(), 1);
  assert!(matches!(
      checker.diagnostics[0].kind,
      DiagnosticKind::ExcessProperty { ref property } if property == "extra"
  ));
}

#[test]
fn empty_target_type_has_no_excess_property_error() {
  let mut checker = Checker::new();
  let target = object_type(vec![]);
  checker.declare(
    "val",
    VarKind::Let,
    Expr::Object(vec![field("foo", Expr::Number(1.0))]),
    Some(target),
  );
  assert!(checker.diagnostics.is_empty());
}

#[test]
fn satisfies_preserves_expression_type_but_checks_assignability() {
  let mut checker = Checker::new();
  let target = object_type(vec![("foo", Type::Number)]);
  let expr = Expr::Satisfies {
    expr: Box::new(Expr::Object(vec![
      field("foo", Expr::Number(1.0)),
      field("bar", Expr::Number(2.0)),
    ])),
    typ: target.clone(),
  };
  let typed = checker.infer_expr(
    &expr,
    None,
    InferOptions::for_binding(VarKind::Const),
    FreshContext::Direct,
  );
  if let Type::Object(obj) = typed.ty {
    assert_eq!(obj.properties.len(), 2);
  } else {
    panic!("expected object type");
  }
  assert_eq!(checker.diagnostics.len(), 1);
  assert!(matches!(
      checker.diagnostics[0].kind,
      DiagnosticKind::ExcessProperty { ref property } if property == "bar"
  ));
}

#[test]
fn diagnostics_follow_property_insertion_order() {
  let mut checker = Checker::new();
  let target = object_type(vec![("keep", Type::Number)]);
  checker.declare(
    "val",
    VarKind::Let,
    Expr::Object(vec![
      field("b", Expr::Number(1.0)),
      field("a", Expr::Number(2.0)),
      field("keep", Expr::Number(3.0)),
    ]),
    Some(target),
  );
  let props: Vec<String> = checker
    .diagnostics
    .iter()
    .filter_map(|d| match &d.kind {
      DiagnosticKind::ExcessProperty { property } => Some(property.clone()),
      _ => None,
    })
    .collect();
  assert_eq!(props, vec!["b".to_string(), "a".to_string()]);
}

#[test]
fn contextual_property_typing_prevents_widening() {
  let mut checker = Checker::new();
  let contextual = object_type(vec![(
    "kind",
    Type::union(vec![
      Type::LiteralString("one".into()),
      Type::LiteralString("two".into()),
    ]),
  )]);
  let typed = checker.infer_expr(
    &Expr::Object(vec![field("kind", Expr::String("one".into()))]),
    Some(&contextual),
    InferOptions::for_binding(VarKind::Let),
    FreshContext::Direct,
  );
  if let Type::Object(obj) = typed.ty {
    assert_eq!(obj.properties[0].typ, Type::LiteralString("one".into()));
  } else {
    panic!("expected object type");
  }
}

#[test]
fn contextual_tuple_typed_array_preserves_element_positions() {
  let mut checker = Checker::new();
  let target = Type::Tuple(TupleType {
    elements: vec![Type::LiteralNumber(1), Type::LiteralString("a".into())],
    readonly: false,
  });
  let typed = checker.infer_expr(
    &Expr::Array(vec![Expr::Number(1.0), Expr::String("a".into())]),
    Some(&target),
    InferOptions::for_binding(VarKind::Let),
    FreshContext::Direct,
  );
  assert_eq!(typed.ty, target);
  assert!(checker.diagnostics.is_empty());
}
