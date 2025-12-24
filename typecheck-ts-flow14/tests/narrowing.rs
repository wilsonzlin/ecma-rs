use std::collections::BTreeMap;
use typecheck_ts_flow14::check_body;
use typecheck_ts_flow14::hir::*;
use typecheck_ts_flow14::types::ObjectType;
use typecheck_ts_flow14::types::Type;

fn make_object(class: Option<&str>, props: &[(&str, Type)]) -> Type {
  let mut map = BTreeMap::new();
  for (k, v) in props {
    map.insert((*k).to_string(), v.clone());
  }
  Type::object(ObjectType::new(class.map(|c| c.to_string()), map))
}

#[test]
fn truthiness_narrows_nullable() {
  let mut body = Body::new();
  let x = body.add_var(
    "x",
    Type::string()
      .union(&Type::null())
      .union(&Type::undefined()),
  );

  let cond = body.alloc_expr(Expr::Var(x));
  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));

  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));
  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], Type::string());
  assert_eq!(
    result.expr_types[else_expr.idx()],
    Type::null().union(&Type::undefined())
  );
}

#[test]
fn typeof_narrows_branches() {
  let mut body = Body::new();
  let x = body.add_var("x", Type::string().union(&Type::number()));
  let x_expr = body.alloc_expr(Expr::Var(x));
  let typeof_x = body.alloc_expr(Expr::Unary(UnaryOp::Typeof, x_expr));
  let string_tag = body.alloc_expr(Expr::Literal(Literal::String("string".into())));
  let cond = body.alloc_expr(Expr::Binary(BinaryOp::StrictEquals, typeof_x, string_tag));

  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));

  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));
  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], Type::string());
  assert_eq!(result.expr_types[else_expr.idx()], Type::number());
}

#[test]
fn instanceof_narrows() {
  let mut body = Body::new();
  let a_type = make_object(Some("A"), &[]);
  let b_type = make_object(Some("B"), &[]);
  let x = body.add_var("x", a_type.clone().union(&b_type));

  let x_expr = body.alloc_expr(Expr::Var(x));
  let class_literal = body.alloc_expr(Expr::Literal(Literal::String("A".into())));
  let cond = body.alloc_expr(Expr::Binary(BinaryOp::InstanceOf, x_expr, class_literal));

  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));

  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));
  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], a_type);
  assert_eq!(result.expr_types[else_expr.idx()], b_type);
}

#[test]
fn discriminant_property_narrows() {
  let foo = make_object(
    None,
    &[("kind", Type::string_literal("foo")), ("a", Type::number())],
  );
  let bar = make_object(
    None,
    &[("kind", Type::string_literal("bar")), ("b", Type::string())],
  );

  let mut body = Body::new();
  let x = body.add_var("x", foo.clone().union(&bar));

  let obj_expr = body.alloc_expr(Expr::Var(x));
  let prop_expr = body.alloc_expr(Expr::Property {
    obj: obj_expr,
    name: "kind".into(),
  });
  let literal_expr = body.alloc_expr(Expr::Literal(Literal::String("foo".into())));
  let cond = body.alloc_expr(Expr::Binary(
    BinaryOp::StrictEquals,
    prop_expr,
    literal_expr,
  ));

  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));

  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));
  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], foo);
  assert_eq!(result.expr_types[else_expr.idx()], bar);
}

#[test]
fn in_operator_narrows() {
  let foo = make_object(None, &[("foo", Type::number())]);
  let bar = make_object(None, &[("bar", Type::string())]);
  let mut body = Body::new();
  let x = body.add_var("x", foo.clone().union(&bar));

  let obj_expr = body.alloc_expr(Expr::Var(x));
  let cond = body.alloc_expr(Expr::In {
    property: "foo".into(),
    obj: obj_expr,
  });
  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));

  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));
  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], foo);
  assert_eq!(result.expr_types[else_expr.idx()], bar);
}

#[test]
fn user_defined_type_guard() {
  let foo = make_object(None, &[("foo", Type::number())]);
  let bar = make_object(None, &[("bar", Type::string())]);
  let mut body = Body::new();
  let x = body.add_var("x", foo.clone().union(&bar));

  let fn_id = body.add_function(
    "isFoo",
    x,
    FunctionReturn::TypeGuard {
      narrows: x,
      to: foo.clone(),
    },
  );

  let arg_expr = body.alloc_expr(Expr::Var(x));
  let cond = body.alloc_expr(Expr::Call {
    callee: fn_id,
    args: vec![arg_expr],
  });
  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));
  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));

  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], foo);
  assert_eq!(result.expr_types[else_expr.idx()], bar);
}

#[test]
fn assertion_function_updates_environment() {
  let foo = make_object(None, &[("foo", Type::number())]);
  let bar = make_object(None, &[("bar", Type::string())]);
  let mut body = Body::new();
  let x = body.add_var("x", foo.clone().union(&bar));

  let assert_fn = body.add_function(
    "assertFoo",
    x,
    FunctionReturn::Asserts {
      narrows: x,
      to: foo.clone(),
    },
  );

  let arg_expr = body.alloc_expr(Expr::Var(x));
  let call = body.alloc_expr(Expr::Call {
    callee: assert_fn,
    args: vec![arg_expr],
  });

  let after_expr = body.alloc_expr(Expr::Var(x));
  let call_stmt = body.alloc_stmt(StmtKind::Expr(call));
  let after_stmt = body.alloc_stmt(StmtKind::Expr(after_expr));
  body.push_root(call_stmt);
  body.push_root(after_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[after_expr.idx()], foo);
}

#[test]
fn nested_boolean_and_ternary_are_respected() {
  let mut body = Body::new();
  let x = body.add_var("x", Type::string().union(&Type::null()));

  let typeof_input = body.alloc_expr(Expr::Var(x));
  let typeof_target = body.alloc_expr(Expr::Unary(UnaryOp::Typeof, typeof_input));
  let string_literal = body.alloc_expr(Expr::Literal(Literal::String("string".into())));
  let typeof_x = body.alloc_expr(Expr::Binary(
    BinaryOp::StrictEquals,
    typeof_target,
    string_literal,
  ));

  let when_true_expr = body.alloc_expr(Expr::Var(x));
  let when_false_expr = body.alloc_expr(Expr::Literal(Literal::Boolean(false)));
  let ternary = body.alloc_expr(Expr::Conditional {
    cond: typeof_x,
    when_true: when_true_expr,
    when_false: when_false_expr,
  });

  let right_and_expr = body.alloc_expr(Expr::Var(x));
  let cond = body.alloc_expr(Expr::Logical(LogicalOp::And, ternary, right_and_expr));

  let then_expr = body.alloc_expr(Expr::Var(x));
  let else_expr = body.alloc_expr(Expr::Var(x));
  let then_stmt = body.alloc_stmt(StmtKind::Expr(then_expr));
  let else_stmt = body.alloc_stmt(StmtKind::Expr(else_expr));

  let if_stmt = body.alloc_stmt(StmtKind::If {
    cond,
    then_branch: vec![then_stmt],
    else_branch: vec![else_stmt],
  });
  body.push_root(if_stmt);

  let result = check_body(&body);
  assert_eq!(result.expr_types[then_expr.idx()], Type::string());
  assert_eq!(result.expr_types[else_expr.idx()], Type::null());
}
