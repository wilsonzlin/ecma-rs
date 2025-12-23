use super::body::BodyChecker;
use super::pat::check_pattern;
use super::stmt::check_stmt;
use crate::diagnostic::Diagnostic;
use crate::types::Type;
use crate::types::TypeId;
use bumpalo::collections::Vec as BumpVec;
use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::class_or_object::ClassOrObjVal;
use parse_js::ast::class_or_object::ObjMemberType;
use parse_js::ast::expr::lit::LitArrElem;
use parse_js::ast::expr::lit::LitArrExpr;
use parse_js::ast::expr::lit::LitObjExpr;
use parse_js::ast::expr::lit::LitTemplatePart;
use parse_js::ast::expr::BinaryExpr;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::expr::TaggedTemplateExpr;
use parse_js::ast::expr::UnaryExpr;
use parse_js::ast::expr::UnaryPostfixExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeEntityName;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::ast::type_expr::TypeLiteral;
use parse_js::operator::OperatorName;

pub(crate) fn check_expr(
  ctx: &mut BodyChecker<'_>,
  expr: &Node<Expr>,
  expected: Option<TypeId>,
) -> TypeId {
  let expr_id = ctx.assign_expr_id(expr);
  let ty = match expr.stx.as_ref() {
    Expr::LitNum(num) => ctx.store.literal_number(num.stx.value.to_string()),
    Expr::LitStr(str_) => ctx.store.literal_string(&str_.stx.value),
    Expr::LitBool(b) => ctx.store.literal_bool(b.stx.value),
    Expr::LitNull(_) => ctx.store.null(),
    Expr::LitRegex(_) => ctx.store.string(),
    Expr::LitBigInt(_) => ctx.store.number(),
    Expr::LitTemplate(template) => {
      for part in &template.stx.parts {
        if let LitTemplatePart::Substitution(sub) = part {
          check_expr(ctx, sub, None);
        }
      }
      ctx.store.string()
    }
    Expr::LitArr(arr) => check_array_literal(ctx, arr),
    Expr::LitObj(obj) => check_object_literal(ctx, obj),
    Expr::Id(id) => check_identifier(ctx, id),
    Expr::Member(member) => check_member(ctx, member),
    Expr::ComputedMember(member) => {
      let object_ty = check_expr(ctx, &member.stx.object, None);
      let _ = check_expr(ctx, &member.stx.member, None);
      match ctx.store.get(object_ty) {
        Type::Array(elem) => *elem,
        Type::Object(props) => ctx.store.union(props.values().copied().collect::<Vec<_>>()),
        _ => ctx.store.unknown(),
      }
    }
    Expr::Call(call) => check_call(ctx, call, false),
    Expr::TaggedTemplate(tagged) => check_tagged_template(ctx, tagged),
    Expr::Unary(unary) => check_unary(ctx, unary),
    Expr::UnaryPostfix(unary) => check_unary_postfix(ctx, unary),
    Expr::Binary(binary) => check_binary(ctx, binary),
    Expr::Cond(cond) => {
      check_expr(ctx, &cond.stx.test, Some(ctx.store.boolean()));
      let cons = check_expr(ctx, &cond.stx.consequent, expected);
      let alt = check_expr(ctx, &cond.stx.alternate, expected);
      ctx.store.union(vec![cons, alt])
    }
    Expr::Func(func_expr) => check_function(ctx, &func_expr.stx.func, expected),
    Expr::ArrowFunc(arrow) => check_function(ctx, &arrow.stx.func, expected),
    Expr::This(_) | Expr::Super(_) | Expr::ImportMeta(_) => ctx.store.unknown(),
    Expr::TypeAssertion(assertion) => {
      let asserted = assertion
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| type_from_type_expr(ctx, ann))
        .unwrap_or_else(|| check_expr(ctx, assertion.stx.expression.as_ref(), None));
      let _ = check_expr(ctx, assertion.stx.expression.as_ref(), Some(asserted));
      asserted
    }
    Expr::NonNullAssertion(assertion) => {
      check_expr(ctx, assertion.stx.expression.as_ref(), expected)
    }
    Expr::SatisfiesExpr(satisfies) => {
      let target = type_from_type_expr(ctx, &satisfies.stx.type_annotation);
      let expr_ty = check_expr(ctx, satisfies.stx.expression.as_ref(), Some(target));
      expr_ty
    }
    Expr::NewTarget(_) => ctx.store.unknown(),
    _ => ctx.store.unknown(),
  };

  if let Some(slot) = ctx.expr_types.get_mut(expr_id.index()) {
    *slot = ty;
  }

  if let Some(expected) = expected {
    if ctx.store.is_assignable(ty, expected) {
      return expected;
    }
  }

  ctx.store.widen(ty)
}

fn check_identifier(ctx: &mut BodyChecker<'_>, id: &Node<IdExpr>) -> TypeId {
  if let Some(ty) = ctx.resolve(&id.stx.name) {
    return ty;
  }
  ctx.diagnostics.push(Diagnostic::new(
    "UNKNOWN_IDENTIFIER",
    format!("Unknown identifier `{}`", id.stx.name),
    id.loc,
  ));
  ctx.store.unknown()
}

fn check_member(ctx: &mut BodyChecker<'_>, member: &Node<MemberExpr>) -> TypeId {
  let obj_ty = check_expr(ctx, &member.stx.left, None);
  match ctx.store.get(obj_ty) {
    Type::Object(props) => props
      .get(&member.stx.right)
      .copied()
      .unwrap_or_else(|| ctx.store.unknown()),
    _ => ctx.store.unknown(),
  }
}

fn check_tagged_template(ctx: &mut BodyChecker<'_>, tagged: &Node<TaggedTemplateExpr>) -> TypeId {
  let _ = check_expr(ctx, &tagged.stx.function, None);
  for part in &tagged.stx.parts {
    if let LitTemplatePart::Substitution(expr) = part {
      check_expr(ctx, expr, None);
    }
  }
  ctx.store.string()
}

fn check_call(ctx: &mut BodyChecker<'_>, call: &Node<CallExpr>, construct: bool) -> TypeId {
  let callee_ty = check_expr(ctx, &call.stx.callee, None);
  let mut collected_args = Vec::new();
  for arg in &call.stx.arguments {
    let arg_ty = check_expr(ctx, &arg.stx.value, None);
    collected_args.push(arg_ty);
  }
  let arg_types = BumpVec::from_iter_in(collected_args.iter().copied(), &ctx.arena);

  if let Type::Function(func) = ctx.store.get(callee_ty).clone() {
    for (idx, param_ty) in func.params.iter().enumerate() {
      if let Some(arg_ty) = arg_types.get(idx) {
        if !ctx.store.is_assignable(*arg_ty, *param_ty) {
          let arg_span = call
            .stx
            .arguments
            .get(idx)
            .map(|a| a.loc)
            .unwrap_or(call.loc);
          ctx.diagnostics.push(Diagnostic::new(
            "TYPE_MISMATCH",
            format!("argument {} is not assignable to parameter", idx + 1),
            arg_span,
          ));
        }
      } else {
        ctx.diagnostics.push(Diagnostic::new(
          "TYPE_MISMATCH",
          format!("expected {} arguments", func.params.len()),
          call.loc,
        ));
      }
    }
    func.return_type
  } else {
    ctx.diagnostics.push(Diagnostic::new(
      if construct {
        "NOT_CONSTRUCTABLE"
      } else {
        "NOT_CALLABLE"
      },
      "Callee is not callable",
      call.loc,
    ));
    ctx.store.unknown()
  }
}

fn check_unary(ctx: &mut BodyChecker<'_>, unary: &Node<UnaryExpr>) -> TypeId {
  let arg_ty = check_expr(ctx, &unary.stx.argument, None);
  match unary.stx.operator {
    OperatorName::LogicalNot => ctx.store.boolean(),
    OperatorName::UnaryPlus | OperatorName::UnaryNegation => ctx.store.number(),
    OperatorName::Typeof => ctx.store.string(),
    OperatorName::Void => ctx.store.void(),
    OperatorName::Delete => ctx.store.boolean(),
    _ => arg_ty,
  }
}

fn check_unary_postfix(ctx: &mut BodyChecker<'_>, unary: &Node<UnaryPostfixExpr>) -> TypeId {
  let arg_ty = check_expr(ctx, &unary.stx.argument, None);
  match unary.stx.operator {
    OperatorName::PostfixIncrement | OperatorName::PostfixDecrement => ctx.store.number(),
    _ => arg_ty,
  }
}

fn check_binary(ctx: &mut BodyChecker<'_>, binary: &Node<BinaryExpr>) -> TypeId {
  if binary.stx.operator.is_assignment() {
    let right_ty = check_expr(ctx, &binary.stx.right, None);
    match binary.stx.left.stx.as_ref() {
      Expr::Id(id) => {
        if let Some(existing) = ctx.resolve(&id.stx.name) {
          if !ctx.store.is_assignable(right_ty, existing) {
            ctx.diagnostics.push(Diagnostic::new(
              "TYPE_MISMATCH",
              "assignment is not compatible with target",
              binary.stx.left.loc,
            ));
          }
        } else {
          ctx.define(&id.stx.name, right_ty);
        }
      }
      Expr::Member(member) => {
        let _ = check_expr(ctx, &member.stx.left, None);
      }
      Expr::ComputedMember(member) => {
        let _ = check_expr(ctx, &member.stx.object, None);
        let _ = check_expr(ctx, &member.stx.member, None);
      }
      _ => {
        check_expr(ctx, &binary.stx.left, Some(right_ty));
      }
    }
    return right_ty;
  }

  let left_ty = check_expr(ctx, &binary.stx.left, None);
  let right_ty = check_expr(ctx, &binary.stx.right, None);
  match binary.stx.operator {
    OperatorName::Addition => {
      if ctx.store.is_assignable(left_ty, ctx.store.string())
        || ctx.store.is_assignable(right_ty, ctx.store.string())
      {
        ctx.store.string()
      } else {
        ctx.store.number()
      }
    }
    OperatorName::LogicalAnd | OperatorName::LogicalOr | OperatorName::NullishCoalescing => {
      ctx.store.union(vec![left_ty, right_ty])
    }
    OperatorName::Equality
    | OperatorName::Inequality
    | OperatorName::StrictEquality
    | OperatorName::StrictInequality
    | OperatorName::GreaterThan
    | OperatorName::GreaterThanOrEqual
    | OperatorName::LessThan
    | OperatorName::LessThanOrEqual
    | OperatorName::In
    | OperatorName::Instanceof => ctx.store.boolean(),
    OperatorName::BitwiseAnd
    | OperatorName::BitwiseOr
    | OperatorName::BitwiseXor
    | OperatorName::BitwiseLeftShift
    | OperatorName::BitwiseRightShift
    | OperatorName::BitwiseUnsignedRightShift
    | OperatorName::Subtraction
    | OperatorName::Multiplication
    | OperatorName::Division
    | OperatorName::Remainder
    | OperatorName::Exponentiation => ctx.store.number(),
    _ => ctx.store.union(vec![left_ty, right_ty]),
  }
}

pub(crate) fn check_function(
  ctx: &mut BodyChecker<'_>,
  func: &Node<Func>,
  expected: Option<TypeId>,
) -> TypeId {
  let mut param_types = Vec::new();
  let expected_sig = expected.and_then(|ty| match ctx.store.get(ty).clone() {
    Type::Function(f) => Some(f),
    _ => None,
  });
  let mut expected_return = expected_sig.as_ref().map(|f| f.return_type);

  if let Some(sig) = &expected_sig {
    for (idx, param) in func.stx.parameters.iter().enumerate() {
      let param_ty = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| type_from_type_expr(ctx, ann))
        .or_else(|| sig.params.get(idx).copied())
        .unwrap_or_else(|| ctx.store.unknown());
      param_types.push(param_ty);
    }
    if expected_return.is_none() {
      expected_return = Some(sig.return_type);
    }
  }

  if param_types.len() < func.stx.parameters.len() {
    for param in param_types.len()..func.stx.parameters.len() {
      let annotation = func.stx.parameters[param]
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| type_from_type_expr(ctx, ann))
        .unwrap_or_else(|| ctx.store.unknown());
      param_types.push(annotation);
    }
  }

  let ret_annotation = func
    .stx
    .return_type
    .as_ref()
    .map(|ann| type_from_type_expr(ctx, ann));
  if expected_return.is_none() {
    expected_return = ret_annotation;
  }

  ctx.push_scope();
  for (param, ty) in func.stx.parameters.iter().zip(param_types.iter()) {
    check_pattern(ctx, &param.stx.pattern.stx.pat, *ty);
    if let Some(default) = &param.stx.default_value {
      check_expr(ctx, default, Some(*ty));
    }
  }

  let prev_expected_return = ctx.expected_return;
  let target_ret = expected_return
    .or(ret_annotation)
    .or(Some(ctx.store.unknown()));
  ctx.expected_return = target_ret;

  let mut actual_return = target_ret.unwrap_or_else(|| ctx.store.void());
  match func.stx.body.as_ref() {
    Some(FuncBody::Block(stmts)) => {
      for stmt in stmts {
        check_stmt(ctx, stmt);
      }
    }
    Some(FuncBody::Expression(expr)) => {
      actual_return = check_expr(ctx, expr, ctx.expected_return);
    }
    None => {}
  }

  if let Some(expected_ret) = target_ret {
    if func.stx.body.is_some() && !ctx.store.is_assignable(actual_return, expected_ret) {
      ctx.diagnostics.push(Diagnostic::new(
        "TYPE_MISMATCH",
        "function return type not assignable to annotation",
        func.loc,
      ));
    }
  }

  ctx.expected_return = prev_expected_return;
  ctx.pop_scope();

  let ret_ty = target_ret.unwrap_or(actual_return);
  ctx.store.function(param_types, ret_ty, true)
}

pub(crate) fn type_from_type_expr(ctx: &mut BodyChecker<'_>, ty: &Node<TypeExpr>) -> TypeId {
  match ty.stx.as_ref() {
    TypeExpr::Any(_) => ctx.store.any(),
    TypeExpr::Unknown(_) => ctx.store.unknown(),
    TypeExpr::Never(_) => ctx.store.never(),
    TypeExpr::Void(_) => ctx.store.void(),
    TypeExpr::String(_) => ctx.store.string(),
    TypeExpr::Number(_) => ctx.store.number(),
    TypeExpr::Boolean(_) => ctx.store.boolean(),
    TypeExpr::Null(_) => ctx.store.null(),
    TypeExpr::Undefined(_) => ctx.store.undefined(),
    TypeExpr::LiteralType(lit) => match lit.stx.as_ref() {
      TypeLiteral::Boolean(b) => ctx.store.literal_bool(*b),
      TypeLiteral::Number(n) => ctx.store.literal_number(n.clone()),
      TypeLiteral::String(s) => ctx.store.literal_string(s.clone()),
      _ => ctx.store.unknown(),
    },
    TypeExpr::ArrayType(arr) => {
      let elem = type_from_type_expr(ctx, &arr.stx.element_type);
      ctx.store.array(elem)
    }
    TypeExpr::UnionType(union) => {
      let members = union
        .stx
        .types
        .iter()
        .map(|t| type_from_type_expr(ctx, t))
        .collect();
      ctx.store.union(members)
    }
    TypeExpr::ParenthesizedType(inner) => type_from_type_expr(ctx, &inner.stx.type_expr),
    TypeExpr::FunctionType(func) => {
      let params = func
        .stx
        .parameters
        .iter()
        .map(|p| type_from_type_expr(ctx, &p.stx.type_expr))
        .collect();
      let ret = type_from_type_expr(ctx, &func.stx.return_type);
      ctx.store.function(params, ret, false)
    }
    TypeExpr::TypeReference(reference) => {
      if let TypeEntityName::Identifier(name) = &reference.stx.name {
        if name == "Array" {
          if let Some(args) = &reference.stx.type_arguments {
            if let Some(first) = args.first() {
              let inner = type_from_type_expr(ctx, first);
              return ctx.store.array(inner);
            }
          }
        }
      }
      ctx.store.unknown()
    }
    _ => ctx.store.unknown(),
  }
}

fn check_array_literal(ctx: &mut BodyChecker<'_>, arr: &Node<LitArrExpr>) -> TypeId {
  let mut element_types = Vec::new();
  for elem in &arr.stx.elements {
    match elem {
      LitArrElem::Single(expr) => element_types.push(check_expr(ctx, expr, None)),
      LitArrElem::Rest(expr) => element_types.push(check_expr(ctx, expr, None)),
      LitArrElem::Empty => {}
    }
  }
  let element_ty = if element_types.is_empty() {
    ctx.store.unknown()
  } else {
    ctx.store.union(element_types)
  };
  ctx.store.array(element_ty)
}

fn check_object_literal(ctx: &mut BodyChecker<'_>, obj: &Node<LitObjExpr>) -> TypeId {
  let mut props = std::collections::BTreeMap::new();
  for member in &obj.stx.members {
    match &member.stx.typ {
      ObjMemberType::Valued { key, val } => {
        let name = match key {
          ClassOrObjKey::Direct(direct) => direct.stx.key.clone(),
          ClassOrObjKey::Computed(expr) => {
            check_expr(ctx, expr, None);
            continue;
          }
        };
        let value_ty = match val {
          ClassOrObjVal::Prop(Some(expr)) => check_expr(ctx, expr, None),
          ClassOrObjVal::Getter(getter) => check_function(ctx, &getter.stx.func, None),
          ClassOrObjVal::Setter(setter) => check_function(ctx, &setter.stx.func, None),
          ClassOrObjVal::Method(method) => check_function(ctx, &method.stx.func, None),
          _ => ctx.store.unknown(),
        };
        props.insert(name, value_ty);
      }
      ObjMemberType::Shorthand { id } => {
        let name = id.stx.name.clone();
        let ty = check_identifier(ctx, id);
        props.insert(name, ty);
      }
      ObjMemberType::Rest { val } => {
        let rest_ty = check_expr(ctx, val, None);
        if let Type::Object(rest_props) = ctx.store.get(rest_ty) {
          for (k, v) in rest_props.iter() {
            props.insert(k.clone(), *v);
          }
        }
      }
    }
  }
  ctx.store.object(props)
}
