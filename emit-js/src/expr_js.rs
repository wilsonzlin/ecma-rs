use crate::emitter::{EmitError, EmitErrorKind, EmitResult, Emitter};
use crate::escape::{cooked_template_segment, emit_template_literal_segment};
use crate::precedence::starts_with_optional_chaining;
use crate::stmt::{emit_class_like, emit_decorators};
use crate::ts_type::{emit_ts_type, emit_type_expr, emit_type_parameters};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType};
use parse_js::ast::expr::lit::{
  LitArrElem, LitArrExpr, LitObjExpr, LitTemplateExpr, LitTemplatePart,
};
use parse_js::ast::expr::pat::{ArrPat, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::expr::*;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{Accessibility, ParamDecl, PatDecl};
use parse_js::ast::type_expr::{TypeExpr, TypeParameter};
use parse_js::operator::{Associativity, OperatorName, OPERATORS};
use parse_js::token::TT;

const PRIMARY_PRECEDENCE: u8 = 19;
const CALL_MEMBER_PRECEDENCE: u8 = 18;
const POSTFIX_PRECEDENCE: u8 = 17;
const ARROW_PRECEDENCE: u8 = 3;

/// Context for expression emission. Currently unused but kept to allow
/// statement-start callers to request safer forms in the future.
#[derive(Clone, Copy)]
pub enum ExprCtx {
  Default,
  /// Expression is in statement position (e.g. `foo;`).
  Stmt,
  /// Expression appears as the RHS of `export default`.
  ExportDefault,
}

pub fn emit_expr(em: &mut Emitter, expr: &Node<Expr>, ctx: ExprCtx) -> EmitResult {
  match emit_expr_with_min_prec(em, expr, 1, ctx) {
    Err(EmitError {
      kind: EmitErrorKind::Unsupported(_),
      ..
    }) => emit_expr_via_fmt(em, expr),
    other => other,
  }
}

fn emit_expr_with_min_prec(
  em: &mut Emitter,
  expr: &Node<Expr>,
  min_prec: u8,
  ctx: ExprCtx,
) -> EmitResult {
  let prec = expr_precedence(expr)?;
  let needs_paren = prec < min_prec;

  if needs_paren {
    em.write_punct("(");
  }
  emit_expr_no_parens(em, expr, ctx)?;
  if needs_paren {
    em.write_punct(")");
  }

  Ok(())
}

fn expr_precedence(expr: &Node<Expr>) -> Result<u8, EmitError> {
  match expr.stx.as_ref() {
    Expr::Id(_) | Expr::This(_) | Expr::Super(_) | Expr::NewTarget(_) | Expr::ImportMeta(_) => {
      Ok(PRIMARY_PRECEDENCE)
    }
    Expr::LitNum(_)
    | Expr::LitBool(_)
    | Expr::LitNull(_)
    | Expr::LitBigInt(_)
    | Expr::LitStr(_)
    | Expr::LitRegex(_)
    | Expr::LitArr(_)
    | Expr::LitObj(_)
    | Expr::LitTemplate(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::JsxElem(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::ArrPat(_) | Expr::IdPat(_) | Expr::ObjPat(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::Call(_) | Expr::Member(_) | Expr::ComputedMember(_) | Expr::Instantiation(_) => {
      Ok(CALL_MEMBER_PRECEDENCE)
    }
    Expr::Binary(binary) => Ok(
      OPERATORS
        .get(&binary.stx.operator)
        .map(|op| op.precedence)
        .ok_or_else(|| EmitError::unsupported("unknown operator"))?,
    ),
    Expr::Cond(_) => Ok(
      OPERATORS
        .get(&OperatorName::Conditional)
        .map(|op| op.precedence)
        .ok_or_else(|| EmitError::unsupported("unknown operator"))?,
    ),
    Expr::Unary(unary) => Ok(
      OPERATORS
        .get(&unary.stx.operator)
        .map(|op| op.precedence)
        .ok_or_else(|| EmitError::unsupported("unknown operator"))?,
    ),
    Expr::UnaryPostfix(postfix) => Ok(
      OPERATORS
        .get(&postfix.stx.operator)
        .map(|op| op.precedence)
        .ok_or_else(|| EmitError::unsupported("unknown operator"))?,
    ),
    Expr::NonNullAssertion(_) => Ok(CALL_MEMBER_PRECEDENCE),
    Expr::TypeAssertion(_) => Ok(crate::precedence::TYPE_ASSERTION_PRECEDENCE.value()),
    Expr::SatisfiesExpr(_) => Ok(crate::precedence::SATISFIES_PRECEDENCE.value()),
    Expr::ArrowFunc(_) => Ok(ARROW_PRECEDENCE),
    Expr::Func(_) | Expr::Class(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::Import(_) => Ok(CALL_MEMBER_PRECEDENCE),
    Expr::TaggedTemplate(_) => Ok(CALL_MEMBER_PRECEDENCE),
    _ => Err(EmitError::unsupported("expression kind not supported")),
  }
}

fn emit_expr_no_parens(em: &mut Emitter, expr: &Node<Expr>, ctx: ExprCtx) -> EmitResult {
  match expr.stx.as_ref() {
    Expr::Id(id) => em.write_identifier(&id.stx.name),
    Expr::This(_) => em.write_keyword("this"),
    Expr::Super(_) => em.write_keyword("super"),
    Expr::NewTarget(_) => em.write_str("new.target"),
    Expr::ImportMeta(_) => em.write_str("import.meta"),
    Expr::LitNum(num) => em.write_number(&num.stx.value.to_string()),
    Expr::LitBool(lit) => em.write_keyword(if lit.stx.value { "true" } else { "false" }),
    Expr::LitNull(_) => em.write_keyword("null"),
    Expr::LitBigInt(lit) => em.write_bigint_literal(&lit.stx.value),
    Expr::LitStr(lit) => emit_string_literal(em, &lit.stx.value),
    Expr::LitRegex(lit) => {
      let mut buf = Vec::new();
      crate::escape::emit_regex_literal(&mut buf, &lit.stx.value);
      em.write_str(std::str::from_utf8(&buf).expect("regex literal escape output is UTF-8"));
    }
    Expr::LitArr(arr) => emit_array_literal(em, arr)?,
    Expr::LitObj(obj) => emit_object_literal(em, obj)?,
    Expr::LitTemplate(template) => emit_template_literal(em, template)?,
    Expr::JsxElem(elem) => crate::jsx_emit::emit_jsx_elem(em, elem)?,
    Expr::ArrPat(arr) => emit_array_pattern(em, arr)?,
    Expr::IdPat(id) => emit_id_pat(em, id)?,
    Expr::ObjPat(obj) => emit_object_pattern(em, obj)?,
    Expr::Binary(binary) => emit_binary(em, binary, ctx)?,
    Expr::Cond(cond) => emit_conditional(em, cond, ctx)?,
    Expr::Call(call) => emit_call(em, call, ctx)?,
    Expr::Member(member) => emit_member(em, member, ctx)?,
    Expr::ComputedMember(member) => emit_computed_member(em, member, ctx)?,
    Expr::Instantiation(instantiation) => emit_instantiation_expr(em, instantiation, ctx)?,
    Expr::Unary(unary) => emit_unary(em, unary, ctx)?,
    Expr::UnaryPostfix(postfix) => emit_postfix(em, postfix, ctx)?,
    Expr::NonNullAssertion(non_null) => {
      emit_expr_with_min_prec(em, &non_null.stx.expression, CALL_MEMBER_PRECEDENCE, ctx)?;
      em.write_punct("!");
    }
    Expr::TypeAssertion(assertion) => emit_type_assertion(em, assertion, ctx)?,
    Expr::SatisfiesExpr(satisfies) => emit_satisfies_expr(em, satisfies, ctx)?,
    Expr::ArrowFunc(func) => emit_arrow_function(em, func, ctx)?,
    Expr::Func(func) => emit_function_expr(em, func, ctx)?,
    Expr::Class(class) => emit_class_expression(em, class)?,
    Expr::Import(import) => emit_import_expr(em, import, ctx)?,
    Expr::TaggedTemplate(tagged) => emit_tagged_template(em, tagged, ctx)?,
    _ => return Err(EmitError::unsupported("expression kind not supported")),
  }
  Ok(())
}

fn emit_binary(em: &mut Emitter, binary: &Node<BinaryExpr>, ctx: ExprCtx) -> EmitResult {
  let op = OPERATORS
    .get(&binary.stx.operator)
    .ok_or_else(|| EmitError::unsupported("unknown operator"))?;
  let op_txt = binary_operator_text(binary.stx.operator)?;
  let prec = op.precedence;

  emit_expr_with_min_prec(em, &binary.stx.left, prec, ctx)?;

  match binary.stx.operator {
    OperatorName::In | OperatorName::Instanceof => em.write_keyword(op_txt),
    OperatorName::NullishCoalescing
    | OperatorName::LogicalAnd
    | OperatorName::LogicalOr
    | OperatorName::BitwiseAnd
    | OperatorName::BitwiseOr
    | OperatorName::BitwiseXor
    | OperatorName::BitwiseLeftShift
    | OperatorName::BitwiseRightShift
    | OperatorName::BitwiseUnsignedRightShift
    | OperatorName::Addition
    | OperatorName::Subtraction
    | OperatorName::Multiplication
    | OperatorName::Division
    | OperatorName::Remainder
    | OperatorName::Exponentiation
    | OperatorName::Equality
    | OperatorName::Inequality
    | OperatorName::StrictEquality
    | OperatorName::StrictInequality
    | OperatorName::LessThan
    | OperatorName::LessThanOrEqual
    | OperatorName::GreaterThan
    | OperatorName::GreaterThanOrEqual
    | OperatorName::Comma
    | OperatorName::Assignment
    | OperatorName::AssignmentAddition
    | OperatorName::AssignmentSubtraction
    | OperatorName::AssignmentMultiplication
    | OperatorName::AssignmentDivision
    | OperatorName::AssignmentRemainder
    | OperatorName::AssignmentExponentiation
    | OperatorName::AssignmentBitwiseAnd
    | OperatorName::AssignmentBitwiseOr
    | OperatorName::AssignmentBitwiseXor
    | OperatorName::AssignmentBitwiseLeftShift
    | OperatorName::AssignmentBitwiseRightShift
    | OperatorName::AssignmentBitwiseUnsignedRightShift
    | OperatorName::AssignmentLogicalAnd
    | OperatorName::AssignmentLogicalOr
    | OperatorName::AssignmentNullishCoalescing => em.write_punct(op_txt),
    _ => return Err(EmitError::unsupported("operator not supported")),
  }

  let right_prec = prec + (op.associativity == Associativity::Left) as u8;
  emit_expr_with_min_prec(em, &binary.stx.right, right_prec, ctx)
}

fn emit_conditional(em: &mut Emitter, cond: &Node<CondExpr>, ctx: ExprCtx) -> EmitResult {
  let prec = OPERATORS
    .get(&OperatorName::Conditional)
    .ok_or_else(|| EmitError::unsupported("unknown operator"))?
    .precedence;
  emit_expr_with_min_prec(em, &cond.stx.test, prec, ctx)?;
  em.write_punct("?");
  emit_expr_with_min_prec(em, &cond.stx.consequent, prec, ctx)?;
  em.write_punct(":");
  emit_expr_with_min_prec(em, &cond.stx.alternate, prec, ctx)
}

fn emit_call(em: &mut Emitter, call: &Node<CallExpr>, ctx: ExprCtx) -> EmitResult {
  if call.stx.optional_chaining {
    if let Expr::Instantiation(instantiation) = call.stx.callee.stx.as_ref() {
      emit_expr_with_min_prec(
        em,
        &instantiation.stx.expression,
        CALL_MEMBER_PRECEDENCE,
        ctx,
      )?;
      em.write_str("?.");
      em.write_punct("<");
      for (idx, arg) in instantiation.stx.type_arguments.iter().enumerate() {
        if idx > 0 {
          em.write_punct(",");
          if !em.minify() {
            em.write_space();
          }
        }
        emit_ts_type(em, arg)?;
      }
      em.write_punct(">");
      em.write_punct("(");
      for (i, arg) in call.stx.arguments.iter().enumerate() {
        if i > 0 {
          em.write_punct(",");
        }
        let CallArg { spread, value } = arg.stx.as_ref();
        if *spread {
          em.write_punct("...");
        }
        emit_expr_with_min_prec(em, value, 1, ctx)?;
      }
      em.write_punct(")");
      return Ok(());
    }
  }

  emit_expr_with_min_prec(em, &call.stx.callee, CALL_MEMBER_PRECEDENCE, ctx)?;
  if call.stx.optional_chaining {
    em.write_str("?.(");
  } else {
    em.write_punct("(");
  }
  for (i, arg) in call.stx.arguments.iter().enumerate() {
    if i > 0 {
      em.write_punct(",");
    }
    let CallArg { spread, value } = arg.stx.as_ref();
    if *spread {
      em.write_punct("...");
    }
    emit_expr_with_min_prec(em, value, 1, ctx)?;
  }
  em.write_punct(")");
  Ok(())
}

fn emit_member(em: &mut Emitter, member: &Node<MemberExpr>, ctx: ExprCtx) -> EmitResult {
  if member.stx.optional_chaining {
    emit_expr_with_min_prec(em, &member.stx.left, CALL_MEMBER_PRECEDENCE, ctx)?;
    em.write_str("?.");
  } else if let Expr::LitNum(num) = member.stx.left.stx.as_ref() {
    let rendered = num.stx.value.to_string();
    em.write_str(&rendered);
    if requires_trailing_dot(&rendered) {
      em.write_punct(".");
    }
    em.write_punct(".");
  } else {
    emit_expr_with_min_prec(em, &member.stx.left, CALL_MEMBER_PRECEDENCE, ctx)?;
    em.write_punct(".");
  }
  em.write_identifier(&member.stx.right);
  Ok(())
}

fn emit_computed_member(
  em: &mut Emitter,
  member: &Node<ComputedMemberExpr>,
  ctx: ExprCtx,
) -> EmitResult {
  emit_expr_with_min_prec(em, &member.stx.object, CALL_MEMBER_PRECEDENCE, ctx)?;
  if member.stx.optional_chaining {
    em.write_str("?.[");
  } else {
    em.write_punct("[");
  }
  emit_expr_with_min_prec(em, &member.stx.member, 1, ctx)?;
  em.write_punct("]");
  Ok(())
}

fn emit_instantiation_expr(
  em: &mut Emitter,
  instantiation: &Node<InstantiationExpr>,
  ctx: ExprCtx,
) -> EmitResult {
  emit_expr_with_min_prec(
    em,
    &instantiation.stx.expression,
    CALL_MEMBER_PRECEDENCE,
    ctx,
  )?;
  em.write_punct("<");
  for (idx, arg) in instantiation.stx.type_arguments.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
      if !em.minify() {
        em.write_space();
      }
    }
    emit_ts_type(em, arg)?;
  }
  em.write_punct(">");
  Ok(())
}

fn emit_unary(em: &mut Emitter, unary: &Node<UnaryExpr>, ctx: ExprCtx) -> EmitResult {
  if unary.stx.operator == OperatorName::New {
    return emit_new_expr(em, &unary.stx.argument, ctx);
  }

  let op = unary_operator_text(unary.stx.operator)?;
  match unary.stx.operator {
    OperatorName::Typeof | OperatorName::Void | OperatorName::Delete | OperatorName::Await => {
      em.write_keyword(op)
    }
    OperatorName::Yield => em.write_keyword(op),
    OperatorName::YieldDelegated => {
      em.write_keyword(op);
      em.write_punct("*");
    }
    OperatorName::LogicalNot
    | OperatorName::BitwiseNot
    | OperatorName::UnaryPlus
    | OperatorName::UnaryNegation
    | OperatorName::PrefixIncrement
    | OperatorName::PrefixDecrement => em.write_punct(op),
    _ => return Err(EmitError::unsupported("unary operator not supported")),
  }
  let prec = OPERATORS
    .get(&unary.stx.operator)
    .ok_or_else(|| EmitError::unsupported("unknown operator"))?
    .precedence;
  emit_expr_with_min_prec(em, &unary.stx.argument, prec, ctx)
}

fn emit_new_expr(em: &mut Emitter, argument: &Node<Expr>, ctx: ExprCtx) -> EmitResult {
  em.write_keyword("new");

  match argument.stx.as_ref() {
    Expr::Call(call) => {
      if call.stx.optional_chaining {
        em.write_punct("(");
        emit_call(em, call, ctx)?;
        em.write_punct(")");
        return Ok(());
      }

      let callee = &call.stx.callee;
      if starts_with_optional_chaining(callee) {
        em.write_punct("(");
        emit_expr_with_min_prec(em, callee, CALL_MEMBER_PRECEDENCE, ctx)?;
        em.write_punct(")");
      } else {
        emit_expr_with_min_prec(em, callee, CALL_MEMBER_PRECEDENCE, ctx)?;
      }

      em.write_punct("(");
      for (i, arg) in call.stx.arguments.iter().enumerate() {
        if i > 0 {
          em.write_punct(",");
        }
        let CallArg { spread, value } = arg.stx.as_ref();
        if *spread {
          em.write_punct("...");
        }
        emit_expr_with_min_prec(em, value, 1, ctx)?;
      }
      em.write_punct(")");
      Ok(())
    }
    _ => {
      if starts_with_optional_chaining(argument) {
        em.write_punct("(");
        emit_expr_with_min_prec(em, argument, CALL_MEMBER_PRECEDENCE, ctx)?;
        em.write_punct(")");
      } else {
        emit_expr_with_min_prec(em, argument, CALL_MEMBER_PRECEDENCE, ctx)?;
      }
      Ok(())
    }
  }
}

fn emit_postfix(em: &mut Emitter, postfix: &Node<UnaryPostfixExpr>, ctx: ExprCtx) -> EmitResult {
  emit_expr_with_min_prec(em, &postfix.stx.argument, POSTFIX_PRECEDENCE, ctx)?;
  let op = match postfix.stx.operator {
    OperatorName::PostfixIncrement => "++",
    OperatorName::PostfixDecrement => "--",
    _ => return Err(EmitError::unsupported("postfix operator not supported")),
  };
  em.write_punct(op);
  Ok(())
}

fn emit_array_literal(em: &mut Emitter, arr: &Node<LitArrExpr>) -> EmitResult {
  em.write_punct("[");
  for (idx, elem) in arr.stx.elements.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    match elem {
      LitArrElem::Single(expr) => emit_expr(em, expr, ExprCtx::Default)?,
      LitArrElem::Rest(expr) => {
        em.write_punct("...");
        emit_expr(em, expr, ExprCtx::Default)?;
      }
      LitArrElem::Empty => {}
    }
  }
  em.write_punct("]");
  Ok(())
}

fn emit_object_literal(em: &mut Emitter, obj: &Node<LitObjExpr>) -> EmitResult {
  em.write_punct("{");
  for (idx, member) in obj.stx.members.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_obj_member(em, member)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_obj_member(em: &mut Emitter, member: &Node<ObjMember>) -> EmitResult {
  match &member.stx.typ {
    ObjMemberType::Valued { key, val } => emit_obj_valued_member(em, key, val),
    ObjMemberType::Shorthand { id } => {
      em.write_identifier(&id.stx.name);
      Ok(())
    }
    ObjMemberType::Rest { val } => {
      em.write_punct("...");
      emit_expr(em, val, ExprCtx::Default)
    }
  }
}

fn emit_obj_valued_member(
  em: &mut Emitter,
  key: &ClassOrObjKey,
  val: &ClassOrObjVal,
) -> EmitResult {
  match val {
    ClassOrObjVal::Prop(init) => {
      emit_class_or_object_key(em, key)?;
      if let Some(init) = init {
        em.write_punct(":");
        emit_expr(em, init, ExprCtx::Default)?;
      }
      Ok(())
    }
    ClassOrObjVal::Getter(get) => {
      em.write_keyword("get");
      emit_class_or_object_key(em, key)?;
      emit_type_params(em, get.stx.func.stx.type_parameters.as_deref());
      em.write_punct("(");
      em.write_punct(")");
      if let Some(ret) = &get.stx.func.stx.return_type {
        emit_type_annotation(em, ret)?;
      }
      emit_func_body(em, &get.stx.func.stx.body, ExprCtx::Default)
    }
    ClassOrObjVal::Setter(set) => {
      em.write_keyword("set");
      emit_class_or_object_key(em, key)?;
      emit_type_params(em, set.stx.func.stx.type_parameters.as_deref());
      em.write_punct("(");
      if let Some(param) = set.stx.func.stx.parameters.first() {
        emit_param_decl(em, param)?;
      }
      em.write_punct(")");
      if let Some(ret) = &set.stx.func.stx.return_type {
        emit_type_annotation(em, ret)?;
      }
      emit_func_body(em, &set.stx.func.stx.body, ExprCtx::Default)
    }
    ClassOrObjVal::Method(method) => {
      if method.stx.func.stx.async_ {
        em.write_keyword("async");
      }
      if method.stx.func.stx.generator {
        em.write_punct("*");
      }
      emit_class_or_object_key(em, key)?;
      emit_function_params_and_body(em, &method.stx.func, ExprCtx::Default)
    }
    ClassOrObjVal::IndexSignature(_) | ClassOrObjVal::StaticBlock(_) => {
      Err(EmitError::unsupported("object member kind not supported"))
    }
  }
}

fn emit_class_or_object_key(em: &mut Emitter, key: &ClassOrObjKey) -> EmitResult {
  match key {
    ClassOrObjKey::Direct(name) => {
      match name.stx.tt {
        TT::LiteralString => emit_string_literal(em, &name.stx.key),
        TT::LiteralBigInt => em.write_bigint_literal(&name.stx.key),
        TT::LiteralNumber | TT::LiteralNumberBin | TT::LiteralNumberHex | TT::LiteralNumberOct => {
          em.write_number(&name.stx.key)
        }
        tt if tt == TT::Identifier || tt.is_keyword() => em.write_identifier(&name.stx.key),
        _ => em.write_str(&name.stx.key),
      }
      Ok(())
    }
    ClassOrObjKey::Computed(expr) => {
      em.write_punct("[");
      emit_expr(em, expr, ExprCtx::Default)?;
      em.write_punct("]");
      Ok(())
    }
  }
}

fn emit_type_annotation(em: &mut Emitter, ty: &Node<TypeExpr>) -> EmitResult {
  em.write_punct(":");
  if !em.minify() {
    em.write_space();
  }
  emit_ts_type(em, ty)
}

fn emit_type_params(em: &mut Emitter, params: Option<&[Node<TypeParameter>]>) {
  let Some(params) = params else {
    return;
  };
  if params.is_empty() {
    return;
  }
  let mut buf = String::new();
  emit_type_parameters(&mut buf, Some(params));
  em.write_str(&buf);
}

fn emit_param_decl(em: &mut Emitter, param: &Node<ParamDecl>) -> EmitResult {
  let param = param.stx.as_ref();
  emit_decorators(em, &param.decorators)?;
  if param.rest {
    em.write_punct("...");
  }
  if let Some(accessibility) = &param.accessibility {
    emit_accessibility(em, *accessibility);
  }
  if param.readonly {
    em.write_keyword("readonly");
  }
  emit_pat_decl(em, &param.pattern)?;
  if param.optional {
    em.write_punct("?");
  }
  if let Some(ty) = &param.type_annotation {
    emit_type_annotation(em, ty)?;
  }
  if let Some(default) = &param.default_value {
    em.write_punct("=");
    emit_expr(em, default, ExprCtx::Default)?;
  }
  Ok(())
}

fn emit_accessibility(em: &mut Emitter, accessibility: Accessibility) {
  match accessibility {
    Accessibility::Public => em.write_keyword("public"),
    Accessibility::Private => em.write_keyword("private"),
    Accessibility::Protected => em.write_keyword("protected"),
  }
}

fn emit_pat_decl(em: &mut Emitter, decl: &Node<PatDecl>) -> EmitResult {
  emit_pat(em, &decl.stx.pat)
}

fn emit_pat(em: &mut Emitter, pat: &Node<Pat>) -> EmitResult {
  match pat.stx.as_ref() {
    Pat::Arr(arr) => emit_array_pattern(em, arr),
    Pat::Id(id) => emit_id_pat(em, id),
    Pat::Obj(obj) => emit_object_pattern(em, obj),
    Pat::AssignTarget(expr) => emit_expr(em, expr, ExprCtx::Default),
  }
}

fn emit_id_pat(em: &mut Emitter, id: &Node<IdPat>) -> EmitResult {
  em.write_identifier(&id.stx.name);
  Ok(())
}

fn emit_array_pattern(em: &mut Emitter, arr: &Node<ArrPat>) -> EmitResult {
  em.write_punct("[");
  for (idx, elem) in arr.stx.elements.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    if let Some(elem) = elem {
      emit_pat(em, &elem.target)?;
      if let Some(default) = &elem.default_value {
        em.write_punct("=");
        emit_expr(em, default, ExprCtx::Default)?;
      }
    }
  }
  if let Some(rest) = &arr.stx.rest {
    if !arr.stx.elements.is_empty() {
      em.write_punct(",");
    }
    em.write_punct("...");
    emit_pat(em, rest)?;
  }
  em.write_punct("]");
  Ok(())
}

fn emit_object_pattern(em: &mut Emitter, obj: &Node<ObjPat>) -> EmitResult {
  em.write_punct("{");
  for (idx, prop) in obj.stx.properties.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_obj_pat_prop(em, prop)?;
  }
  if let Some(rest) = &obj.stx.rest {
    if !obj.stx.properties.is_empty() {
      em.write_punct(",");
    }
    em.write_punct("...");
    emit_pat(em, rest)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_obj_pat_prop(em: &mut Emitter, prop: &Node<ObjPatProp>) -> EmitResult {
  emit_class_or_object_key(em, &prop.stx.key)?;
  if !prop.stx.shorthand {
    em.write_punct(":");
    emit_pat(em, &prop.stx.target)?;
  }
  if let Some(default) = &prop.stx.default_value {
    em.write_punct("=");
    emit_expr(em, default, ExprCtx::Default)?;
  }
  Ok(())
}

fn emit_type_assertion(
  em: &mut Emitter,
  assertion: &Node<TypeAssertionExpr>,
  ctx: ExprCtx,
) -> EmitResult {
  emit_expr_with_min_prec(
    em,
    &assertion.stx.expression,
    crate::precedence::TYPE_ASSERTION_PRECEDENCE.value(),
    ctx,
  )?;
  em.write_keyword("as");
  if assertion.stx.const_assertion {
    em.write_keyword("const");
    return Ok(());
  }
  match &assertion.stx.type_annotation {
    Some(ty) => {
      let mut buf = String::new();
      emit_type_expr(&mut buf, ty).map_err(EmitError::from)?;
      em.write_str(&buf);
      Ok(())
    }
    None => Err(EmitError::missing_type_annotation()),
  }
}

fn emit_satisfies_expr(
  em: &mut Emitter,
  satisfies: &Node<SatisfiesExpr>,
  ctx: ExprCtx,
) -> EmitResult {
  emit_expr_with_min_prec(
    em,
    &satisfies.stx.expression,
    crate::precedence::TYPE_ASSERTION_PRECEDENCE.value(),
    ctx,
  )?;
  em.write_keyword("satisfies");
  let mut buf = String::new();
  emit_type_expr(&mut buf, &satisfies.stx.type_annotation).map_err(EmitError::from)?;
  em.write_str(&buf);
  Ok(())
}

fn emit_arrow_function(em: &mut Emitter, func: &Node<ArrowFuncExpr>, ctx: ExprCtx) -> EmitResult {
  let func = func.stx.as_ref();
  let func = func.func.stx.as_ref();

  if func.generator {
    return Err(EmitError::unsupported(
      "generator arrow function not supported",
    ));
  }
  if func.async_ {
    em.write_keyword("async");
  }

  emit_type_params(em, func.type_parameters.as_deref());
  emit_function_params(em, &func.parameters)?;
  if let Some(ret) = &func.return_type {
    emit_type_annotation(em, ret)?;
  }

  em.write_punct("=>");
  match &func.body {
    Some(FuncBody::Expression(expr)) => {
      let needs_parens = is_comma_expression(expr.stx.as_ref()) || expr_starts_with_brace(expr);
      if needs_parens {
        em.write_punct("(");
      }
      emit_expr_with_min_prec(em, expr, 1, ctx)?;
      if needs_parens {
        em.write_punct(")");
      }
      Ok(())
    }
    Some(FuncBody::Block(stmts)) => {
      em.write_punct("{");
      for stmt in stmts {
        crate::stmt::emit_stmt(em, stmt)?;
      }
      em.write_punct("}");
      Ok(())
    }
    None => Err(EmitError::unsupported("arrow function missing body")),
  }
}

fn emit_function_params(em: &mut Emitter, params: &[Node<ParamDecl>]) -> EmitResult {
  em.write_punct("(");
  for (idx, param) in params.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_param_decl(em, param)?;
  }
  em.write_punct(")");
  Ok(())
}

fn emit_function_params_and_body(em: &mut Emitter, func: &Node<Func>, ctx: ExprCtx) -> EmitResult {
  emit_type_params(em, func.stx.type_parameters.as_deref());
  emit_function_params(em, &func.stx.parameters)?;
  if let Some(ret) = &func.stx.return_type {
    emit_type_annotation(em, ret)?;
  }
  emit_func_body(em, &func.stx.body, ctx)
}

fn emit_func_body(em: &mut Emitter, body: &Option<FuncBody>, ctx: ExprCtx) -> EmitResult {
  match body {
    Some(FuncBody::Block(stmts)) => {
      em.write_punct("{");
      for stmt in stmts {
        crate::stmt::emit_stmt(em, stmt)?;
      }
      em.write_punct("}");
      Ok(())
    }
    Some(FuncBody::Expression(expr)) => emit_expr(em, expr, ctx),
    None => Err(EmitError::unsupported("function missing body")),
  }
}

fn emit_function_expr(em: &mut Emitter, func: &Node<FuncExpr>, ctx: ExprCtx) -> EmitResult {
  let func = func.stx.as_ref();
  if func.func.stx.async_ {
    em.write_keyword("async");
  }
  em.write_keyword("function");
  if func.func.stx.generator {
    em.write_punct("*");
  }
  if let Some(name) = &func.name {
    em.write_identifier(&name.stx.name);
  }
  emit_function_params_and_body(em, &func.func, ctx)
}

fn emit_class_expression(em: &mut Emitter, class: &Node<ClassExpr>) -> EmitResult {
  let class = class.stx.as_ref();
  emit_decorators(em, &class.decorators)?;
  emit_class_like(
    em,
    class.name.as_ref(),
    class.type_parameters.as_deref(),
    class.extends.as_ref(),
    &class.implements,
    |em, ty| emit_ts_type(em, ty),
    &class.members,
    true,
  )
}

fn emit_import_expr(em: &mut Emitter, import: &Node<ImportExpr>, ctx: ExprCtx) -> EmitResult {
  em.write_keyword("import");
  em.write_punct("(");
  emit_expr(em, &import.stx.module, ctx)?;
  if let Some(attrs) = &import.stx.attributes {
    em.write_punct(",");
    emit_expr(em, attrs, ctx)?;
  }
  em.write_punct(")");
  Ok(())
}

fn emit_tagged_template(
  em: &mut Emitter,
  tagged: &Node<TaggedTemplateExpr>,
  ctx: ExprCtx,
) -> EmitResult {
  emit_expr_with_min_prec(em, &tagged.stx.function, CALL_MEMBER_PRECEDENCE, ctx)?;
  emit_template_parts(em, &tagged.stx.parts)
}

fn emit_template_literal(em: &mut Emitter, template: &Node<LitTemplateExpr>) -> EmitResult {
  emit_template_parts(em, &template.stx.parts)
}

fn emit_template_parts(em: &mut Emitter, parts: &[LitTemplatePart]) -> EmitResult {
  em.write_raw_byte(b'`');
  for (idx, part) in parts.iter().enumerate() {
    match part {
      LitTemplatePart::String(raw) => {
        let is_first = idx == 0;
        let is_last = idx + 1 == parts.len();
        let cooked = cooked_template_segment(raw, is_first, is_last);
        let mut buf = Vec::new();
        emit_template_literal_segment(&mut buf, cooked);
        em.write_raw_str(std::str::from_utf8(&buf).expect("template literal segment is UTF-8"));
      }
      LitTemplatePart::Substitution(expr) => {
        em.write_raw_str("${");
        emit_expr(em, expr, ExprCtx::Default)?;
        em.write_raw_byte(b'}');
      }
    }
  }
  em.write_raw_byte(b'`');
  Ok(())
}

fn emit_expr_via_fmt(em: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  let mut buf = String::new();
  let mut emit_type = |out: &mut String, ty: &Node<TypeExpr>| emit_type_expr(out, ty);
  crate::expr::emit_expr_with_options(&mut buf, expr, &mut emit_type, em.options())?;
  em.write_str(&buf);
  Ok(())
}

fn emit_string_literal(em: &mut Emitter, value: &str) {
  em.write_string_literal(value);
}

fn binary_operator_text(op: OperatorName) -> Result<&'static str, EmitError> {
  match op {
    OperatorName::Addition => Ok("+"),
    OperatorName::Subtraction => Ok("-"),
    OperatorName::Multiplication => Ok("*"),
    OperatorName::Division => Ok("/"),
    OperatorName::Remainder => Ok("%"),
    OperatorName::Exponentiation => Ok("**"),
    OperatorName::LessThan => Ok("<"),
    OperatorName::LessThanOrEqual => Ok("<="),
    OperatorName::GreaterThan => Ok(">"),
    OperatorName::GreaterThanOrEqual => Ok(">="),
    OperatorName::Equality => Ok("=="),
    OperatorName::Inequality => Ok("!="),
    OperatorName::StrictEquality => Ok("==="),
    OperatorName::StrictInequality => Ok("!=="),
    OperatorName::BitwiseAnd => Ok("&"),
    OperatorName::BitwiseOr => Ok("|"),
    OperatorName::BitwiseXor => Ok("^"),
    OperatorName::BitwiseLeftShift => Ok("<<"),
    OperatorName::BitwiseRightShift => Ok(">>"),
    OperatorName::BitwiseUnsignedRightShift => Ok(">>>"),
    OperatorName::LogicalAnd => Ok("&&"),
    OperatorName::LogicalOr => Ok("||"),
    OperatorName::NullishCoalescing => Ok("??"),
    OperatorName::In => Ok("in"),
    OperatorName::Instanceof => Ok("instanceof"),
    OperatorName::Comma => Ok(","),
    OperatorName::Assignment => Ok("="),
    OperatorName::AssignmentAddition => Ok("+="),
    OperatorName::AssignmentBitwiseAnd => Ok("&="),
    OperatorName::AssignmentBitwiseLeftShift => Ok("<<="),
    OperatorName::AssignmentBitwiseOr => Ok("|="),
    OperatorName::AssignmentBitwiseRightShift => Ok(">>="),
    OperatorName::AssignmentBitwiseUnsignedRightShift => Ok(">>>="),
    OperatorName::AssignmentBitwiseXor => Ok("^="),
    OperatorName::AssignmentDivision => Ok("/="),
    OperatorName::AssignmentExponentiation => Ok("**="),
    OperatorName::AssignmentLogicalAnd => Ok("&&="),
    OperatorName::AssignmentLogicalOr => Ok("||="),
    OperatorName::AssignmentMultiplication => Ok("*="),
    OperatorName::AssignmentNullishCoalescing => Ok("??="),
    OperatorName::AssignmentRemainder => Ok("%="),
    OperatorName::AssignmentSubtraction => Ok("-="),
    _ => Err(EmitError::unsupported(
      "operator not supported in binary emitter",
    )),
  }
}

fn unary_operator_text(op: OperatorName) -> Result<&'static str, EmitError> {
  match op {
    OperatorName::LogicalNot => Ok("!"),
    OperatorName::BitwiseNot => Ok("~"),
    OperatorName::UnaryPlus => Ok("+"),
    OperatorName::UnaryNegation => Ok("-"),
    OperatorName::PrefixIncrement => Ok("++"),
    OperatorName::PrefixDecrement => Ok("--"),
    OperatorName::Typeof => Ok("typeof"),
    OperatorName::Void => Ok("void"),
    OperatorName::Delete => Ok("delete"),
    OperatorName::Await => Ok("await"),
    OperatorName::Yield => Ok("yield"),
    OperatorName::YieldDelegated => Ok("yield"),
    _ => Err(EmitError::unsupported("unsupported unary operator")),
  }
}

fn requires_trailing_dot(rendered: &str) -> bool {
  let mut bytes = rendered.as_bytes();
  if bytes.starts_with(b"-") {
    bytes = &bytes[1..];
  }
  bytes.iter().all(|b| b.is_ascii_digit())
}

fn is_comma_expression(expr: &Expr) -> bool {
  matches!(expr, Expr::Binary(binary) if binary.stx.operator == OperatorName::Comma)
}

fn expr_starts_with_brace(expr: &Node<Expr>) -> bool {
  match expr.stx.as_ref() {
    Expr::LitObj(_) | Expr::ObjPat(_) => true,
    Expr::Binary(binary) => expr_starts_with_brace(&binary.stx.left),
    Expr::Call(call) => expr_starts_with_brace(&call.stx.callee),
    Expr::Instantiation(instantiation) => expr_starts_with_brace(&instantiation.stx.expression),
    Expr::Member(member) => expr_starts_with_brace(&member.stx.left),
    Expr::ComputedMember(member) => expr_starts_with_brace(&member.stx.object),
    Expr::TaggedTemplate(tagged) => expr_starts_with_brace(&tagged.stx.function),
    Expr::NonNullAssertion(expr) => expr_starts_with_brace(&expr.stx.expression),
    Expr::TypeAssertion(assertion) => expr_starts_with_brace(&assertion.stx.expression),
    Expr::SatisfiesExpr(satisfies) => expr_starts_with_brace(&satisfies.stx.expression),
    Expr::UnaryPostfix(unary) => expr_starts_with_brace(&unary.stx.argument),
    Expr::Cond(cond) => expr_starts_with_brace(&cond.stx.test),
    _ => false,
  }
}
