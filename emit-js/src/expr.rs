use std::fmt;

use parse_js::ast::expr::{
  lit::{LitBigIntExpr, LitBoolExpr, LitNumExpr, LitRegexExpr, LitStrExpr},
  BinaryExpr, CallArg, CallExpr, ComputedMemberExpr, Expr, IdExpr, MemberExpr,
};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;
use parse_js::operator::{Associativity, OperatorName, OPERATORS};

use crate::emitter::{with_node_context, EmitError, EmitResult};
use crate::expr_ts::{
  NON_NULL_ASSERTION_PRECEDENCE, SATISFIES_PRECEDENCE, TYPE_ASSERTION_PRECEDENCE,
};
use crate::Emitter;

const PRIMARY_PRECEDENCE: u8 = 19;
const CALL_MEMBER_PRECEDENCE: u8 = 18; // Matches OperatorName::Call/MemberAccess precedence.

pub struct ExprEmitter<'a, W, F>
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  pub(crate) out: &'a mut W,
  pub(crate) emit_type: F,
}

impl<'a, W, F> ExprEmitter<'a, W, F>
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  pub fn new(out: &'a mut W, emit_type: F) -> Self {
    Self { out, emit_type }
  }

  pub fn emit_expr(&mut self, expr: &Node<Expr>) -> EmitResult {
    with_node_context(expr.loc, || self.emit_expr_with_min_prec(expr, 1))
  }

  pub(crate) fn emit_expr_with_min_prec(&mut self, expr: &Node<Expr>, min_prec: u8) -> EmitResult {
    with_node_context(expr.loc, || {
      let prec = expr_precedence(expr)?;
      let needs_parens = prec < min_prec;

      if needs_parens {
        write!(self.out, "(")?;
      }
      self.emit_expr_no_parens(expr)?;
      if needs_parens {
        write!(self.out, ")")?;
      }

      Ok(())
    })
  }

  fn emit_expr_no_parens(&mut self, expr: &Node<Expr>) -> EmitResult {
    with_node_context(expr.loc, || match expr.stx.as_ref() {
      Expr::Id(id) => self.emit_id(id),
      Expr::This(_) => self.emit_this(),
      Expr::Super(_) => self.emit_super(),
      Expr::NewTarget(_) => self.emit_new_target(),
      Expr::ImportMeta(_) => self.emit_import_meta(),
      Expr::LitNum(num) => self.emit_lit_num(num),
      Expr::LitBool(lit) => self.emit_lit_bool(lit),
      Expr::LitNull(_) => self.emit_lit_null(),
      Expr::LitBigInt(lit) => self.emit_lit_big_int(lit),
      Expr::LitStr(lit) => self.emit_lit_str(lit),
      Expr::LitRegex(lit) => self.emit_lit_regex(lit),
      Expr::JsxElem(elem) => crate::jsx::emit_jsx_elem(self.out, elem),
      Expr::Binary(binary) => self.emit_binary(binary),
      Expr::Call(call) => self.emit_call(call),
      Expr::Member(member) => self.emit_member(member),
      Expr::ComputedMember(member) => self.emit_computed_member(member),
      Expr::NonNullAssertion(non_null) => self.emit_non_null_assertion(non_null),
      Expr::TypeAssertion(assertion) => self.emit_type_assertion(assertion),
      Expr::SatisfiesExpr(satisfies) => self.emit_satisfies_expr(satisfies),
      _ => Err(EmitError::unsupported("expression kind not supported")),
    })
  }

  fn emit_id(&mut self, id: &Node<IdExpr>) -> EmitResult {
    with_node_context(id.loc, || {
      self.out.write_str(&id.stx.name)?;
      Ok(())
    })
  }

  fn emit_this(&mut self) -> EmitResult {
    self.out.write_str("this")?;
    Ok(())
  }

  fn emit_super(&mut self) -> EmitResult {
    self.out.write_str("super")?;
    Ok(())
  }

  fn emit_new_target(&mut self) -> EmitResult {
    self.out.write_str("new.target")?;
    Ok(())
  }

  fn emit_import_meta(&mut self) -> EmitResult {
    self.out.write_str("import.meta")?;
    Ok(())
  }

  fn emit_lit_num(&mut self, lit: &Node<LitNumExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      write!(self.out, "{}", lit.stx.value)?;
      Ok(())
    })
  }

  fn emit_lit_bool(&mut self, lit: &Node<LitBoolExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      self
        .out
        .write_str(if lit.stx.value { "true" } else { "false" })?;
      Ok(())
    })
  }

  fn emit_lit_null(&mut self) -> EmitResult {
    self.out.write_str("null")?;
    Ok(())
  }

  fn emit_lit_big_int(&mut self, lit: &Node<LitBigIntExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      self.out.write_str(&lit.stx.value)?;
      Ok(())
    })
  }

  fn emit_lit_str(&mut self, lit: &Node<LitStrExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      let mut buf = Vec::new();
      crate::emit_string_literal_double_quoted(&mut buf, &lit.stx.value);
      self
        .out
        .write_str(std::str::from_utf8(&buf).expect("string literal escape output is UTF-8"))?;
      Ok(())
    })
  }

  fn emit_lit_regex(&mut self, lit: &Node<LitRegexExpr>) -> EmitResult {
    with_node_context(lit.loc, || {
      self.out.write_str(&lit.stx.value)?;
      Ok(())
    })
  }

  fn emit_binary(&mut self, binary: &Node<BinaryExpr>) -> EmitResult {
    with_node_context(binary.loc, || {
      let op = OPERATORS
        .get(&binary.stx.operator)
        .ok_or(EmitError::unsupported("unknown operator"))?;
      let op_txt = binary_operator_text(binary.stx.operator)?;
      let prec = op.precedence;

      self.emit_expr_with_min_prec(&binary.stx.left, prec)?;
      if binary.stx.operator == OperatorName::Comma {
        write!(self.out, ", ")?;
      } else {
        write!(self.out, " {} ", op_txt)?;
      }
      let right_prec = prec + (op.associativity == Associativity::Left) as u8;
      self.emit_expr_with_min_prec(&binary.stx.right, right_prec)
    })
  }

  fn emit_call(&mut self, call: &Node<CallExpr>) -> EmitResult {
    with_node_context(call.loc, || {
      self.emit_expr_with_min_prec(&call.stx.callee, CALL_MEMBER_PRECEDENCE)?;
      if call.stx.optional_chaining {
        write!(self.out, "?.(")?;
      } else {
        write!(self.out, "(")?;
      }
      for (i, arg) in call.stx.arguments.iter().enumerate() {
        if i > 0 {
          write!(self.out, ", ")?;
        }
        let CallArg { spread, value } = arg.stx.as_ref();
        if *spread {
          write!(self.out, "...")?;
        }
        self.emit_expr_with_min_prec(value, 1)?;
      }
      write!(self.out, ")")?;
      Ok(())
    })
  }

  fn emit_member(&mut self, member: &Node<MemberExpr>) -> EmitResult {
    with_node_context(member.loc, || {
      if member.stx.optional_chaining {
        self.emit_expr_with_min_prec(&member.stx.left, CALL_MEMBER_PRECEDENCE)?;
        write!(self.out, "?.")?;
      } else if let Expr::LitNum(num) = member.stx.left.stx.as_ref() {
        let rendered = num.stx.value.to_string();
        self.out.write_str(&rendered)?;
        if requires_trailing_dot(&rendered) {
          self.out.write_char('.')?;
        }
        self.out.write_char('.')?;
      } else {
        self.emit_expr_with_min_prec(&member.stx.left, CALL_MEMBER_PRECEDENCE)?;
        self.out.write_char('.')?;
      }
      self.out.write_str(&member.stx.right)?;
      Ok(())
    })
  }

  fn emit_computed_member(&mut self, member: &Node<ComputedMemberExpr>) -> EmitResult {
    with_node_context(member.loc, || {
      self.emit_expr_with_min_prec(&member.stx.object, CALL_MEMBER_PRECEDENCE)?;
      if member.stx.optional_chaining {
        write!(self.out, "?.[")?;
      } else {
        write!(self.out, "[")?;
      }
      self.emit_expr_with_min_prec(&member.stx.member, 1)?;
      write!(self.out, "]")?;
      Ok(())
    })
  }

  pub(crate) fn emit_type(&mut self, ty: &Node<TypeExpr>) -> EmitResult {
    with_node_context(ty.loc, || {
      (self.emit_type)(&mut self.out, ty).map_err(EmitError::from)
    })
  }
}

pub fn emit_expr<W, F>(out: &mut W, expr: &Node<Expr>, emit_type: F) -> EmitResult
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  let mut emitter = ExprEmitter::new(out, emit_type);
  emitter.emit_expr(expr)
}

pub fn emit_expr_with_emitter(out: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  struct EmitterWriteAdapter<'a> {
    emitter: &'a mut Emitter,
  }

  impl fmt::Write for EmitterWriteAdapter<'_> {
    fn write_str(&mut self, s: &str) -> fmt::Result {
      self.emitter.write_str(s);
      Ok(())
    }

    fn write_char(&mut self, c: char) -> fmt::Result {
      let mut buf = [0u8; 4];
      let encoded = c.encode_utf8(&mut buf);
      self.emitter.write_str(encoded);
      Ok(())
    }
  }

  let mut adapter = EmitterWriteAdapter { emitter: out };
  let mut emit_type = |out: &mut EmitterWriteAdapter<'_>, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
  emit_expr(&mut adapter, expr, &mut emit_type)
}

fn expr_precedence(expr: &Node<Expr>) -> Result<u8, EmitError> {
  with_node_context(expr.loc, || match expr.stx.as_ref() {
    Expr::Id(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::This(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::Super(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::NewTarget(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::ImportMeta(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::LitNum(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::LitBool(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::LitNull(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::LitBigInt(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::LitStr(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::LitRegex(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::JsxElem(_) => Ok(PRIMARY_PRECEDENCE),
    Expr::Binary(binary) => Ok(
      OPERATORS
        .get(&binary.stx.operator)
        .map(|op| op.precedence)
        .ok_or(EmitError::unsupported("unknown operator"))?,
    ),
    Expr::Call(_) => Ok(CALL_MEMBER_PRECEDENCE),
    Expr::Member(_) => Ok(CALL_MEMBER_PRECEDENCE),
    Expr::ComputedMember(_) => Ok(CALL_MEMBER_PRECEDENCE),
    Expr::NonNullAssertion(_) => Ok(NON_NULL_ASSERTION_PRECEDENCE),
    Expr::TypeAssertion(_) => Ok(TYPE_ASSERTION_PRECEDENCE),
    Expr::SatisfiesExpr(_) => Ok(SATISFIES_PRECEDENCE),
    _ => Err(EmitError::unsupported("expression kind not supported")),
  })
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
    // Operators that should be handled in dedicated branches instead of generic binary printing.
    OperatorName::Call
    | OperatorName::ComputedMemberAccess
    | OperatorName::Conditional
    | OperatorName::ConditionalAlternate
    | OperatorName::MemberAccess
    | OperatorName::OptionalChainingCall
    | OperatorName::OptionalChainingComputedMemberAccess
    | OperatorName::OptionalChainingMemberAccess
    | OperatorName::Await
    | OperatorName::BitwiseNot
    | OperatorName::Delete
    | OperatorName::LogicalNot
    | OperatorName::New
    | OperatorName::PrefixDecrement
    | OperatorName::PrefixIncrement
    | OperatorName::Typeof
    | OperatorName::UnaryNegation
    | OperatorName::UnaryPlus
    | OperatorName::Void
    | OperatorName::Yield
    | OperatorName::YieldDelegated
    | OperatorName::PostfixDecrement
    | OperatorName::PostfixIncrement => Err(EmitError::unsupported(
      "operator not supported in binary emitter",
    )),
  }
}

fn requires_trailing_dot(rendered: &str) -> bool {
  let mut bytes = rendered.as_bytes();
  if bytes.starts_with(b"-") {
    bytes = &bytes[1..];
  }
  bytes.iter().all(|b| b.is_ascii_digit())
}

#[cfg(test)]
mod tests {
  use super::*;
  use parse_js::ast::expr::lit::LitNumExpr;
  use parse_js::ast::expr::NonNullAssertionExpr;
  use parse_js::ast::expr::SatisfiesExpr;
  use parse_js::ast::expr::TypeAssertionExpr;
  use parse_js::ast::type_expr::{TypeEntityName, TypeReference};
  use parse_js::loc::Loc;
  use parse_js::num::JsNumber;

  fn node<T: derive_visitor::Drive + derive_visitor::DriveMut>(stx: T) -> Node<T> {
    Node::new(Loc(0, 0), stx)
  }

  fn type_ref(name: &str) -> Node<TypeExpr> {
    node(TypeExpr::TypeReference(node(TypeReference {
      name: TypeEntityName::Identifier(name.to_string()),
      type_arguments: None,
    })))
  }

  fn id(name: &str) -> Node<Expr> {
    node(Expr::Id(node(IdExpr {
      name: name.to_string(),
    })))
  }

  fn binary_add(left: Node<Expr>, right: Node<Expr>) -> Node<Expr> {
    node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Addition,
      left,
      right,
    })))
  }

  fn lit_num(value: f64) -> Node<Expr> {
    node(Expr::LitNum(node(LitNumExpr {
      value: JsNumber(value),
    })))
  }

  fn member(left: Node<Expr>, right: &str, optional_chaining: bool) -> Node<Expr> {
    node(Expr::Member(node(MemberExpr {
      optional_chaining,
      left,
      right: right.to_string(),
    })))
  }

  fn assert_emit(expr: Node<Expr>, expected: &str) {
    let mut out = String::new();
    let mut emit_type = |out: &mut String, ty: &Node<TypeExpr>| match ty.stx.as_ref() {
      TypeExpr::TypeReference(reference) => match &reference.stx.name {
        TypeEntityName::Identifier(name) => {
          out.push_str(name);
          Ok(())
        }
        _ => Err(fmt::Error),
      },
      _ => Err(fmt::Error),
    };

    emit_expr(&mut out, &expr, &mut emit_type).unwrap();
    assert_eq!(out, expected);
  }

  #[test]
  fn emits_member_after_integer_literal_with_extra_dot() {
    assert_emit(member(lit_num(1.0), "toString", false), "1..toString");
  }

  #[test]
  fn emits_member_after_decimal_literal_without_extra_dot() {
    assert_emit(member(lit_num(1.2), "toString", false), "1.2.toString");
  }

  #[test]
  fn emits_optional_chaining_member_after_integer_literal_without_extra_dot() {
    assert_emit(member(lit_num(1.0), "toString", true), "1?.toString");
  }

  #[test]
  fn emits_type_assertion_const() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(id("x")),
      type_annotation: None,
      const_assertion: true,
    });
    let expr = node(Expr::TypeAssertion(assertion));

    assert_emit(expr, "x as const");
  }

  #[test]
  fn emits_type_assertion_type() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(id("x")),
      type_annotation: Some(type_ref("T")),
      const_assertion: false,
    });
    let expr = node(Expr::TypeAssertion(assertion));

    assert_emit(expr, "x as T");
  }

  #[test]
  fn emits_satisfies_expression() {
    let satisfies = node(SatisfiesExpr {
      expression: Box::new(id("x")),
      type_annotation: type_ref("T"),
    });
    let expr = node(Expr::SatisfiesExpr(satisfies));

    assert_emit(expr, "x satisfies T");
  }

  #[test]
  fn wraps_type_assertion_operand_when_needed() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(binary_add(id("a"), id("b"))),
      type_annotation: Some(type_ref("T")),
      const_assertion: false,
    });
    let expr = node(Expr::TypeAssertion(assertion));

    assert_emit(expr, "(a + b) as T");
  }

  #[test]
  fn emits_non_null_with_parentheses_for_low_precedence_operand() {
    let non_null = node(NonNullAssertionExpr {
      expression: Box::new(binary_add(id("a"), id("b"))),
    });
    let expr = node(Expr::NonNullAssertion(non_null));

    let mut out = String::new();
    let mut emit_type = |_out: &mut String, _ty: &Node<TypeExpr>| Ok(());
    emit_expr(&mut out, &expr, &mut emit_type).unwrap();
    assert_eq!(out, "(a + b)!");
  }

  #[test]
  fn type_assertion_inside_call_argument() {
    let arg = node(CallArg {
      spread: false,
      value: node(Expr::TypeAssertion(node(TypeAssertionExpr {
        expression: Box::new(id("x")),
        type_annotation: Some(type_ref("T")),
        const_assertion: false,
      }))),
    });
    let call = node(Expr::Call(node(CallExpr {
      optional_chaining: false,
      callee: id("f"),
      arguments: vec![arg],
    })));

    assert_emit(call, "f(x as T)");
  }

  #[test]
  fn type_assertion_operand_in_binary_respects_grouping() {
    let assertion = node(TypeAssertionExpr {
      expression: Box::new(binary_add(id("a"), id("b"))),
      type_annotation: Some(type_ref("T")),
      const_assertion: false,
    });
    let outer = node(Expr::Binary(node(BinaryExpr {
      operator: OperatorName::Addition,
      left: node(Expr::TypeAssertion(assertion)),
      right: id("c"),
    })));

    assert_emit(outer, "(a + b) as T + c");
  }
}
