use std::fmt;

use parse_js::ast::expr::{NonNullAssertionExpr, SatisfiesExpr, TypeAssertionExpr};
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;

use crate::expr::{EmitError, EmitResult, ExprEmitter};

pub(crate) const TYPE_ASSERTION_PRECEDENCE: u8 = 15;
pub(crate) const SATISFIES_PRECEDENCE: u8 = TYPE_ASSERTION_PRECEDENCE;
pub(crate) const NON_NULL_ASSERTION_PRECEDENCE: u8 = 18;

impl<'a, W, F> ExprEmitter<'a, W, F>
where
  W: fmt::Write,
  F: FnMut(&mut W, &Node<TypeExpr>) -> fmt::Result,
{
  pub(crate) fn emit_type_assertion(&mut self, assertion: &Node<TypeAssertionExpr>) -> EmitResult {
    self.emit_expr_with_min_prec(&assertion.stx.expression, TYPE_ASSERTION_PRECEDENCE)?;
    write!(self.out, " as ")?;

    if assertion.stx.const_assertion {
      self.out.write_str("const")?;
      return Ok(());
    }

    match &assertion.stx.type_annotation {
      Some(ty) => self.emit_type(ty),
      None => Err(EmitError::MissingTypeAnnotation),
    }
  }

  pub(crate) fn emit_non_null_assertion(
    &mut self,
    assertion: &Node<NonNullAssertionExpr>,
  ) -> EmitResult {
    self.emit_expr_with_min_prec(&assertion.stx.expression, NON_NULL_ASSERTION_PRECEDENCE)?;
    write!(self.out, "!")?;
    Ok(())
  }

  pub(crate) fn emit_satisfies_expr(&mut self, satisfies: &Node<SatisfiesExpr>) -> EmitResult {
    self.emit_expr_with_min_prec(&satisfies.stx.expression, TYPE_ASSERTION_PRECEDENCE)?;
    write!(self.out, " satisfies ")?;
    self.emit_type(&satisfies.stx.type_annotation)
  }
}
