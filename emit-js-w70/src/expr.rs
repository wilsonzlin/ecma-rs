use crate::literal;
use crate::EmitMode;
use parse_js::ast::expr::ComputedMemberExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::expr::TaggedTemplateExpr;
use parse_js::ast::node::Node;
use std::fmt;

enum ExprContext {
  Default,
  MemberObject { needs_numeric_fix: bool },
}

pub(crate) fn emit_expr_to<W: fmt::Write>(
  out: &mut W,
  expr: &Node<Expr>,
  mode: EmitMode,
) -> fmt::Result {
  emit_expr_with_ctx(out, expr, mode, ExprContext::Default)
}

fn emit_expr_with_ctx<W: fmt::Write>(
  out: &mut W,
  expr: &Node<Expr>,
  mode: EmitMode,
  ctx: ExprContext,
) -> fmt::Result {
  match expr.stx.as_ref() {
    Expr::Id(node) => out.write_str(&node.stx.name),
    Expr::This(_) => out.write_str("this"),
    Expr::Super(_) => out.write_str("super"),
    Expr::LitBigInt(node) => literal::emit_big_int_literal(out, node.stx.as_ref()),
    Expr::LitBool(node) => literal::emit_bool_literal(out, node.stx.as_ref()),
    Expr::LitNull(_) => literal::emit_null_literal(out),
    Expr::LitNum(node) => literal::emit_number_literal(
      out,
      node.stx.value,
      matches!(
        ctx,
        ExprContext::MemberObject {
          needs_numeric_fix: true
        }
      ),
    ),
    Expr::LitRegex(node) => literal::emit_regex_literal(out, node.stx.as_ref()),
    Expr::LitStr(node) => literal::emit_string_literal_expr(out, node.stx.as_ref(), mode),
    Expr::LitTemplate(node) => literal::emit_template_literal(out, &node.stx.parts, |out, expr| {
      emit_expr_with_ctx(out, expr, mode, ExprContext::Default)
    }),
    Expr::TaggedTemplate(node) => emit_tagged_template_expr(out, node.stx.as_ref(), mode),
    Expr::Member(node) => emit_member_expr(out, node.stx.as_ref(), mode),
    Expr::ComputedMember(node) => emit_computed_member_expr(out, node.stx.as_ref(), mode),
    _ => todo!("expression emission not implemented"),
  }
}

fn emit_tagged_template_expr<W: fmt::Write>(
  out: &mut W,
  expr: &TaggedTemplateExpr,
  mode: EmitMode,
) -> fmt::Result {
  emit_expr_with_ctx(out, &expr.function, mode, ExprContext::Default)?;
  literal::emit_template_literal(out, &expr.parts, |out, expr| {
    emit_expr_with_ctx(out, expr, mode, ExprContext::Default)
  })
}

fn emit_member_expr<W: fmt::Write>(out: &mut W, expr: &MemberExpr, mode: EmitMode) -> fmt::Result {
  emit_expr_with_ctx(
    out,
    &expr.left,
    mode,
    ExprContext::MemberObject {
      needs_numeric_fix: !expr.optional_chaining,
    },
  )?;
  if expr.optional_chaining {
    out.write_str("?.")?;
  } else {
    out.write_char('.')?;
  }
  out.write_str(&expr.right)
}

fn emit_computed_member_expr<W: fmt::Write>(
  out: &mut W,
  expr: &ComputedMemberExpr,
  mode: EmitMode,
) -> fmt::Result {
  emit_expr_with_ctx(out, &expr.object, mode, ExprContext::Default)?;
  if expr.optional_chaining {
    out.write_str("?.[")?;
  } else {
    out.write_char('[')?;
  }
  emit_expr_with_ctx(out, &expr.member, mode, ExprContext::Default)?;
  out.write_char(']')
}
