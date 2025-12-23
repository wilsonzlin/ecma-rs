mod expr;
pub mod literal;
pub mod string;

use expr::emit_expr_to;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum EmitMode {
  Canonical,
  Minified,
}

/// Emit an expression into a string.
pub fn emit(expr: &Node<Expr>, mode: EmitMode) -> String {
  let mut out = String::new();
  emit_to(&mut out, expr, mode).unwrap();
  out
}

/// Emit an expression into a writer.
pub fn emit_to<W: std::fmt::Write>(
  out: &mut W,
  expr: &Node<Expr>,
  mode: EmitMode,
) -> std::fmt::Result {
  emit_expr_to(out, expr, mode)
}
