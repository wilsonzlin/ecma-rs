use crate::string::emit_string_literal;
use crate::string::emit_template_part;
use crate::EmitMode;
use parse_js::ast::expr::lit::LitBigIntExpr;
use parse_js::ast::expr::lit::LitBoolExpr;
use parse_js::ast::expr::lit::LitRegexExpr;
use parse_js::ast::expr::lit::LitStrExpr;
use parse_js::ast::expr::lit::LitTemplatePart;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::num::JsNumber;
use std::fmt;

pub fn emit_big_int_literal<W: fmt::Write>(out: &mut W, lit: &LitBigIntExpr) -> fmt::Result {
  out.write_str(&lit.value)
}

pub fn emit_bool_literal<W: fmt::Write>(out: &mut W, lit: &LitBoolExpr) -> fmt::Result {
  out.write_str(if lit.value { "true" } else { "false" })
}

pub fn emit_null_literal<W: fmt::Write>(out: &mut W) -> fmt::Result {
  out.write_str("null")
}

pub fn emit_number_literal<W: fmt::Write>(
  out: &mut W,
  value: JsNumber,
  needs_property_access_escape: bool,
) -> fmt::Result {
  let rendered = value.to_string();
  out.write_str(&rendered)?;
  if needs_property_access_escape && requires_trailing_dot(&rendered) {
    out.write_char('.')?;
  }
  Ok(())
}

pub fn emit_regex_literal<W: fmt::Write>(out: &mut W, lit: &LitRegexExpr) -> fmt::Result {
  out.write_str(&lit.value)
}

pub fn emit_string_literal_expr<W: fmt::Write>(
  out: &mut W,
  lit: &LitStrExpr,
  mode: EmitMode,
) -> fmt::Result {
  emit_string_literal(out, &lit.value, mode)
}

pub fn emit_template_literal<W: fmt::Write, F>(
  out: &mut W,
  parts: &[LitTemplatePart],
  mut emit_expr: F,
) -> fmt::Result
where
  F: FnMut(&mut W, &Node<Expr>) -> fmt::Result,
{
  out.write_char('`')?;
  for part in parts {
    match part {
      LitTemplatePart::String(value) => emit_template_part(out, value)?,
      LitTemplatePart::Substitution(expr) => {
        out.write_str("${")?;
        emit_expr(out, expr)?;
        out.write_char('}')?;
      }
    }
  }
  out.write_char('`')
}

fn requires_trailing_dot(rendered: &str) -> bool {
  let mut bytes = rendered.as_bytes();
  if bytes.starts_with(b"-") {
    bytes = &bytes[1..];
  }
  bytes.iter().all(|b| b.is_ascii_digit())
}
