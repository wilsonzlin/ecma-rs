use std::fmt;

use parse_js::ast::expr::jsx::{
  JsxAttr,
  JsxAttrVal,
  JsxElem,
  JsxElemChild,
  JsxElemName,
  JsxExprContainer,
  JsxMemberExpr,
  JsxName,
  JsxSpreadAttr,
  JsxText,
};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;

use crate::expr::EmitResult;

pub fn emit_jsx_elem<W: fmt::Write>(out: &mut W, elem: &Node<JsxElem>) -> EmitResult {
  match &elem.stx.name {
    Some(name) => {
      out.write_char('<')?;
      emit_jsx_elem_name(out, name)?;
      for attr in &elem.stx.attributes {
        out.write_char(' ')?;
        emit_jsx_attr(out, attr)?;
      }
      if elem.stx.children.is_empty() {
        out.write_str("/>")?;
        return Ok(());
      }
      out.write_char('>')?;
      for child in &elem.stx.children {
        emit_jsx_child(out, child)?;
      }
      out.write_str("</")?;
      emit_jsx_elem_name(out, name)?;
      out.write_char('>')?;
      Ok(())
    }
    None => {
      out.write_str("<>")?;
      for child in &elem.stx.children {
        emit_jsx_child(out, child)?;
      }
      out.write_str("</>")?;
      Ok(())
    }
  }
}

pub fn emit_jsx_expr_container<W: fmt::Write>(
  out: &mut W,
  container: &Node<JsxExprContainer>,
) -> EmitResult {
  if is_empty_jsx_expr_placeholder(&container.stx.value) {
    out.write_str("{}")?;
    return Ok(());
  }

  out.write_char('{')?;
  if container.stx.spread {
    out.write_str("...")?;
  }
  let mut emit_type = |out: &mut W, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
  crate::expr::emit_expr(out, &container.stx.value, &mut emit_type)?;
  out.write_char('}')?;
  Ok(())
}

pub fn emit_jsx_member_expr<W: fmt::Write>(out: &mut W, member: &Node<JsxMemberExpr>) -> EmitResult {
  out.write_str(&member.stx.base.stx.name)?;
  for segment in &member.stx.path {
    out.write_char('.')?;
    out.write_str(segment)?;
  }
  Ok(())
}

pub fn emit_jsx_name<W: fmt::Write>(out: &mut W, name: &Node<JsxName>) -> EmitResult {
  if let Some(namespace) = &name.stx.namespace {
    out.write_str(namespace)?;
    out.write_char(':')?;
  }
  out.write_str(&name.stx.name)?;
  Ok(())
}

pub fn emit_jsx_elem_name<W: fmt::Write>(out: &mut W, name: &JsxElemName) -> EmitResult {
  match name {
    JsxElemName::Name(name) => emit_jsx_name(out, name),
    JsxElemName::Id(id) => {
      out.write_str(&id.stx.name)?;
      Ok(())
    }
    JsxElemName::Member(member) => emit_jsx_member_expr(out, member),
  }
}

pub fn emit_jsx_attr<W: fmt::Write>(out: &mut W, attr: &JsxAttr) -> EmitResult {
  match attr {
    JsxAttr::Named { name, value } => {
      emit_jsx_name(out, name)?;
      if let Some(value) = value {
        out.write_char('=')?;
        emit_jsx_attr_value(out, value)?;
      }
      Ok(())
    }
    JsxAttr::Spread { value } => emit_jsx_spread_attr(out, value),
  }
}

pub fn emit_jsx_spread_attr<W: fmt::Write>(out: &mut W, attr: &Node<JsxSpreadAttr>) -> EmitResult {
  out.write_str("{...")?;
  let mut emit_type = |out: &mut W, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
  crate::expr::emit_expr(out, &attr.stx.value, &mut emit_type)?;
  out.write_char('}')?;
  Ok(())
}

pub fn emit_jsx_attr_value<W: fmt::Write>(out: &mut W, value: &JsxAttrVal) -> EmitResult {
  match value {
    JsxAttrVal::Text(text) => escape_jsx_string_literal(out, &text.stx.value),
    JsxAttrVal::Expression(expr) => emit_jsx_expr_container(out, expr),
    JsxAttrVal::Element(elem) => emit_jsx_elem(out, elem),
  }
}

pub fn emit_jsx_expression_text<W: fmt::Write>(out: &mut W, text: &Node<JsxText>) -> EmitResult {
  escape_jsx_child_text(out, &text.stx.value)
}

pub fn escape_jsx_string_literal<W: fmt::Write>(out: &mut W, value: &str) -> EmitResult {
  out.write_char('"')?;
  for ch in value.chars() {
    match ch {
      '"' => out.write_str("&quot;")?,
      '\u{0}' => out.write_str("&#0;")?,
      '\u{1}'..='\u{1F}' | '\u{85}' | '\u{2028}' | '\u{2029}' => {
        write!(out, "&#x{:X};", ch as u32)?;
      }
      _ => out.write_char(ch)?,
    }
  }
  out.write_char('"')?;
  Ok(())
}

pub fn escape_jsx_child_text<W: fmt::Write>(out: &mut W, value: &str) -> EmitResult {
  for ch in value.chars() {
    match ch {
      '<' => out.write_str("&lt;")?,
      '>' => out.write_str("&gt;")?,
      '{' => out.write_str("&#123;")?,
      '}' => out.write_str("&#125;")?,
      _ => out.write_char(ch)?,
    }
  }
  Ok(())
}

fn emit_jsx_child<W: fmt::Write>(out: &mut W, child: &JsxElemChild) -> EmitResult {
  match child {
    JsxElemChild::Element(elem) => emit_jsx_elem(out, elem),
    JsxElemChild::Expr(expr) => emit_jsx_expr_container(out, expr),
    JsxElemChild::Text(text) => escape_jsx_child_text(out, &text.stx.value),
  }
}

fn is_empty_jsx_expr_placeholder(expr: &Node<Expr>) -> bool {
  expr.loc.is_empty()
    && matches!(expr.stx.as_ref(), Expr::Id(id) if id.stx.name.is_empty())
}
