use std::fmt::{self, Write};

use parse_js::ast::expr::jsx::{
  JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxExprContainer, JsxMemberExpr,
  JsxName, JsxSpreadAttr,
};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;

use crate::emitter::{with_node_context, EmitResult};

pub fn emit_jsx_elem<W: fmt::Write>(out: &mut W, elem: &Node<JsxElem>) -> EmitResult {
  with_node_context(elem.loc, || match &elem.stx.name {
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
      emit_jsx_children(out, &elem.stx.children)?;
      out.write_str("</")?;
      emit_jsx_elem_name(out, name)?;
      out.write_char('>')?;
      Ok(())
    }
    None => {
      out.write_str("<>")?;
      emit_jsx_children(out, &elem.stx.children)?;
      out.write_str("</>")?;
      Ok(())
    }
  })
}

pub fn emit_jsx_expr_container<W: fmt::Write>(
  out: &mut W,
  container: &Node<JsxExprContainer>,
) -> EmitResult {
  with_node_context(container.loc, || {
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
  })
}

pub fn emit_jsx_member_expr<W: fmt::Write>(
  out: &mut W,
  member: &Node<JsxMemberExpr>,
) -> EmitResult {
  with_node_context(member.loc, || {
    out.write_str(&member.stx.base.stx.name)?;
    for segment in &member.stx.path {
      out.write_char('.')?;
      out.write_str(segment)?;
    }
    Ok(())
  })
}

pub fn emit_jsx_name<W: fmt::Write>(out: &mut W, name: &Node<JsxName>) -> EmitResult {
  with_node_context(name.loc, || {
    if let Some(namespace) = &name.stx.namespace {
      out.write_str(namespace)?;
      out.write_char(':')?;
    }
    out.write_str(&name.stx.name)?;
    Ok(())
  })
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
  with_node_context(attr.loc, || {
    out.write_str("{...")?;
    let mut emit_type = |out: &mut W, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
    crate::expr::emit_expr(out, &attr.stx.value, &mut emit_type)?;
    out.write_char('}')?;
    Ok(())
  })
}

pub fn emit_jsx_attr_value<W: fmt::Write>(out: &mut W, value: &JsxAttrVal) -> EmitResult {
  match value {
    JsxAttrVal::Text(text) => {
      with_node_context(text.loc, || escape_jsx_string_literal(out, &text.stx.value))
    }
    JsxAttrVal::Expression(expr) => emit_jsx_expr_container(out, expr),
    JsxAttrVal::Element(elem) => emit_jsx_elem(out, elem),
  }
}

pub fn escape_jsx_string_literal<W: fmt::Write>(out: &mut W, value: &str) -> EmitResult {
  let mut escaped = String::with_capacity(value.len() + 2);
  escaped.push('"');
  for ch in value.chars() {
    match ch {
      '"' => escaped.push_str("&quot;"),
      '\u{0}' => escaped.push_str("&#0;"),
      '\u{1}'..='\u{1F}' | '\u{85}' | '\u{2028}' | '\u{2029}' => {
        write!(&mut escaped, "&#x{:X};", ch as u32)?;
      }
      _ => escaped.push(ch),
    }
  }
  escaped.push('"');
  out.write_str(&escaped)?;
  Ok(())
}

pub fn escape_jsx_child_text<W: fmt::Write>(out: &mut W, value: &str) -> EmitResult {
  let mut escaped = String::with_capacity(value.len());
  for ch in value.chars() {
    match ch {
      '<' => escaped.push_str("&lt;"),
      '>' => escaped.push_str("&gt;"),
      '{' => escaped.push_str("&#123;"),
      '}' => escaped.push_str("&#125;"),
      _ => escaped.push(ch),
    }
  }
  out.write_str(&escaped)?;
  Ok(())
}

fn emit_jsx_child<W: fmt::Write>(out: &mut W, child: &JsxElemChild) -> EmitResult {
  match child {
    JsxElemChild::Element(elem) => emit_jsx_elem(out, elem),
    JsxElemChild::Expr(expr) => emit_jsx_expr_container(out, expr),
    JsxElemChild::Text(text) => escape_jsx_child_text(out, &text.stx.value),
  }
}

fn emit_jsx_children<W: fmt::Write>(out: &mut W, children: &[JsxElemChild]) -> EmitResult {
  let mut idx = 0;
  while idx < children.len() {
    match &children[idx] {
      JsxElemChild::Text(text) => {
        let mut combined = text.stx.value.clone();
        idx += 1;
        while idx < children.len() {
          if let JsxElemChild::Text(next_text) = &children[idx] {
            combined.push_str(&next_text.stx.value);
            idx += 1;
          } else {
            break;
          }
        }
        with_node_context(text.loc, || escape_jsx_child_text(out, &combined))?;
      }
      child => {
        emit_jsx_child(out, child)?;
        idx += 1;
      }
    }
  }
  Ok(())
}

fn is_empty_jsx_expr_placeholder(expr: &Node<Expr>) -> bool {
  expr.loc.is_empty() && matches!(expr.stx.as_ref(), Expr::Id(id) if id.stx.name.is_empty())
}
