use parse_js::ast::expr::jsx::{
  JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxExprContainer, JsxMemberExpr,
  JsxName, JsxSpreadAttr, JsxText,
};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;

use crate::emitter::{with_node_context, EmitResult};
use crate::Emitter;

pub fn emit_jsx_elem(out: &mut Emitter, elem: &Node<JsxElem>) -> EmitResult {
  with_node_context(elem.loc, || match &elem.stx.name {
    Some(name) => {
      out.write_punct("<");
      emit_jsx_elem_name(out, name)?;
      for attr in &elem.stx.attributes {
        out.write_space();
        emit_jsx_attr(out, attr)?;
      }
      if elem.stx.children.is_empty() {
        out.write_punct("/>");
        return Ok(());
      }
      out.write_punct(">");
      for child in &elem.stx.children {
        emit_jsx_child(out, child)?;
      }
      out.write_punct("</");
      emit_jsx_elem_name(out, name)?;
      out.write_punct(">");
      Ok(())
    }
    None => {
      out.write_punct("<>");
      for child in &elem.stx.children {
        emit_jsx_child(out, child)?;
      }
      out.write_punct("</>");
      Ok(())
    }
  })
}

pub fn emit_jsx_expr_container(out: &mut Emitter, container: &Node<JsxExprContainer>) -> EmitResult {
  with_node_context(container.loc, || {
    if is_empty_jsx_expr_placeholder(&container.stx.value) {
      out.write_punct("{}");
      return Ok(());
    }

    out.write_punct("{");
    if container.stx.spread {
      out.write_punct("...");
    }
    let mut emit_type = |out: &mut Emitter, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
    crate::expr::emit_expr(out, &container.stx.value, &mut emit_type)?;
    out.write_punct("}");
    Ok(())
  })
}

pub fn emit_jsx_member_expr(out: &mut Emitter, member: &Node<JsxMemberExpr>) -> EmitResult {
  with_node_context(member.loc, || {
    out.write_identifier(&member.stx.base.stx.name);
    for segment in &member.stx.path {
      out.write_punct(".");
      out.write_identifier(segment);
    }
    Ok(())
  })
}

pub fn emit_jsx_name(out: &mut Emitter, name: &Node<JsxName>) -> EmitResult {
  with_node_context(name.loc, || {
    if let Some(namespace) = &name.stx.namespace {
      out.write_identifier(namespace);
      out.write_punct(":");
    }
    out.write_identifier(&name.stx.name);
    Ok(())
  })
}

pub fn emit_jsx_elem_name(out: &mut Emitter, name: &JsxElemName) -> EmitResult {
  match name {
    JsxElemName::Name(name) => emit_jsx_name(out, name),
    JsxElemName::Id(id) => {
      out.write_identifier(&id.stx.name);
      Ok(())
    }
    JsxElemName::Member(member) => emit_jsx_member_expr(out, member),
  }
}

pub fn emit_jsx_attr(out: &mut Emitter, attr: &JsxAttr) -> EmitResult {
  match attr {
    JsxAttr::Named { name, value } => {
      emit_jsx_name(out, name)?;
      if let Some(value) = value {
        out.write_punct("=");
        emit_jsx_attr_value(out, value)?;
      }
      Ok(())
    }
    JsxAttr::Spread { value } => emit_jsx_spread_attr(out, value),
  }
}

pub fn emit_jsx_spread_attr(out: &mut Emitter, attr: &Node<JsxSpreadAttr>) -> EmitResult {
  with_node_context(attr.loc, || {
    out.write_punct("{");
    out.write_punct("...");
    let mut emit_type = |out: &mut Emitter, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
    crate::expr::emit_expr(out, &attr.stx.value, &mut emit_type)?;
    out.write_punct("}");
    Ok(())
  })
}

pub fn emit_jsx_attr_value(out: &mut Emitter, value: &JsxAttrVal) -> EmitResult {
  match value {
    JsxAttrVal::Text(text) => escape_jsx_string_literal(out, &text.stx.value),
    JsxAttrVal::Expression(expr) => emit_jsx_expr_container(out, expr),
    JsxAttrVal::Element(elem) => emit_jsx_elem(out, elem),
  }
}

pub fn emit_jsx_expression_text(out: &mut Emitter, text: &Node<JsxText>) -> EmitResult {
  with_node_context(text.loc, || escape_jsx_child_text(out, &text.stx.value))
}

pub fn escape_jsx_string_literal(out: &mut Emitter, value: &str) -> EmitResult {
  out.write_raw_byte(b'"');
  let mut plain = String::new();
  let flush_plain = |out: &mut Emitter, plain: &mut String| {
    if plain.is_empty() {
      return;
    }
    out.write_raw_str(plain);
    plain.clear();
  };
  for ch in value.chars() {
    match ch {
      '"' => {
        flush_plain(out, &mut plain);
        out.write_raw_str("&quot;");
      }
      '\u{0}' => {
        flush_plain(out, &mut plain);
        out.write_raw_str("&#0;");
      }
      '\u{1}'..='\u{1F}' | '\u{85}' | '\u{2028}' | '\u{2029}' => {
        flush_plain(out, &mut plain);
        let escape = format!("&#x{:X};", ch as u32);
        out.write_raw_str(&escape);
      }
      ch => plain.push(ch),
    }
  }
  flush_plain(out, &mut plain);
  out.write_raw_byte(b'"');
  Ok(())
}

pub fn escape_jsx_child_text(out: &mut Emitter, value: &str) -> EmitResult {
  let mut plain = String::new();
  let flush_plain = |out: &mut Emitter, plain: &mut String| {
    if plain.is_empty() {
      return;
    }
    out.write_raw_str(plain);
    plain.clear();
  };
  for ch in value.chars() {
    match ch {
      '<' => {
        flush_plain(out, &mut plain);
        out.write_raw_str("&lt;");
      }
      '>' => {
        flush_plain(out, &mut plain);
        out.write_raw_str("&gt;");
      }
      '{' => {
        flush_plain(out, &mut plain);
        out.write_raw_str("&#123;");
      }
      '}' => {
        flush_plain(out, &mut plain);
        out.write_raw_str("&#125;");
      }
      ch => plain.push(ch),
    }
  }
  flush_plain(out, &mut plain);
  Ok(())
}

fn emit_jsx_child(out: &mut Emitter, child: &JsxElemChild) -> EmitResult {
  match child {
    JsxElemChild::Element(elem) => emit_jsx_elem(out, elem),
    JsxElemChild::Expr(expr) => emit_jsx_expr_container(out, expr),
    JsxElemChild::Text(text) => escape_jsx_child_text(out, &text.stx.value),
  }
}

fn is_empty_jsx_expr_placeholder(expr: &Node<Expr>) -> bool {
  expr.loc.is_empty() && matches!(expr.stx.as_ref(), Expr::Id(id) if id.stx.name.is_empty())
}
