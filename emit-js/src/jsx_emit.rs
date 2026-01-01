use crate::emitter::{with_node_context, EmitResult, Emitter};
use crate::expr_js::{emit_expr as emit_expr_js, ExprCtx};
use parse_js::ast::expr::jsx::{
  JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxExprContainer, JsxMemberExpr,
  JsxName, JsxSpreadAttr, JsxText,
};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;

pub(crate) fn emit_jsx_elem(em: &mut Emitter, elem: &Node<JsxElem>) -> EmitResult {
  with_node_context(elem.loc, || match &elem.stx.name {
    Some(name) => {
      em.write_punct("<");
      emit_jsx_elem_name(em, name)?;
      for attr in &elem.stx.attributes {
        em.write_space();
        emit_jsx_attr(em, attr)?;
      }
      if elem.stx.children.is_empty() {
        em.write_str("/>");
        return Ok(());
      }
      em.write_punct(">");
      emit_jsx_children(em, &elem.stx.children)?;
      em.write_str("</");
      emit_jsx_elem_name(em, name)?;
      em.write_punct(">");
      Ok(())
    }
    None => {
      em.write_str("<>");
      emit_jsx_children(em, &elem.stx.children)?;
      em.write_str("</>");
      Ok(())
    }
  })
}

fn emit_jsx_expr_container(em: &mut Emitter, container: &Node<JsxExprContainer>) -> EmitResult {
  with_node_context(container.loc, || {
    if is_empty_jsx_expr_placeholder(&container.stx.value) {
      em.write_str("{}");
      return Ok(());
    }

    em.write_punct("{");
    if container.stx.spread {
      em.write_punct("...");
    }
    emit_expr_js(em, &container.stx.value, ExprCtx::Default)?;
    em.write_punct("}");
    Ok(())
  })
}

fn emit_jsx_member_expr(em: &mut Emitter, member: &Node<JsxMemberExpr>) -> EmitResult {
  with_node_context(member.loc, || {
    em.write_str(&member.stx.base.stx.name);
    for segment in &member.stx.path {
      em.write_punct(".");
      em.write_str(segment);
    }
    Ok(())
  })
}

fn emit_jsx_name(em: &mut Emitter, name: &Node<JsxName>) -> EmitResult {
  with_node_context(name.loc, || {
    if let Some(namespace) = &name.stx.namespace {
      em.write_str(namespace);
      em.write_punct(":");
    }
    em.write_str(&name.stx.name);
    Ok(())
  })
}

fn emit_jsx_elem_name(em: &mut Emitter, name: &JsxElemName) -> EmitResult {
  match name {
    JsxElemName::Name(name) => emit_jsx_name(em, name),
    JsxElemName::Id(id) => {
      em.write_str(&id.stx.name);
      Ok(())
    }
    JsxElemName::Member(member) => emit_jsx_member_expr(em, member),
  }
}

fn emit_jsx_attr(em: &mut Emitter, attr: &JsxAttr) -> EmitResult {
  match attr {
    JsxAttr::Named { name, value } => {
      emit_jsx_name(em, name)?;
      if let Some(value) = value {
        em.write_punct("=");
        emit_jsx_attr_value(em, value)?;
      }
      Ok(())
    }
    JsxAttr::Spread { value } => emit_jsx_spread_attr(em, value),
  }
}

fn emit_jsx_spread_attr(em: &mut Emitter, attr: &Node<JsxSpreadAttr>) -> EmitResult {
  with_node_context(attr.loc, || {
    em.write_str("{...");
    emit_expr_js(em, &attr.stx.value, ExprCtx::Default)?;
    em.write_punct("}");
    Ok(())
  })
}

fn emit_jsx_attr_value(em: &mut Emitter, value: &JsxAttrVal) -> EmitResult {
  match value {
    JsxAttrVal::Text(text) => with_node_context(text.loc, || {
      // Reuse the public fmt-based escape helper to keep escaping semantics in sync.
      crate::jsx::escape_jsx_string_literal(em, &text.stx.value)
    }),
    JsxAttrVal::Expression(expr) => emit_jsx_expr_container(em, expr),
    JsxAttrVal::Element(elem) => emit_jsx_elem(em, elem),
  }
}

fn emit_jsx_child_text(em: &mut Emitter, text: &Node<JsxText>) -> EmitResult {
  with_node_context(text.loc, || {
    crate::jsx::escape_jsx_child_text(em, &text.stx.value)
  })
}

fn emit_jsx_child(em: &mut Emitter, child: &JsxElemChild) -> EmitResult {
  match child {
    JsxElemChild::Element(elem) => emit_jsx_elem(em, elem),
    JsxElemChild::Expr(expr) => emit_jsx_expr_container(em, expr),
    JsxElemChild::Text(text) => emit_jsx_child_text(em, text),
  }
}

fn emit_jsx_children(em: &mut Emitter, children: &[JsxElemChild]) -> EmitResult {
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
        with_node_context(text.loc, || {
          crate::jsx::escape_jsx_child_text(em, &combined)
        })?;
      }
      child => {
        emit_jsx_child(em, child)?;
        idx += 1;
      }
    }
  }
  Ok(())
}

fn is_empty_jsx_expr_placeholder(expr: &Node<Expr>) -> bool {
  expr.loc.is_empty() && matches!(expr.stx.as_ref(), Expr::Id(id) if id.stx.name.is_empty())
}
