use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::{ArrPat, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ParamDecl, PatDecl};

use crate::js_expr::{emit_js_expr, JsEmitError, JsEmitResult};
use crate::Emitter;

pub fn emit_js_pat(out: &mut Emitter, pat: &Node<Pat>) -> JsEmitResult {
  match pat.stx.as_ref() {
    Pat::Arr(arr) => emit_array_pattern(out, arr),
    Pat::Id(id) => emit_id_pattern(out, id),
    Pat::Obj(obj) => emit_object_pattern(out, obj),
    Pat::AssignTarget(expr) => emit_js_expr(out, expr),
  }
}

pub fn emit_js_pat_decl(out: &mut Emitter, decl: &Node<PatDecl>) -> JsEmitResult {
  emit_js_pat(out, &decl.stx.pat)
}

pub fn emit_js_param_decl(out: &mut Emitter, decl: &Node<ParamDecl>) -> JsEmitResult {
  if !decl.stx.decorators.is_empty() {
    return Err(JsEmitError::Unsupported(
      "parameter decorators are not supported by JS emitter",
    ));
  }
  if decl.stx.accessibility.is_some() {
    return Err(JsEmitError::Unsupported(
      "parameter accessibility is not supported by JS emitter",
    ));
  }
  if decl.stx.readonly {
    return Err(JsEmitError::Unsupported(
      "readonly parameters are not supported by JS emitter",
    ));
  }
  if decl.stx.type_annotation.is_some() {
    return Err(JsEmitError::Unsupported(
      "type annotations are not supported by JS emitter",
    ));
  }
  if decl.stx.optional {
    return Err(JsEmitError::Unsupported(
      "optional parameters are not supported by JS emitter",
    ));
  }
  if decl.stx.rest {
    out.write_punct("...");
  }
  emit_js_pat_decl(out, &decl.stx.pattern)?;
  if let Some(default) = &decl.stx.default_value {
    out.write_punct("=");
    emit_js_expr(out, default)?;
  }
  Ok(())
}

pub(crate) fn emit_js_param_list(out: &mut Emitter, params: &[Node<ParamDecl>]) -> JsEmitResult {
  out.write_punct("(");
  for (idx, param) in params.iter().enumerate() {
    if idx > 0 {
      out.write_punct(",");
    }
    emit_js_param_decl(out, param)?;
  }
  out.write_punct(")");
  Ok(())
}

fn emit_id_pattern(out: &mut Emitter, id: &Node<IdPat>) -> JsEmitResult {
  out.write_identifier(&id.stx.name);
  Ok(())
}

fn emit_array_pattern(out: &mut Emitter, arr: &Node<ArrPat>) -> JsEmitResult {
  out.write_punct("[");
  for (index, elem) in arr.stx.elements.iter().enumerate() {
    if index > 0 {
      out.write_punct(",");
    }
    if let Some(elem) = elem {
      emit_js_pat(out, &elem.target)?;
      if let Some(default) = &elem.default_value {
        out.write_punct("=");
        emit_js_expr(out, default)?;
      }
    }
  }
  if let Some(rest) = &arr.stx.rest {
    if !arr.stx.elements.is_empty() {
      out.write_punct(",");
    }
    out.write_punct("...");
    emit_js_pat(out, rest)?;
  }
  out.write_punct("]");
  Ok(())
}

fn emit_object_pattern(out: &mut Emitter, obj: &Node<ObjPat>) -> JsEmitResult {
  out.write_punct("{");
  for (index, prop) in obj.stx.properties.iter().enumerate() {
    if index > 0 {
      out.write_punct(",");
    }
    emit_obj_pat_prop(out, prop)?;
  }
  if let Some(rest) = &obj.stx.rest {
    if !obj.stx.properties.is_empty() {
      out.write_punct(",");
    }
    out.write_punct("...");
    emit_js_pat(out, rest)?;
  }
  out.write_punct("}");
  Ok(())
}

fn emit_class_or_object_key(out: &mut Emitter, key: &ClassOrObjKey) -> JsEmitResult {
  match key {
    ClassOrObjKey::Direct(name) => {
      out.write_str(&name.stx.key);
    }
    ClassOrObjKey::Computed(expr) => {
      out.write_punct("[");
      emit_js_expr(out, expr)?;
      out.write_punct("]");
    }
  }
  Ok(())
}

fn emit_obj_pat_prop(out: &mut Emitter, prop: &Node<ObjPatProp>) -> JsEmitResult {
  emit_class_or_object_key(out, &prop.stx.key)?;
  if !prop.stx.shorthand {
    out.write_punct(":");
    emit_js_pat(out, &prop.stx.target)?;
  }
  if let Some(default) = &prop.stx.default_value {
    out.write_punct("=");
    emit_js_expr(out, default)?;
  }
  Ok(())
}
