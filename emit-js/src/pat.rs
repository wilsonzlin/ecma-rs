use std::fmt;
use std::fmt::Write;

use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::{ArrPat, ClassOrFuncName, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{ParamDecl, PatDecl};
use parse_js::ast::type_expr::TypeExpr;

fn emit_expr<W: fmt::Write>(out: &mut W, expr: &Node<Expr>) -> fmt::Result {
  let mut emit_type = |out: &mut W, ty: &Node<TypeExpr>| crate::emit_type_expr(out, ty);
  crate::expr::emit_expr(out, expr, &mut emit_type).map_err(|_| fmt::Error)
}

pub fn emit_pat<W: Write>(out: &mut W, pat: &Node<Pat>) -> fmt::Result {
  match pat.stx.as_ref() {
    Pat::Arr(arr) => emit_array_pattern(out, arr),
    Pat::Id(id) => emit_id_pattern(out, id),
    Pat::Obj(obj) => emit_object_pattern(out, obj),
    Pat::AssignTarget(expr) => emit_expr(out, expr),
  }
}

pub fn emit_pat_decl<W: Write>(out: &mut W, decl: &Node<PatDecl>) -> fmt::Result {
  emit_pat(out, &decl.stx.pat)
}

pub fn emit_param_decl<W: Write>(out: &mut W, decl: &Node<ParamDecl>) -> fmt::Result {
  if decl.stx.rest {
    out.write_str("...")?;
  }
  emit_pat_decl(out, &decl.stx.pattern)?;
  if decl.stx.optional {
    out.write_char('?')?;
  }
  if let Some(default) = &decl.stx.default_value {
    out.write_char('=')?;
    emit_expr(out, default)?;
  }
  Ok(())
}

#[allow(dead_code)] // Public helper for downstream emitters that need to print standalone class/function names.
pub fn emit_class_or_func_name<W: Write>(out: &mut W, name: &Node<ClassOrFuncName>) -> fmt::Result {
  out.write_str(&name.stx.name)
}

pub(crate) fn emit_id_pattern<W: Write>(out: &mut W, id: &Node<IdPat>) -> fmt::Result {
  out.write_str(&id.stx.name)
}

pub(crate) fn emit_array_pattern<W: Write>(out: &mut W, arr: &Node<ArrPat>) -> fmt::Result {
  out.write_char('[')?;
  for (index, elem) in arr.stx.elements.iter().enumerate() {
    if index > 0 {
      out.write_char(',')?;
    }
    if let Some(elem) = elem {
      emit_pat(out, &elem.target)?;
      if let Some(default) = &elem.default_value {
        out.write_char('=')?;
        emit_expr(out, default)?;
      }
    }
  }
  if let Some(rest) = &arr.stx.rest {
    if !arr.stx.elements.is_empty() {
      out.write_char(',')?;
    }
    out.write_str("...")?;
    emit_pat(out, rest)?;
  }
  out.write_char(']')
}

pub(crate) fn emit_object_pattern<W: Write>(out: &mut W, obj: &Node<ObjPat>) -> fmt::Result {
  out.write_char('{')?;
  for (index, prop) in obj.stx.properties.iter().enumerate() {
    if index > 0 {
      out.write_char(',')?;
    }
    emit_obj_pat_prop(out, prop)?;
  }
  if let Some(rest) = &obj.stx.rest {
    if !obj.stx.properties.is_empty() {
      out.write_char(',')?;
    }
    out.write_str("...")?;
    emit_pat(out, rest)?;
  }
  out.write_char('}')
}

pub(crate) fn emit_class_or_object_key<W: Write>(out: &mut W, key: &ClassOrObjKey) -> fmt::Result {
  match key {
    ClassOrObjKey::Direct(name) => out.write_str(&name.stx.key),
    ClassOrObjKey::Computed(expr) => {
      out.write_char('[')?;
      emit_expr(out, expr)?;
      out.write_char(']')
    }
  }
}

fn emit_obj_pat_prop<W: Write>(out: &mut W, prop: &Node<ObjPatProp>) -> fmt::Result {
  emit_class_or_object_key(out, &prop.stx.key)?;
  if !prop.stx.shorthand {
    out.write_char(':')?;
    emit_pat(out, &prop.stx.target)?;
  }
  if let Some(default) = &prop.stx.default_value {
    out.write_char('=')?;
    emit_expr(out, default)?;
  }
  Ok(())
}
