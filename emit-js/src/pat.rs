use parse_js::ast::class_or_object::ClassOrObjKey;
use parse_js::ast::expr::pat::{ArrPat, ClassOrFuncName, IdPat, ObjPat, ObjPatProp, Pat};
use parse_js::ast::expr::{Decorator, Expr};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{Accessibility, ParamDecl, PatDecl};
use parse_js::token::TT;

use crate::emit_string_literal_double_quoted;
use crate::emitter::EmitResult;
use crate::expr::emit_expr_with_emitter;
use crate::Emitter;

fn emit_expr(out: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  emit_expr_with_emitter(out, expr)
}

fn emit_decorators(out: &mut Emitter, decorators: &[Node<Decorator>]) -> EmitResult {
  for decorator in decorators {
    out.write_punct("@");
    emit_expr(out, &decorator.stx.expression)?;
    out.write_space();
  }
  Ok(())
}

fn emit_accessibility(out: &mut Emitter, accessibility: Accessibility) {
  match accessibility {
    Accessibility::Public => out.write_keyword("public"),
    Accessibility::Private => out.write_keyword("private"),
    Accessibility::Protected => out.write_keyword("protected"),
  }
}

pub fn emit_pat(out: &mut Emitter, pat: &Node<Pat>) -> EmitResult {
  match pat.stx.as_ref() {
    Pat::Arr(arr) => emit_array_pattern(out, arr),
    Pat::Id(id) => emit_id_pattern(out, id),
    Pat::Obj(obj) => emit_object_pattern(out, obj),
    Pat::AssignTarget(expr) => emit_expr(out, expr),
  }
}

pub fn emit_pat_decl(out: &mut Emitter, decl: &Node<PatDecl>) -> EmitResult {
  emit_pat(out, &decl.stx.pat)
}

pub fn emit_param_decl(out: &mut Emitter, decl: &Node<ParamDecl>) -> EmitResult {
  emit_decorators(out, &decl.stx.decorators)?;
  if let Some(accessibility) = decl.stx.accessibility {
    emit_accessibility(out, accessibility);
  }
  if decl.stx.readonly {
    out.write_keyword("readonly");
  }
  if decl.stx.rest {
    out.write_punct("...");
  }
  emit_pat_decl(out, &decl.stx.pattern)?;
  if decl.stx.optional {
    out.write_punct("?");
  }
  if let Some(annotation) = &decl.stx.type_annotation {
    out.write_punct(":");
    if out.mode() == crate::EmitMode::Canonical {
      out.write_space();
    }
    crate::emit_ts_type(out, annotation)?;
  }
  if let Some(default) = &decl.stx.default_value {
    out.write_punct("=");
    emit_expr(out, default)?;
  }
  Ok(())
}

pub fn emit_class_or_func_name(out: &mut Emitter, name: &Node<ClassOrFuncName>) -> EmitResult {
  out.write_identifier(&name.stx.name);
  Ok(())
}

pub(crate) fn emit_id_pattern(out: &mut Emitter, id: &Node<IdPat>) -> EmitResult {
  out.write_identifier(&id.stx.name);
  Ok(())
}

pub(crate) fn emit_array_pattern(out: &mut Emitter, arr: &Node<ArrPat>) -> EmitResult {
  out.write_punct("[");
  for (index, elem) in arr.stx.elements.iter().enumerate() {
    if index > 0 {
      out.write_punct(",");
    }
    if let Some(elem) = elem {
      emit_pat(out, &elem.target)?;
      if let Some(default) = &elem.default_value {
        out.write_punct("=");
        emit_expr(out, default)?;
      }
    }
  }
  if let Some(rest) = &arr.stx.rest {
    if !arr.stx.elements.is_empty() {
      out.write_punct(",");
    }
    out.write_punct("...");
    emit_pat(out, rest)?;
  }
  out.write_punct("]");
  Ok(())
}

pub(crate) fn emit_object_pattern(out: &mut Emitter, obj: &Node<ObjPat>) -> EmitResult {
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
    emit_pat(out, rest)?;
  }
  out.write_punct("}");
  Ok(())
}

pub(crate) fn emit_class_or_object_key(out: &mut Emitter, key: &ClassOrObjKey) -> EmitResult {
  match key {
    ClassOrObjKey::Direct(name) => {
      match name.stx.tt {
        TT::LiteralString => {
          let mut buf = Vec::new();
          emit_string_literal_double_quoted(&mut buf, &name.stx.key);
          out.write_str(std::str::from_utf8(&buf).expect("string literal escape output is UTF-8"));
        }
        TT::LiteralNumber | TT::LiteralNumberBin | TT::LiteralNumberHex | TT::LiteralNumberOct => {
          out.write_number(&name.stx.key)
        }
        tt if tt == TT::Identifier || tt.is_keyword() => out.write_identifier(&name.stx.key),
        _ => out.write_str(&name.stx.key),
      }
      Ok(())
    }
    ClassOrObjKey::Computed(expr) => {
      out.write_punct("[");
      emit_expr(out, expr)?;
      out.write_punct("]");
      Ok(())
    }
  }
}

fn emit_obj_pat_prop(out: &mut Emitter, prop: &Node<ObjPatProp>) -> EmitResult {
  emit_class_or_object_key(out, &prop.stx.key)?;
  if !prop.stx.shorthand {
    out.write_punct(":");
    emit_pat(out, &prop.stx.target)?;
  }
  if let Some(default) = &prop.stx.default_value {
    out.write_punct("=");
    emit_expr(out, default)?;
  }
  Ok(())
}
