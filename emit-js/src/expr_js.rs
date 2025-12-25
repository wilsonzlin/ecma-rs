use crate::emitter::Emitter;
use crate::expr::{EmitError, EmitResult};
use crate::ts_type::emit_type_expr;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType};
use parse_js::ast::expr::lit::LitObjExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::node::Node;
use parse_js::ast::type_expr::TypeExpr;

/// Context for expression emission. Currently only influences statement-level
/// wrapping handled by callers, but kept explicit so integration with a
/// full expression emitter can preserve intent.
#[derive(Clone, Copy)]
pub enum ExprCtx {
  Default,
  /// Expression is in statement position (e.g. `foo;`).
  Stmt,
  /// Expression appears as the RHS of `export default`.
  ExportDefault,
}

/// Temporary adapter that delegates to the existing fmt-based expression
/// emitter until the dedicated `Emitter`-backed expression printer is
/// available. Limited object literal support is implemented directly to cover
/// module import/export attributes and expression statements starting with an
/// object.
pub fn emit_expr(em: &mut Emitter, expr: &Node<Expr>, _ctx: ExprCtx) -> EmitResult {
  match expr.stx.as_ref() {
    Expr::LitObj(obj) => emit_lit_obj(em, obj),
    _ => emit_expr_via_fmt(em, expr),
  }
}

fn emit_expr_via_fmt(em: &mut Emitter, expr: &Node<Expr>) -> EmitResult {
  let mut buf = String::new();
  let mut emit_type = |out: &mut String, ty: &Node<TypeExpr>| emit_type_expr(out, ty);
  crate::expr::emit_expr(&mut buf, expr, &mut emit_type)?;
  em.write_str(&buf);
  Ok(())
}

fn emit_lit_obj(em: &mut Emitter, obj: &Node<LitObjExpr>) -> EmitResult {
  em.write_punct("{");
  for (idx, member) in obj.stx.members.iter().enumerate() {
    if idx > 0 {
      em.write_punct(",");
    }
    emit_obj_member(em, member)?;
  }
  em.write_punct("}");
  Ok(())
}

fn emit_obj_member(em: &mut Emitter, member: &Node<ObjMember>) -> EmitResult {
  match &member.stx.typ {
    ObjMemberType::Valued { key, val } => emit_obj_valued_member(em, key, val),
    ObjMemberType::Shorthand { id } => {
      em.write_identifier(&id.stx.name);
      Ok(())
    }
    ObjMemberType::Rest { val } => {
      em.write_punct("...");
      emit_expr(em, val, ExprCtx::Default)
    }
  }
}

fn emit_obj_valued_member(
  em: &mut Emitter,
  key: &ClassOrObjKey,
  val: &ClassOrObjVal,
) -> EmitResult {
  match val {
    ClassOrObjVal::Prop(init) => {
      emit_class_or_object_key(em, key)?;
      if let Some(init) = init {
        em.write_punct(":");
        emit_expr(em, init, ExprCtx::Default)?;
      }
      Ok(())
    }
    ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_) | ClassOrObjVal::Method(_) => {
      Err(EmitError::Unsupported("object method emission not yet supported"))
    }
    ClassOrObjVal::IndexSignature(_) | ClassOrObjVal::StaticBlock(_) => Err(EmitError::Unsupported(
      "object member kind not supported in emitter",
    )),
  }
}

fn emit_class_or_object_key(em: &mut Emitter, key: &ClassOrObjKey) -> EmitResult {
  match key {
    ClassOrObjKey::Direct(name) => {
      em.write_str(&name.stx.key);
      Ok(())
    }
    ClassOrObjKey::Computed(expr) => {
      em.write_punct("[");
      emit_expr(em, expr, ExprCtx::Default)?;
      em.write_punct("]");
      Ok(())
    }
  }
}
