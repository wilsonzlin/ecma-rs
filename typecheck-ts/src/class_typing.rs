//! Class member typing helpers over HIR only.
//!
//! Instance/static class shapes are lowered from [`hir_js::DefTypeInfo::Class`]
//! / [`hir_js::ClassMemberSig`] in [`crate::check::decls::HirDeclLowerer`].
//! This module owns HIR-side lookup paths for value-side field annotations
//! (replacing the former AST class-body walk).

use diagnostics::TextRange;
use hir_js::{ClassMemberSig, DefId, DefTypeInfo, LowerResult, TypeExprId};

/// Value-side field annotation on a [`ClassMemberSig`], if present.
///
/// Includes ordinary/private fields, ambient properties, and constructor
/// parameter properties modeled as extra field signatures.
pub(crate) fn class_member_field_type_expr(member: &ClassMemberSig) -> Option<TypeExprId> {
  member.field_type_annotation()
}

/// Resolve `(owning_class_def, type_expr)` for a span that matches a class
/// member field annotation in HIR.
///
/// Prefer [`hir_js::DefData::declared_type`] (per-field arenas) when a field
/// `DefId` exists; use this for ambient class properties and constructor
/// parameter properties that only appear on the owning class's
/// [`DefTypeInfo::Class`] member list.
pub(crate) fn hir_class_member_type_at_span(
  lowered: &LowerResult,
  target: TextRange,
) -> Option<(DefId, TypeExprId)> {
  let mut matches: Vec<(DefId, TypeExprId)> = Vec::new();
  for def in lowered.defs.iter() {
    let Some(DefTypeInfo::Class { members, .. }) = def.type_info.as_ref() else {
      continue;
    };
    for member in members.iter() {
      if member.span != target {
        continue;
      }
      if let Some(ty) = class_member_field_type_expr(member) {
        matches.push((def.id, ty));
      }
    }
  }
  matches.sort_by_key(|(id, _)| id.0);
  matches.first().copied()
}

/// `class C<T>` type params for an annotation owner (the class itself, or a
/// child field/method/accessor). Used when lowering per-def arenas that do not
/// own the class type-parameter list.
pub(crate) fn enclosing_class_type_params(
  lowered: &LowerResult,
  owner: DefId,
) -> Option<(DefId, Vec<hir_js::TypeParamId>)> {
  let mut current = lowered.def(owner)?;
  if let Some(DefTypeInfo::Class { type_params, .. }) = current.type_info.as_ref() {
    if !type_params.is_empty() {
      return Some((owner, type_params.clone()));
    }
  }
  while let Some(parent_id) = current.parent {
    let parent = lowered.def(parent_id)?;
    if let Some(DefTypeInfo::Class { type_params, .. }) = parent.type_info.as_ref() {
      if type_params.is_empty() {
        return None;
      }
      return Some((parent_id, type_params.clone()));
    }
    current = parent;
  }
  None
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::check::decls::HirDeclLowerer;
  use std::collections::HashMap;
  use std::sync::Arc;
  use types_ts_interned::TypeStore;

  #[test]
  fn class_t_field_ann_lowers_without_tc2008() {
    let src = "class C<T> {\n  #foo: T;\n  constructor(t: T) { this.#foo = t; }\n}\n";
    let lowered = hir_js::lower_from_source_with_kind(hir_js::FileKind::Ts, src).unwrap();
    let field = lowered
      .defs
      .iter()
      .find(|d| lowered.names.resolve(d.name) == Some("#foo"))
      .unwrap();
    let ann = field.declared_type.expect("declared_type");
    let enclosing = enclosing_class_type_params(&lowered, field.id);
    assert!(enclosing.is_some(), "expected enclosing class type params");
    let store = Arc::new(TypeStore::new());
    let mut diagnostics = Vec::new();
    let mut lowerer = HirDeclLowerer::new(
      Arc::clone(&store),
      &lowered.types,
      None,
      HashMap::new(),
      diagnostics::FileId(0),
      None,
      Default::default(),
      &mut diagnostics,
      None,
      None,
      None,
      None,
      None,
      None,
    );
    let (cid, params) = enclosing.unwrap();
    let _ty = lowerer.lower_declared_type_with_class_params(
      field.id,
      ann,
      Some((cid, params.as_slice())),
      &lowered.names,
    );
    assert!(
      !diagnostics.iter().any(|d| d.code.as_str() == "TC2008"),
      "diags={diagnostics:?}"
    );

    let class = lowered
      .defs
      .iter()
      .find(|d| matches!(d.type_info, Some(DefTypeInfo::Class { .. })))
      .unwrap();
    let mut diagnostics2 = Vec::new();
    let mut lowerer2 = HirDeclLowerer::new(
      Arc::clone(&store),
      &lowered.types,
      None,
      HashMap::new(),
      diagnostics::FileId(0),
      None,
      Default::default(),
      &mut diagnostics2,
      None,
      None,
      None,
      None,
      None,
      None,
    );
    let info = class.type_info.as_ref().unwrap();
    let _ = lowerer2.lower_type_info(class.id, info, &lowered.names);
    assert!(
      !diagnostics2.iter().any(|d| d.code.as_str() == "TC2008"),
      "class lower diags={diagnostics2:?}"
    );
  }
}
