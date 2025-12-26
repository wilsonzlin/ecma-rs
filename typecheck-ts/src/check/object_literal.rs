use std::cmp::Ordering;
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId, Label, Span, TextRange};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::node::Node;
use parse_js::loc::Loc;
use types_ts_interned::{TypeExpander, TypeId, TypeKind as InternedTypeKind, TypeStore};

use super::super::{
  BodyCheckResult, HirExpr, HirExprKind, HirObjectProperty, ObjectType, ProgramState,
  Span as HirSpan, TypeKind as LegacyTypeKind,
};
use crate::codes;
use crate::type_queries::{PropertyKey, TypeKindSummary, TypeQueries};

/// Check for excess properties on a fresh object literal assignment using the
/// interned type system. Diagnostics are returned for the caller to attach to
/// their result.
pub(crate) fn check_excess_properties(
  store: &Arc<TypeStore>,
  expander: &impl TypeExpander,
  expr: &Node<AstExpr>,
  target_type: TypeId,
  file: FileId,
) -> Vec<Diagnostic> {
  let Some((object_span, props)) = collect_object_literal(file, expr) else {
    return Vec::new();
  };

  if props.is_empty() {
    return Vec::new();
  }

  // Avoid excess property checks when the target is clearly not object-like.
  let queries = TypeQueries::new(Arc::clone(store), expander);
  let evaluated = queries.evaluate(target_type);
  match queries.type_kind(evaluated) {
    TypeKindSummary::Any | TypeKindSummary::Unknown => return Vec::new(),
    TypeKindSummary::Object
    | TypeKindSummary::Union { .. }
    | TypeKindSummary::Intersection { .. }
    | TypeKindSummary::Ref { .. }
    | TypeKindSummary::Mapped => {}
    _ => return Vec::new(),
  }

  match find_excess_properties(&queries, store.as_ref(), evaluated, &props) {
    ExcessCheck::Excess(extras) => extras
      .into_iter()
      .map(|prop| {
        let mut diagnostic = codes::EXCESS_PROPERTY.error(
          format!("excess property '{}' in object literal", prop.name),
          Span::new(file, object_span),
        );
        if let Some(span) = prop.span {
          diagnostic.push_label(Label::secondary(
            Span::new(file, span),
            format!("property '{}' is not allowed here", prop.name),
          ));
        }
        diagnostic
      })
      .collect(),
    _ => Vec::new(),
  }
}

struct LiteralProp {
  name: String,
  span: Option<TextRange>,
}

fn collect_object_literal(
  file: FileId,
  expr: &Node<AstExpr>,
) -> Option<(TextRange, Vec<LiteralProp>)> {
  match expr.stx.as_ref() {
    AstExpr::TypeAssertion(_) => return None,
    AstExpr::LitObj(obj) => {
      let mut props = Vec::new();
      for member in obj.stx.members.iter() {
        match &member.stx.typ {
          ObjMemberType::Valued { key, val } => {
            let ClassOrObjKey::Direct(direct) = key else {
              continue;
            };
            if let ClassOrObjVal::Prop(_) = val {
              props.push(LiteralProp {
                name: direct.stx.key.clone(),
                span: Some(loc_to_range(file, direct.loc)),
              });
            }
          }
          ObjMemberType::Shorthand { id } => props.push(LiteralProp {
            name: id.stx.name.clone(),
            span: Some(loc_to_range(file, id.loc)),
          }),
          ObjMemberType::Rest { .. } => {}
        }
      }
      Some((loc_to_range(file, expr.loc), props))
    }
    _ => None,
  }
}

fn find_excess_properties<'a, E: TypeExpander>(
  queries: &TypeQueries<'_, E>,
  store: &TypeStore,
  target: TypeId,
  props: &'a [LiteralProp],
) -> ExcessCheck<'a> {
  let evaluated = queries.evaluate(target);
  match store.type_kind(evaluated) {
    InternedTypeKind::Union(members) => {
      let mut best: Option<Vec<&LiteralProp>> = None;
      let mut any_allowed = false;
      for member in members.iter() {
        match find_excess_properties(queries, store, *member, props) {
          ExcessCheck::Allowed => {
            any_allowed = true;
            break;
          }
          ExcessCheck::Excess(extras) => {
            let replace = match &best {
              None => true,
              Some(current) => extras.len() < current.len(),
            };
            if replace {
              best = Some(extras);
            }
          }
          ExcessCheck::NotApplicable => {}
        }
      }
      if any_allowed {
        ExcessCheck::Allowed
      } else if let Some(extras) = best {
        ExcessCheck::Excess(extras)
      } else {
        ExcessCheck::NotApplicable
      }
    }
    _ => {
      if !is_object_like(queries, evaluated) {
        return ExcessCheck::NotApplicable;
      }
      if queries.properties_of(evaluated).is_empty() && queries.indexers(evaluated).is_empty() {
        return ExcessCheck::Allowed;
      }
      let mut extras = Vec::new();
      for prop in props.iter() {
        if !property_allowed(queries, evaluated, &prop.name) {
          extras.push(prop);
        }
      }
      if extras.is_empty() {
        ExcessCheck::Allowed
      } else {
        ExcessCheck::Excess(extras)
      }
    }
  }
}

enum ExcessCheck<'a> {
  NotApplicable,
  Allowed,
  Excess(Vec<&'a LiteralProp>),
}

fn is_object_like<E: TypeExpander>(queries: &TypeQueries<'_, E>, ty: TypeId) -> bool {
  matches!(
    queries.type_kind(ty),
    TypeKindSummary::Object
      | TypeKindSummary::Intersection { .. }
      | TypeKindSummary::Ref { .. }
      | TypeKindSummary::Mapped
  )
}

fn property_allowed<E: TypeExpander>(
  queries: &TypeQueries<'_, E>,
  target: TypeId,
  name: &str,
) -> bool {
  let key = if let Ok(num) = name.parse::<i64>() {
    PropertyKey::Number(num)
  } else {
    PropertyKey::String(name.to_string())
  };
  queries.property_type(target, key).is_some()
}

fn loc_to_range(_file: FileId, loc: Loc) -> TextRange {
  let (range, _) = loc.to_diagnostics_range_with_note();
  TextRange::new(range.start, range.end)
}

// Legacy helpers used by the pre-interned pipeline. These are retained for
// compatibility with the existing `Program` implementation while the new
// interned checker evolves.

pub(crate) fn legacy_is_fresh_object_literal(expr: &HirExpr) -> bool {
  matches!(expr.kind, HirExprKind::Object(_))
}

/// Return the contextual type for a property on an object literal when the target type is known.
pub(crate) fn legacy_contextual_property_type(
  state: &mut ProgramState,
  target: TypeId,
  name: &str,
) -> Option<TypeId> {
  match state.type_store.kind(target).clone() {
    LegacyTypeKind::Any | LegacyTypeKind::Unknown => None,
    LegacyTypeKind::Object(obj) => legacy_property_type_from_object(&obj, name),
    LegacyTypeKind::Union(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(ty) = legacy_contextual_property_type(state, member, name) {
          collected.push(ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(state.type_store.union(collected, &state.builtin))
      }
    }
    _ => None,
  }
}

pub(crate) fn legacy_check_excess_properties(
  state: &mut ProgramState,
  expr: &HirExpr,
  target_type: TypeId,
  result: &mut BodyCheckResult,
  file: FileId,
) {
  if !legacy_is_fresh_object_literal(expr) {
    return;
  }
  let HirExprKind::Object(props) = &expr.kind else {
    return;
  };

  if props.is_empty() || target_type == state.builtin.any || target_type == state.builtin.unknown {
    return;
  }

  let LegacyExcessCheck::Excess(excess) = legacy_find_excess_properties(state, target_type, props)
  else {
    return;
  };

  let note = if excess.allowed.is_empty() {
    None
  } else {
    Some(format!("allowed properties: {}", excess.allowed.join(", ")))
  };

  for prop in excess.extras {
    let name = &prop.name;
    let value = &prop.value;
    let mut diagnostic = codes::EXCESS_PROPERTY.error(
      format!("excess property '{}' in object literal", name),
      HirSpan {
        file,
        range: value.span,
      },
    );
    if let Some(note) = &note {
      diagnostic.push_note(note.clone());
    }
    result.diagnostics.push(diagnostic);
  }
}

fn legacy_property_type_from_object(obj: &ObjectType, name: &str) -> Option<TypeId> {
  if let Some(prop) = obj.props.get(name) {
    return Some(prop.typ);
  }
  if name.parse::<usize>().is_ok() {
    obj.number_index.or(obj.string_index)
  } else {
    obj.string_index
  }
}

struct LegacyExcessResult<'a> {
  extras: Vec<&'a HirObjectProperty>,
  allowed: Vec<String>,
}

enum LegacyExcessCheck<'a> {
  NotApplicable,
  Allowed,
  Excess(LegacyExcessResult<'a>),
}

fn legacy_find_excess_properties<'a>(
  state: &mut ProgramState,
  target_type: TypeId,
  props: &'a [HirObjectProperty],
) -> LegacyExcessCheck<'a> {
  match state.type_store.kind(target_type).clone() {
    LegacyTypeKind::Any | LegacyTypeKind::Unknown => LegacyExcessCheck::Allowed,
    LegacyTypeKind::Object(obj) => legacy_excess_against_object(&obj, props)
      .map(LegacyExcessCheck::Excess)
      .unwrap_or(LegacyExcessCheck::Allowed),
    LegacyTypeKind::Union(members) => {
      let mut best: Option<LegacyExcessResult> = None;
      let mut any_allowed = false;
      for member in members {
        match legacy_find_excess_properties(state, member, props) {
          LegacyExcessCheck::Allowed => {
            any_allowed = true;
            break;
          }
          LegacyExcessCheck::Excess(res) => {
            let replace = match &best {
              None => true,
              Some(current) => {
                res.extras.len() < current.extras.len()
                  || (res.extras.len() == current.extras.len()
                    && res.allowed.cmp(&current.allowed) == Ordering::Less)
              }
            };
            if replace {
              best = Some(res);
            }
          }
          LegacyExcessCheck::NotApplicable => {}
        }
      }
      if any_allowed {
        LegacyExcessCheck::Allowed
      } else if let Some(res) = best {
        LegacyExcessCheck::Excess(res)
      } else {
        LegacyExcessCheck::NotApplicable
      }
    }
    _ => LegacyExcessCheck::NotApplicable,
  }
}

fn legacy_excess_against_object<'a>(
  target: &ObjectType,
  props: &'a [HirObjectProperty],
) -> Option<LegacyExcessResult<'a>> {
  if target.has_index_signature() || target.props.is_empty() {
    return None;
  }
  let mut extras = Vec::new();
  for prop in props.iter() {
    let name = &prop.name;
    if prop.is_spread {
      continue;
    }
    if !legacy_property_allowed(target, name) {
      extras.push(prop);
    }
  }
  if extras.is_empty() {
    None
  } else {
    let mut allowed = legacy_allowed_keys(target);
    allowed.sort();
    allowed.dedup();
    Some(LegacyExcessResult { extras, allowed })
  }
}

fn legacy_property_allowed(target: &ObjectType, name: &str) -> bool {
  if target.props.contains_key(name) {
    return true;
  }
  if name.parse::<usize>().is_ok() {
    target.number_index.is_some() || target.string_index.is_some()
  } else {
    target.string_index.is_some()
  }
}

fn legacy_allowed_keys(target: &ObjectType) -> Vec<String> {
  target.props.keys().cloned().collect()
}
