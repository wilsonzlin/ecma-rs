use hir_js::{BodyId, ExprId};
use std::fmt;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Truthiness {
  AlwaysTruthy,
  AlwaysFalsy,
}

/// Optional TypeScript type information for the optimizer.
///
/// The optimizer is designed to compile without a dependency on `typecheck-ts`.
/// When the `typed` feature is enabled callers can populate this context with a
/// `typecheck_ts::Program` and per-body expression type tables.
#[derive(Clone, Default)]
pub struct TypeContext {
  #[cfg(feature = "typed")]
  pub(crate) program: Option<std::sync::Arc<typecheck_ts::Program>>,
  #[cfg(feature = "typed")]
  pub(crate) expr_types: ahash::HashMap<BodyId, Vec<Option<typecheck_ts::TypeId>>>,
}

impl fmt::Debug for TypeContext {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    let mut s = f.debug_struct("TypeContext");
    #[cfg(feature = "typed")]
    {
      s.field("has_program", &self.program.is_some());
      s.field("body_count", &self.expr_types.len());
    }
    s.finish()
  }
}

impl TypeContext {
  /// Type identifier for a HIR expression, if available.
  pub fn expr_type(&self, body: BodyId, expr: ExprId) -> Option<TypeId> {
    #[cfg(feature = "typed")]
    {
      self
        .expr_types
        .get(&body)
        .and_then(|types| types.get(expr.0 as usize).copied())
        .flatten()
    }
    #[cfg(not(feature = "typed"))]
    {
      let _ = (body, expr);
      None
    }
  }

  /// If `expr` is statically typed as a boolean literal, return that literal value.
  pub fn bool_literal_expr(&self, body: BodyId, expr: ExprId) -> Option<bool> {
    #[cfg(feature = "typed")]
    {
      let program = self.program.as_ref()?;
      let ty = self.expr_type(body, expr)?;
      match program.type_kind(ty) {
        typecheck_ts::TypeKindSummary::BooleanLiteral(value) => Some(value),
        _ => None,
      }
    }
    #[cfg(not(feature = "typed"))]
    {
      let _ = (body, expr);
      None
    }
  }

  /// If `expr` is statically typed as always truthy or always falsy, return that truthiness.
  pub fn expr_truthiness(&self, body: BodyId, expr: ExprId) -> Option<Truthiness> {
    #[cfg(feature = "typed")]
    {
      let program = self.program.as_ref()?;
      if !program.compiler_options().strict_null_checks {
        return None;
      }
      let ty = self.expr_type(body, expr)?;
      type_truthiness(program, ty, 0)
    }
    #[cfg(not(feature = "typed"))]
    {
      let _ = (body, expr);
      None
    }
  }

  /// Returns `true` if the expression type is known to exclude `null | undefined`.
  pub fn expr_excludes_nullish(&self, body: BodyId, expr: ExprId) -> bool {
    #[cfg(feature = "typed")]
    {
      let Some(program) = self.program.as_ref() else {
        return false;
      };
      let Some(ty) = self.expr_type(body, expr) else {
        return false;
      };
      type_excludes_nullish(program, ty, 0)
    }
    #[cfg(not(feature = "typed"))]
    {
      let _ = (body, expr);
      false
    }
  }

  /// Returns the JavaScript `typeof` tag for the expression when it is known.
  ///
  /// This is intentionally conservative; if we cannot reliably map the
  /// TypeScript type to a single runtime `typeof` string we return `None` and
  /// callers should fall back to untyped behaviour.
  pub fn expr_typeof_string(&self, body: BodyId, expr: ExprId) -> Option<&'static str> {
    #[cfg(feature = "typed")]
    {
      let program = self.program.as_ref()?;
      let ty = self.expr_type(body, expr)?;
      type_to_typeof_string(program, ty, 0)
    }
    #[cfg(not(feature = "typed"))]
    {
      let _ = (body, expr);
      None
    }
  }

  /// Returns `true` when the expression is known to evaluate to a primitive boolean.
  ///
  /// This is conservative; if the type information is unavailable or the type
  /// cannot be proven to be `boolean` (including boolean literals), returns
  /// `false`.
  pub fn expr_is_boolean(&self, body: BodyId, expr: ExprId) -> bool {
    #[cfg(feature = "typed")]
    {
      let Some(program) = self.program.as_ref() else {
        return false;
      };
      let Some(ty) = self.expr_type(body, expr) else {
        return false;
      };
      type_is_boolean(program, ty, 0)
    }
    #[cfg(not(feature = "typed"))]
    {
      let _ = (body, expr);
      false
    }
  }
}

#[cfg(feature = "typed")]
pub type TypeId = typecheck_ts::TypeId;

#[cfg(not(feature = "typed"))]
pub type TypeId = ();

#[cfg(feature = "typed")]
impl TypeContext {
  /// Build a [`TypeContext`] from a `typecheck-ts` program.
  ///
  /// When possible we prefer an ID-aligned mapping between `hir-js` bodies and
  /// `typecheck-ts` [`typecheck_ts::BodyCheckResult`] side tables (matching on
  /// `BodyId` and validating the expression counts). If that fails for a
  /// particular body, we fall back to span-based matching as a conservative
  /// best-effort.
  pub fn from_typecheck_program(
    program: std::sync::Arc<typecheck_ts::Program>,
    file: typecheck_ts::FileId,
    lower: &hir_js::LowerResult,
  ) -> Self {
    use ahash::HashMapExt;
    use diagnostics::TextRange;

    let mut checked_expr_types: ahash::HashMap<BodyId, Vec<Option<typecheck_ts::TypeId>>> =
      ahash::HashMap::new();
    let mut span_to_ty: ahash::HashMap<TextRange, Option<typecheck_ts::TypeId>> =
      ahash::HashMap::new();

    for body_id in program.bodies_in_file(file) {
      let checked = program.check_body(body_id);
      checked_expr_types.insert(
        body_id,
        checked.expr_types().iter().copied().map(Some).collect(),
      );
      for (&span, &ty) in checked.expr_spans().iter().zip(checked.expr_types().iter()) {
        span_to_ty
          .entry(span)
          .and_modify(|existing| {
            if existing.map(|existing| existing != ty).unwrap_or(false) {
              *existing = None;
            }
          })
          .or_insert(Some(ty));
      }
    }

    let mut expr_types = ahash::HashMap::new();
    for (body_id, idx) in lower.body_index.iter() {
      let body = &lower.bodies[*idx];
      if let Some(types) = checked_expr_types
        .get(body_id)
        .filter(|types| types.len() == body.exprs.len())
      {
        expr_types.insert(*body_id, types.clone());
        continue;
      }

      let mut body_types = Vec::with_capacity(body.exprs.len());
      for expr in body.exprs.iter() {
        let ty = span_to_ty.get(&expr.span).and_then(|ty| *ty);
        body_types.push(ty);
      }
      expr_types.insert(*body_id, body_types);
    }

    Self {
      program: Some(program),
      expr_types,
    }
  }
}

#[cfg(feature = "typed")]
fn type_excludes_nullish(
  program: &typecheck_ts::Program,
  ty: typecheck_ts::TypeId,
  depth: u8,
) -> bool {
  if !program.compiler_options().strict_null_checks {
    return false;
  }
  // Avoid pathological recursion for self-referential aliases.
  if depth >= 8 {
    return false;
  }

  use types_ts_interned::TypeKind as K;
  match program.interned_type_kind(ty) {
    K::Any
    | K::Unknown
    | K::Void
    | K::Null
    | K::Undefined
    | K::This
    | K::Infer { .. }
    | K::TypeParam(_)
    | K::Predicate { .. }
    | K::Conditional { .. }
    | K::Mapped(_)
    | K::TemplateLiteral(_)
    | K::IndexedAccess { .. }
    | K::KeyOf(_) => false,
    // `never` contains no values and is trivially non-nullish.
    K::Never => true,
    K::Union(members) => members
      .into_iter()
      .all(|member| type_excludes_nullish(program, member, depth + 1)),
    K::Intersection(members) => members
      .into_iter()
      .any(|member| type_excludes_nullish(program, member, depth + 1)),
    K::Ref { def, .. } => type_excludes_nullish(
      program,
      program.declared_type_of_def_interned(def),
      depth + 1,
    ),
    K::EmptyObject => true,
    _ => true,
  }
}

#[cfg(feature = "typed")]
fn type_to_typeof_string(
  program: &typecheck_ts::Program,
  ty: typecheck_ts::TypeId,
  depth: u8,
) -> Option<&'static str> {
  if depth >= 8 {
    return None;
  }

  use types_ts_interned::TypeKind as K;
  match program.interned_type_kind(ty) {
    K::Boolean | K::BooleanLiteral(_) => Some("boolean"),
    K::Number | K::NumberLiteral(_) => Some("number"),
    K::String | K::StringLiteral(_) => Some("string"),
    K::BigInt | K::BigIntLiteral(_) => Some("bigint"),
    K::Symbol | K::UniqueSymbol => Some("symbol"),
    K::Undefined | K::Void => Some("undefined"),
    K::Null => Some("object"),
    K::Callable { .. } => Some("function"),
    // We can only return a `typeof` result when it is uniquely determined by
    // the type. Note that the TypeScript `{}`/`object` supertypes can include
    // callable values, so they do *not* map to a single `typeof` tag.
    K::Tuple(_) | K::Array { .. } => Some("object"),
    K::Ref { def, .. } => type_to_typeof_string(
      program,
      program.declared_type_of_def_interned(def),
      depth + 1,
    ),
    K::Union(members) => {
      let mut tag: Option<&'static str> = None;
      for member in members {
        if matches!(program.interned_type_kind(member), K::Never) {
          continue;
        }
        let member_tag = type_to_typeof_string(program, member, depth + 1)?;
        match tag {
          None => tag = Some(member_tag),
          Some(existing) if existing == member_tag => {}
          _ => return None,
        }
      }
      tag
    }
    K::Intersection(members) => {
      let mut tag: Option<&'static str> = None;
      for member in members {
        if matches!(program.interned_type_kind(member), K::Never) {
          continue;
        }
        let Some(member_tag) = type_to_typeof_string(program, member, depth + 1) else {
          continue;
        };
        match tag {
          None => tag = Some(member_tag),
          Some(existing) if existing == member_tag => {}
          _ => return None,
        }
      }
      tag
    }
    _ => None,
  }
}

#[cfg(feature = "typed")]
fn type_truthiness(
  program: &typecheck_ts::Program,
  ty: typecheck_ts::TypeId,
  depth: u8,
) -> Option<Truthiness> {
  if depth >= 8 {
    return None;
  }

  use types_ts_interned::TypeKind as K;
  match program.interned_type_kind(ty) {
    K::Null | K::Undefined | K::Void => Some(Truthiness::AlwaysFalsy),
    K::BooleanLiteral(value) => Some(if value {
      Truthiness::AlwaysTruthy
    } else {
      Truthiness::AlwaysFalsy
    }),
    K::StringLiteral(_) => match program.type_kind(ty) {
      typecheck_ts::TypeKindSummary::StringLiteral(value) => Some(if value.is_empty() {
        Truthiness::AlwaysFalsy
      } else {
        Truthiness::AlwaysTruthy
      }),
      _ => None,
    },
    K::NumberLiteral(value) => {
      let value = value.0;
      Some(if value == 0.0 || value.is_nan() {
        Truthiness::AlwaysFalsy
      } else {
        Truthiness::AlwaysTruthy
      })
    }
    K::BigIntLiteral(value) => Some(if value == num_bigint::BigInt::from(0) {
      Truthiness::AlwaysFalsy
    } else {
      Truthiness::AlwaysTruthy
    }),
    K::Tuple(_) | K::Array { .. } | K::Callable { .. } | K::Object(_) | K::EmptyObject => {
      Some(Truthiness::AlwaysTruthy)
    }
    K::Symbol | K::UniqueSymbol => Some(Truthiness::AlwaysTruthy),
    K::Union(members) => {
      let mut acc: Option<Truthiness> = None;
      for member in members {
        if matches!(program.interned_type_kind(member), K::Never) {
          continue;
        }
        let member_truthiness = type_truthiness(program, member, depth + 1)?;
        match acc {
          None => acc = Some(member_truthiness),
          Some(existing) if existing == member_truthiness => {}
          _ => return None,
        }
      }
      acc
    }
    K::Intersection(members) => {
      let mut has_truthy = false;
      let mut has_falsy = false;
      for member in members {
        let Some(member_truthiness) = type_truthiness(program, member, depth + 1) else {
          continue;
        };
        match member_truthiness {
          Truthiness::AlwaysTruthy => has_truthy = true,
          Truthiness::AlwaysFalsy => has_falsy = true,
        }
      }
      match (has_truthy, has_falsy) {
        (true, false) => Some(Truthiness::AlwaysTruthy),
        (false, true) => Some(Truthiness::AlwaysFalsy),
        _ => None,
      }
    }
    K::Ref { def, .. } => type_truthiness(
      program,
      program.declared_type_of_def_interned(def),
      depth + 1,
    ),
    _ => None,
  }
}

#[cfg(feature = "typed")]
fn type_is_boolean(program: &typecheck_ts::Program, ty: typecheck_ts::TypeId, depth: u8) -> bool {
  if depth >= 8 {
    return false;
  }

  use types_ts_interned::IntrinsicKind;
  use types_ts_interned::TypeKind as K;

  match program.interned_type_kind(ty) {
    K::Boolean | K::BooleanLiteral(_) => true,
    // `never` contains no runtime values, so it is vacuously a boolean.
    K::Never => true,
    K::Union(members) => members
      .into_iter()
      .all(|member| type_is_boolean(program, member, depth + 1)),
    // Intersection types narrow; if any constituent is boolean the result is a subset of boolean.
    K::Intersection(members) => members
      .into_iter()
      .any(|member| type_is_boolean(program, member, depth + 1)),
    K::Ref { def, .. } => type_is_boolean(
      program,
      program.declared_type_of_def_interned(def),
      depth + 1,
    ),
    K::Intrinsic { kind, ty } => match kind {
      IntrinsicKind::NoInfer => type_is_boolean(program, ty, depth + 1),
      _ => false,
    },
    _ => false,
  }
}
