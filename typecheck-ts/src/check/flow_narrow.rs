//! Narrowing helpers used by the flow-sensitive body checker.
use std::collections::HashMap;

use hir_js::{BinaryOp, NameId};
use num_bigint::BigInt;
use types_ts_interned::{RelateCtx, TypeId, TypeKind, TypeStore};

/// Narrowing facts produced by evaluating an expression in a boolean context.
///
/// - `truthy` applies when the expression evaluates to a truthy value.
/// - `falsy` applies when the expression evaluates to a falsy value.
/// - `assertions` apply unconditionally after the expression completes
///   successfully (used for assertion functions).
#[derive(Clone, Debug, Default)]
pub struct Facts {
  pub truthy: HashMap<NameId, TypeId>,
  pub falsy: HashMap<NameId, TypeId>,
  pub assertions: HashMap<NameId, TypeId>,
}

impl Facts {
  /// Merge another set of facts into this one, joining types with union.
  pub fn merge(&mut self, other: Facts, store: &TypeStore) {
    for (k, v) in other.truthy {
      self
        .truthy
        .entry(k)
        .and_modify(|existing| *existing = store.union(vec![*existing, v]))
        .or_insert(v);
    }
    for (k, v) in other.falsy {
      self
        .falsy
        .entry(k)
        .and_modify(|existing| *existing = store.union(vec![*existing, v]))
        .or_insert(v);
    }
    for (k, v) in other.assertions {
      self
        .assertions
        .entry(k)
        .and_modify(|existing| *existing = store.union(vec![*existing, v]))
        .or_insert(v);
    }
  }
}

/// Literal value used for equality-based narrowing.
#[derive(Clone, Debug)]
pub enum LiteralValue {
  String(String),
  Number(String),
  Boolean(bool),
  Null,
  Undefined,
}

/// Narrow by a nullish equality/inequality comparison.
pub fn narrow_by_nullish_equality(
  ty: TypeId,
  op_kind: BinaryOp,
  lit: &LiteralValue,
  store: &TypeStore,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  if !matches!(lit, LiteralValue::Null | LiteralValue::Undefined) {
    return (primitives.never, ty);
  }
  if !matches!(
    op_kind,
    BinaryOp::Equality
      | BinaryOp::Inequality
      | BinaryOp::StrictEquality
      | BinaryOp::StrictInequality
  ) {
    return (primitives.never, ty);
  }
  let loose = matches!(op_kind, BinaryOp::Equality | BinaryOp::Inequality);
  let matches_literal = |kind: &TypeKind| match lit {
    LiteralValue::Null => {
      matches!(kind, TypeKind::Null) || (loose && matches!(kind, TypeKind::Undefined))
    }
    LiteralValue::Undefined => {
      matches!(kind, TypeKind::Undefined) || (loose && matches!(kind, TypeKind::Null))
    }
    _ => false,
  };

  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_nullish_equality(member, op_kind, lit, store);
        if y != primitives.never {
          yes.push(y);
        }
        if n != primitives.never {
          no.push(n);
        }
      }
      (store.union(yes), store.union(no))
    }
    kind => {
      let matches = matches_literal(&kind);
      if matches {
        (ty, primitives.never)
      } else {
        (primitives.never, ty)
      }
    }
  }
}

/// Narrow by an equality comparison with a literal value.
pub fn narrow_by_literal(ty: TypeId, lit: &LiteralValue, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_literal(member, lit, store);
        if y != primitives.never {
          yes.push(y);
        }
        if n != primitives.never {
          no.push(n);
        }
      }
      (store.union(yes), store.union(no))
    }
    TypeKind::StringLiteral(name) => match lit {
      LiteralValue::String(target) if store.name(name) == *target => (ty, primitives.never),
      LiteralValue::String(_) => (primitives.never, ty),
      _ => (primitives.never, ty),
    },
    TypeKind::String => match lit {
      LiteralValue::String(target) => (
        store.intern_type(TypeKind::StringLiteral(store.intern_name(target))),
        ty,
      ),
      _ => (primitives.never, ty),
    },
    TypeKind::NumberLiteral(value) => match lit {
      LiteralValue::Number(target) if value.0.to_string() == *target => (ty, primitives.never),
      LiteralValue::Number(_) => (primitives.never, ty),
      _ => (primitives.never, ty),
    },
    TypeKind::Number => match lit {
      LiteralValue::Number(target) => (
        store.intern_type(TypeKind::NumberLiteral(
          target.parse::<f64>().unwrap_or_default().into(),
        )),
        ty,
      ),
      _ => (primitives.never, ty),
    },
    TypeKind::BooleanLiteral(value) => match lit {
      LiteralValue::Boolean(target) if value == *target => (ty, primitives.never),
      LiteralValue::Boolean(_) => (primitives.never, ty),
      _ => (primitives.never, ty),
    },
    TypeKind::Boolean => match lit {
      LiteralValue::Boolean(target) => (store.intern_type(TypeKind::BooleanLiteral(*target)), ty),
      _ => (primitives.never, ty),
    },
    TypeKind::Null => match lit {
      LiteralValue::Null => (ty, primitives.never),
      _ => (primitives.never, ty),
    },
    TypeKind::Undefined => match lit {
      LiteralValue::Undefined => (ty, primitives.never),
      _ => (primitives.never, ty),
    },
    _ => (primitives.never, ty),
  }
}

/// Compute the truthy and falsy types for a given variable type.
pub fn truthy_falsy_types(ty: TypeId, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut truthy = Vec::new();
      let mut falsy = Vec::new();
      for member in members {
        let (t, f) = truthy_falsy_types(member, store);
        if t != primitives.never {
          truthy.push(t);
        }
        if f != primitives.never {
          falsy.push(f);
        }
      }
      (store.union(truthy), store.union(falsy))
    }
    TypeKind::Null | TypeKind::Undefined => (primitives.never, ty),
    TypeKind::BooleanLiteral(false) => (primitives.never, ty),
    TypeKind::BooleanLiteral(true) => (ty, primitives.never),
    TypeKind::NumberLiteral(num) => {
      if num.0 == 0.0 || num.0.is_nan() {
        (primitives.never, ty)
      } else {
        (ty, primitives.never)
      }
    }
    TypeKind::BigIntLiteral(value) => {
      if value == BigInt::from(0) {
        (primitives.never, ty)
      } else {
        (ty, primitives.never)
      }
    }
    TypeKind::StringLiteral(id) if store.name(id).is_empty() => (primitives.never, ty),
    TypeKind::Boolean => (
      store.intern_type(TypeKind::BooleanLiteral(true)),
      store.intern_type(TypeKind::BooleanLiteral(false)),
    ),
    _ => (ty, primitives.never),
  }
}

/// Split a type into its non-nullish and nullish parts.
pub fn narrow_non_nullish(ty: TypeId, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut non_nullish = Vec::new();
      let mut nullish = Vec::new();
      for member in members {
        let (yes, no) = narrow_non_nullish(member, store);
        if yes != primitives.never {
          non_nullish.push(yes);
        }
        if no != primitives.never {
          nullish.push(no);
        }
      }
      (store.union(non_nullish), store.union(nullish))
    }
    TypeKind::Null | TypeKind::Undefined | TypeKind::Void => (primitives.never, ty),
    TypeKind::Any | TypeKind::Unknown | TypeKind::Intersection(_) => (ty, ty),
    TypeKind::Never => (primitives.never, primitives.never),
    _ => (ty, primitives.never),
  }
}

/// Split a type into its non-nullish and nullish components.
pub fn split_nullish(ty: TypeId, store: &TypeStore) -> (TypeId, TypeId) {
  narrow_non_nullish(ty, store)
}

/// Narrow a variable by a typeof comparison (e.g. `typeof x === "string"`).
pub fn narrow_by_typeof(ty: TypeId, target: &str, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  let matches = |k: &TypeKind| match k {
    TypeKind::String | TypeKind::StringLiteral(_) => target == "string",
    TypeKind::Number | TypeKind::NumberLiteral(_) => target == "number",
    TypeKind::Boolean | TypeKind::BooleanLiteral(_) => target == "boolean",
    TypeKind::BigInt | TypeKind::BigIntLiteral(_) => target == "bigint",
    TypeKind::Symbol | TypeKind::UniqueSymbol => target == "symbol",
    TypeKind::Callable { .. } => target == "function",
    TypeKind::Undefined => target == "undefined",
    TypeKind::Null => target == "object",
    TypeKind::Object(_) | TypeKind::Array { .. } | TypeKind::Ref { .. } => target == "object",
    _ => false,
  };

  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        if matches(&store.type_kind(member)) {
          yes.push(member);
        } else {
          no.push(member);
        }
      }
      (store.union(yes), store.union(no))
    }
    _ => {
      if matches(&store.type_kind(ty)) {
        (ty, primitives.never)
      } else {
        (primitives.never, ty)
      }
    }
  }
}

/// Narrow by a discriminant property check (e.g. `x.kind === "foo"`).
pub fn narrow_by_discriminant(
  ty: TypeId,
  prop: &str,
  value: &str,
  store: &TypeStore,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_discriminant(member, prop, value, store);
        if t != primitives.never {
          yes.push(t);
        }
        if f != primitives.never {
          no.push(f);
        }
      }
    }
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      let mut matched = false;
      for property in shape.properties.iter() {
        match store.type_kind(property.data.ty) {
          TypeKind::StringLiteral(name_id) => {
            if matches!(property.key, types_ts_interned::PropKey::String(name) if store.name(name) == prop)
              && store.name(name_id) == value
            {
              matched = true;
              break;
            }
          }
          TypeKind::String => {
            if matches!(property.key, types_ts_interned::PropKey::String(name) if store.name(name) == prop)
            {
              matched = true;
              break;
            }
          }
          _ => {}
        }
      }
      if matched {
        yes.push(ty);
      } else {
        no.push(ty);
      }
    }
    _ => no.push(ty),
  }

  (store.union(yes), store.union(no))
}

/// Narrow by an `in` check (`"prop" in x`).
pub fn narrow_by_in_check(ty: TypeId, prop: &str, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_in_check(member, prop, store);
        if t != primitives.never {
          yes.push(t);
        }
        if f != primitives.never {
          no.push(f);
        }
      }
    }
    TypeKind::Array { .. } => {
      yes.push(ty);
    }
    TypeKind::Ref { .. } => {
      yes.push(ty);
      no.push(ty);
    }
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      let has_prop = shape.properties.iter().any(|p| match p.key {
        types_ts_interned::PropKey::String(name) => store.name(name) == prop,
        types_ts_interned::PropKey::Number(num) => num.to_string() == prop,
        _ => false,
      }) || shape.indexers.first().is_some();
      if has_prop {
        yes.push(ty);
      } else {
        no.push(ty);
      }
    }
    _ => no.push(ty),
  }
  (store.union(yes), store.union(no))
}

/// Narrow by an `instanceof` check, keeping only object-like members.
pub fn narrow_by_instanceof(ty: TypeId, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_instanceof(member, store);
        if y != primitives.never {
          yes.push(y);
        }
        if n != primitives.never {
          no.push(n);
        }
      }
      (store.union(yes), store.union(no))
    }
    TypeKind::Object(_)
    | TypeKind::Array { .. }
    | TypeKind::Callable { .. }
    | TypeKind::Ref { .. } => (ty, primitives.never),
    _ => (primitives.never, ty),
  }
}

/// Narrow by an asserted type from a predicate.
pub fn narrow_by_asserted(ty: TypeId, asserted: TypeId, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_asserted(member, asserted, store);
        if y != primitives.never {
          yes.push(y);
        }
        if n != primitives.never {
          no.push(n);
        }
      }
      (store.union(yes), store.union(no))
    }
    _ => {
      if matches_asserted(ty, asserted, store) {
        (ty, primitives.never)
      } else {
        (primitives.never, ty)
      }
    }
  }
}

/// Narrow a type by retaining members assignable to the target while keeping a
/// conservative remainder for the falsy branch.
pub fn narrow_by_assignability(
  ty: TypeId,
  target: TypeId,
  store: &TypeStore,
  relate: &RelateCtx<'_>,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_assignability(member, target, store, relate);
        if y != primitives.never {
          yes.push(y);
        }
        if n != primitives.never {
          no.push(n);
        }
      }
      (store.union(yes), store.union(no))
    }
    _ => {
      if relate.is_assignable(ty, target) {
        (ty, primitives.never)
      } else if relate.is_assignable(target, ty) {
        (target, ty)
      } else {
        (primitives.never, ty)
      }
    }
  }
}

fn matches_asserted(ty: TypeId, asserted: TypeId, store: &TypeStore) -> bool {
  if ty == asserted {
    return true;
  }
  match store.type_kind(asserted) {
    TypeKind::Union(members) => members.iter().any(|m| matches_asserted(ty, *m, store)),
    TypeKind::String => matches!(
      store.type_kind(ty),
      TypeKind::String | TypeKind::StringLiteral(_)
    ),
    TypeKind::Number => matches!(
      store.type_kind(ty),
      TypeKind::Number | TypeKind::NumberLiteral(_)
    ),
    TypeKind::Boolean => matches!(
      store.type_kind(ty),
      TypeKind::Boolean | TypeKind::BooleanLiteral(_)
    ),
    TypeKind::Null => matches!(store.type_kind(ty), TypeKind::Null),
    TypeKind::Undefined => matches!(store.type_kind(ty), TypeKind::Undefined),
    TypeKind::Object(_) => matches!(store.type_kind(ty), TypeKind::Object(_)),
    TypeKind::Ref { .. } => matches!(store.type_kind(ty), TypeKind::Ref { .. }),
    _ => false,
  }
}
