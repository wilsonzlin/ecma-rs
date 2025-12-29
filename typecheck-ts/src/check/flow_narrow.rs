//! Narrowing helpers used by the flow-sensitive body checker.
use std::collections::HashMap;

use hir_js::BinaryOp;
use num_bigint::BigInt;
use types_ts_interned::{RelateCtx, RelateTypeExpander, TypeId, TypeKind, TypeStore};

use super::flow::{FlowKey, PathSegment};

/// Narrowing facts produced by evaluating an expression in a boolean context.
///
/// - `truthy` applies when the expression evaluates to a truthy value.
/// - `falsy` applies when the expression evaluates to a falsy value.
/// - `assertions` apply unconditionally after the expression completes
///   successfully (used for assertion functions).
#[derive(Clone, Debug, Default)]
pub struct Facts {
  pub truthy: HashMap<FlowKey, TypeId>,
  pub falsy: HashMap<FlowKey, TypeId>,
  pub assertions: HashMap<FlowKey, TypeId>,
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

/// Compose facts for `A && B`.
pub fn and_facts(left: Facts, right: Facts, store: &TypeStore) -> Facts {
  let Facts {
    truthy: left_truthy,
    falsy: left_falsy,
    assertions: left_assertions,
  } = left;
  let Facts {
    truthy: right_truthy,
    falsy: right_falsy,
    assertions: right_assertions,
  } = right;

  let truthy = apply_sequence(&left_truthy, &right_truthy);
  let falsy = join_alternatives(
    &left_falsy,
    &apply_sequence(&left_truthy, &right_falsy),
    store,
  );
  let assertions = merge_assertions(left_assertions, right_assertions, store);

  Facts {
    truthy,
    falsy,
    assertions,
  }
}

/// Compose facts for `A || B`.
pub fn or_facts(left: Facts, right: Facts, store: &TypeStore) -> Facts {
  let Facts {
    truthy: left_truthy,
    falsy: left_falsy,
    assertions: left_assertions,
  } = left;
  let Facts {
    truthy: right_truthy,
    falsy: right_falsy,
    assertions: right_assertions,
  } = right;

  let truthy = join_alternatives(
    &left_truthy,
    &apply_sequence(&left_falsy, &right_truthy),
    store,
  );
  let falsy = apply_sequence(&left_falsy, &right_falsy);
  let assertions = merge_assertions(left_assertions, right_assertions, store);

  Facts {
    truthy,
    falsy,
    assertions,
  }
}

fn apply_sequence(
  first: &HashMap<FlowKey, TypeId>,
  second: &HashMap<FlowKey, TypeId>,
) -> HashMap<FlowKey, TypeId> {
  let mut result = first.clone();
  for (name, ty) in second.iter() {
    result.insert(name.clone(), *ty);
  }
  result
}

fn join_alternatives(
  first: &HashMap<FlowKey, TypeId>,
  second: &HashMap<FlowKey, TypeId>,
  store: &TypeStore,
) -> HashMap<FlowKey, TypeId> {
  let mut result = first.clone();
  for (name, ty) in second.iter() {
    result
      .entry(name.clone())
      .and_modify(|existing| *existing = store.union(vec![*existing, *ty]))
      .or_insert(*ty);
  }
  result
}

fn merge_assertions(
  mut left: HashMap<FlowKey, TypeId>,
  right: HashMap<FlowKey, TypeId>,
  store: &TypeStore,
) -> HashMap<FlowKey, TypeId> {
  for (name, ty) in right {
    left
      .entry(name)
      .and_modify(|existing| *existing = store.union(vec![*existing, ty]))
      .or_insert(ty);
  }
  left
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
    TypeKind::Never => (primitives.never, primitives.never),
    TypeKind::Any | TypeKind::Unknown => (ty, ty),
    TypeKind::Null | TypeKind::Undefined | TypeKind::Void => (primitives.never, ty),
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
    TypeKind::StringLiteral(id) => {
      if store.name(id).is_empty() {
        (primitives.never, ty)
      } else {
        (ty, primitives.never)
      }
    }
    TypeKind::String | TypeKind::TemplateLiteral(_) => (ty, primitives.never),
    TypeKind::Number | TypeKind::BigInt => (ty, ty),
    TypeKind::Boolean => (
      store.intern_type(TypeKind::BooleanLiteral(true)),
      store.intern_type(TypeKind::BooleanLiteral(false)),
    ),
    TypeKind::Symbol | TypeKind::UniqueSymbol => (ty, primitives.never),
    TypeKind::Object(_)
    | TypeKind::Array { .. }
    | TypeKind::Tuple(_)
    | TypeKind::Callable { .. } => (ty, primitives.never),
    TypeKind::Ref { .. }
    | TypeKind::TypeParam(_)
    | TypeKind::Infer { .. }
    | TypeKind::Intersection(_)
    | TypeKind::Conditional { .. }
    | TypeKind::Mapped(_)
    | TypeKind::IndexedAccess { .. }
    | TypeKind::KeyOf(_)
    | TypeKind::This
    | TypeKind::Predicate { .. } => (ty, ty),
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

/// Narrow by a discriminant property check (e.g. `x.kind === "foo"` or `x.kind === 1`).
pub fn narrow_by_discriminant(
  ty: TypeId,
  prop: &str,
  value: &LiteralValue,
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
      let matched = shape.properties.iter().any(|property| {
        matches!(property.key, types_ts_interned::PropKey::String(name) if store.name(name) == prop)
          && matches_discriminant_value(property.data.ty, value, store)
      });
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

/// Narrow by a discriminant property along a path (e.g. `x.meta.kind === "foo"`).
pub fn narrow_by_discriminant_path(
  ty: TypeId,
  path: &[PathSegment],
  value: &LiteralValue,
  store: &TypeStore,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (t, f) = narrow_by_discriminant_path(member, path, value, store);
        if t != primitives.never {
          yes.push(t);
        }
        if f != primitives.never {
          no.push(f);
        }
      }
      (store.union(yes), store.union(no))
    }
    TypeKind::Intersection(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (t, f) = narrow_by_discriminant_path(member, path, value, store);
        if t != primitives.never {
          yes.push(t);
        }
        if f != primitives.never {
          no.push(f);
        }
      }
      (store.union(yes), store.union(no))
    }
    _ => {
      if matches_discriminant_path(ty, path, value, store) {
        (ty, primitives.never)
      } else {
        (primitives.never, ty)
      }
    }
  }
}

fn matches_discriminant_path(
  ty: TypeId,
  path: &[PathSegment],
  value: &LiteralValue,
  store: &TypeStore,
) -> bool {
  if path.is_empty() {
    return false;
  }
  match store.type_kind(ty) {
    TypeKind::Union(members) => members
      .iter()
      .any(|member| matches_discriminant_path(*member, path, value, store)),
    TypeKind::Intersection(members) => members
      .iter()
      .any(|member| matches_discriminant_path(*member, path, value, store)),
    TypeKind::Object(obj) => {
      let object = store.object(obj);
      let shape = store.shape(object.shape);
      let Some(first) = path.first() else {
        return false;
      };
      let prop_ty = shape
        .properties
        .iter()
        .find_map(|prop| match (&prop.key, first) {
          (types_ts_interned::PropKey::String(name), PathSegment::String(seg))
            if store.name(*name) == *seg =>
          {
            Some(prop.data.ty)
          }
          (types_ts_interned::PropKey::Number(num), PathSegment::Number(seg))
            if num.to_string() == *seg =>
          {
            Some(prop.data.ty)
          }
          _ => None,
        });
      let prop_ty = prop_ty.or_else(|| shape.indexers.first().map(|idx| idx.value_type));
      let Some(prop_ty) = prop_ty else {
        return false;
      };
      if path.len() == 1 {
        matches_discriminant_value(prop_ty, value, store)
      } else {
        matches_discriminant_path(prop_ty, &path[1..], value, store)
      }
    }
    _ => false,
  }
}

fn matches_discriminant_value(ty: TypeId, value: &LiteralValue, store: &TypeStore) -> bool {
  match store.type_kind(ty) {
    TypeKind::Union(members) => members
      .iter()
      .any(|member| matches_discriminant_value(*member, value, store)),
    kind => match (kind, value) {
      (TypeKind::StringLiteral(name_id), LiteralValue::String(target)) => {
        store.name(name_id) == *target
      }
      (TypeKind::String, LiteralValue::String(_)) => true,
      (TypeKind::NumberLiteral(num), LiteralValue::Number(target)) => num.0.to_string() == *target,
      (TypeKind::Number, LiteralValue::Number(_)) => true,
      (TypeKind::BooleanLiteral(lit), LiteralValue::Boolean(target)) => lit == *target,
      (TypeKind::Boolean, LiteralValue::Boolean(_)) => true,
      _ => false,
    },
  }
}

/// Narrow by an `in` check (`"prop" in x`).
pub fn narrow_by_in_check(
  ty: TypeId,
  prop: &str,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_in_check(member, prop, store, expander);
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
    TypeKind::Ref { def, args } => {
      if let Some(expanded) = expander.and_then(|e| e.expand_ref(store, def, &args)) {
        return narrow_by_in_check(expanded, prop, store, expander);
      }
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

pub fn narrow_by_instanceof_rhs(
  left_ty: TypeId,
  right_ty: TypeId,
  store: &TypeStore,
  relate: &RelateCtx,
  expander: Option<&dyn RelateTypeExpander>,
) -> (TypeId, TypeId) {
  let target = instance_type_from_ctor(right_ty, store, expander);
  narrow_instanceof_with_target(left_ty, target, store, relate)
}

fn narrow_instanceof_with_target(
  left_ty: TypeId,
  target: Option<TypeId>,
  store: &TypeStore,
  relate: &RelateCtx,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(left_ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_instanceof_with_target(member, target, store, relate);
        if y != primitives.never {
          yes.push(y);
        }
        if n != primitives.never {
          no.push(n);
        }
      }
      (store.union(yes), store.union(no))
    }
    TypeKind::Null | TypeKind::Undefined => (primitives.never, left_ty),
    _ => {
      if let Some(target) = target {
        if relate.is_assignable(left_ty, target) {
          (left_ty, primitives.never)
        } else {
          (primitives.never, left_ty)
        }
      } else {
        narrow_by_instanceof(left_ty, store)
      }
    }
  }
}

fn instance_type_from_ctor(
  ty: TypeId,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
) -> Option<TypeId> {
  let mut targets = Vec::new();
  collect_instance_types(ty, store, expander, &mut targets);
  if targets.is_empty() {
    None
  } else {
    Some(store.union(targets))
  }
}

fn collect_instance_types(
  ty: TypeId,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  out: &mut Vec<TypeId>,
) {
  match store.type_kind(ty) {
    TypeKind::Union(members) | TypeKind::Intersection(members) => {
      for member in members {
        collect_instance_types(member, store, expander, out);
      }
    }
    TypeKind::Ref { def, args } => {
      if let Some(expanded) = expander.and_then(|e| e.expand_ref(store, def, &args)) {
        collect_instance_types(expanded, store, expander, out);
      }
    }
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      for sig in shape.construct_signatures.iter() {
        out.push(store.signature(*sig).ret);
      }
    }
    _ => {}
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

/// Split a type into non-nullish and nullish parts.
pub fn split_nullish(ty: TypeId, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut present = Vec::new();
      let mut nullish = Vec::new();
      for member in members {
        match store.type_kind(member) {
          TypeKind::Null | TypeKind::Undefined => nullish.push(member),
          _ => present.push(member),
        }
      }
      (
        store.union(present),
        if nullish.is_empty() {
          primitives.never
        } else {
          store.union(nullish)
        },
      )
    }
    TypeKind::Null | TypeKind::Undefined => (primitives.never, ty),
    _ => (ty, primitives.never),
  }
}
