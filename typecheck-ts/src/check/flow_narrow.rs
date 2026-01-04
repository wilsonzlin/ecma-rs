//! Narrowing helpers used by the flow-sensitive body checker.
use std::collections::{HashMap, HashSet};

use hir_js::BinaryOp;
use num_bigint::BigInt;
use types_ts_interned::{IntrinsicKind, RelateCtx, RelateTypeExpander, TypeId, TypeKind, TypeStore};

use super::flow::{FlowKey, PathSegment};

/// Expand `TypeKind::Ref` nodes, stopping when expansion makes no progress or
/// encounters a cycle.
///
/// `RelateTypeExpander::expand_ref` is already recursion-safe during expansion,
/// but callers must still defend against "no-progress" results (e.g. a
/// self-referential type alias whose expansion is itself a `Ref`, or a small
/// alias cycle like `A = B; B = A`).
fn expand_ref_no_progress_guard(
  ty: TypeId,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  seen: &mut HashSet<TypeId>,
  budget: &mut usize,
) -> TypeId {
  let Some(expander) = expander else {
    return store.canon(ty);
  };
  let mut current = store.canon(ty);
  while *budget > 0 {
    match store.type_kind(current) {
      TypeKind::Ref { def, args } => {
        if !seen.insert(current) {
          break;
        }
        let Some(expanded) = expander.expand_ref(store, def, &args) else {
          break;
        };
        let expanded = store.canon(expanded);
        if expanded == current {
          break;
        }
        current = expanded;
        *budget -= 1;
      }
      _ => break,
    }
  }
  current
}

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
  let prim = store.primitive_ids();

  let truthy = apply_sequence(&left_truthy, &right_truthy);
  let right_falsy = apply_sequence(&left_truthy, &right_falsy);
  let mut falsy = HashMap::new();
  for (name, left_ty) in left_falsy.iter() {
    if let Some(right_ty) = right_falsy.get(name) {
      if *right_ty == prim.never {
        falsy.insert(name.clone(), *left_ty);
      } else {
        let nullish = narrow_non_nullish(*left_ty, store).1;
        let ty = if nullish == prim.never {
          *right_ty
        } else {
          store.union(vec![*right_ty, nullish])
        };
        falsy.insert(name.clone(), ty);
      }
    } else {
      falsy.insert(name.clone(), *left_ty);
    }
  }
  for (name, ty) in right_falsy.iter() {
    falsy.entry(name.clone()).or_insert(*ty);
  }
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

  let right_truthy = apply_sequence(&left_falsy, &right_truthy);
  let mut truthy = left_truthy.clone();
  for (name, ty) in right_truthy.iter() {
    truthy
      .entry(name.clone())
      .and_modify(|existing| *existing = store.union(vec![*existing, *ty]))
      .or_insert_with(|| {
        if let Some(falsy) = right_falsy.get(name) {
          store.union(vec![*ty, *falsy])
        } else {
          *ty
        }
      });
  }
  let falsy = apply_sequence(&left_falsy, &right_falsy);
  let assertions = merge_assertions(left_assertions, right_assertions, store);

  Facts {
    truthy,
    falsy,
    assertions,
  }
}

/// Compose facts for `A ?? B`.
///
/// The right-hand side is evaluated only when `A` is `null` / `undefined`. This
/// helper keeps the implementation conservative: it preserves narrowing facts
/// from `A` (when `A` itself decides the branch) and combines them with the
/// facts that hold when `B` is evaluated, seeded by the provided
/// `left_nullish_facts`.
pub fn nullish_coalesce_facts(
  left: Facts,
  right: Facts,
  left_nullish_facts: HashMap<FlowKey, TypeId>,
  store: &TypeStore,
) -> Facts {
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

  let right_truthy = apply_sequence(&left_nullish_facts, &right_truthy);
  let right_falsy = apply_sequence(&left_nullish_facts, &right_falsy);

  Facts {
    truthy: join_alternatives(&left_truthy, &right_truthy, store),
    falsy: join_alternatives(&left_falsy, &right_falsy, store),
    assertions: merge_assertions(left_assertions, right_assertions, store),
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
    TypeKind::Any | TypeKind::Unknown | TypeKind::EmptyObject => (ty, ty),
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
    TypeKind::Number | TypeKind::BigInt | TypeKind::String | TypeKind::TemplateLiteral(_) => {
      (ty, ty)
    }
    TypeKind::Boolean => (
      store.intern_type(TypeKind::BooleanLiteral(true)),
      store.intern_type(TypeKind::BooleanLiteral(false)),
    ),
    TypeKind::Symbol | TypeKind::UniqueSymbol => (ty, primitives.never),
    TypeKind::Object(_)
    | TypeKind::Array { .. }
    | TypeKind::Tuple(_)
    | TypeKind::Callable { .. } => (ty, primitives.never),
    TypeKind::Intrinsic {
      kind: IntrinsicKind::NoInfer,
      ty: operand,
    } => truthy_falsy_types(operand, store),
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
    TypeKind::Intrinsic { .. } => (ty, ty),
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
    TypeKind::Intrinsic {
      kind: IntrinsicKind::NoInfer,
      ty: operand,
    } => narrow_non_nullish(operand, store),
    TypeKind::Intrinsic {
      kind: IntrinsicKind::BuiltinIteratorReturn,
      ..
    } => (ty, ty),
    TypeKind::Any | TypeKind::Unknown | TypeKind::Intersection(_) => (ty, ty),
    TypeKind::Never => (primitives.never, primitives.never),
    _ => (ty, primitives.never),
  }
}

/// Narrow a variable by a typeof comparison (e.g. `typeof x === "string"`).
pub fn narrow_by_typeof(ty: TypeId, target: &str, store: &TypeStore) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  fn matches_typeof(kind: &TypeKind, target: &str, store: &TypeStore) -> bool {
    match kind {
    TypeKind::String | TypeKind::StringLiteral(_) => target == "string",
    TypeKind::Number | TypeKind::NumberLiteral(_) => target == "number",
    TypeKind::Boolean | TypeKind::BooleanLiteral(_) => target == "boolean",
    TypeKind::BigInt | TypeKind::BigIntLiteral(_) => target == "bigint",
    TypeKind::Symbol | TypeKind::UniqueSymbol => target == "symbol",
    TypeKind::Callable { .. } => target == "function",
    TypeKind::Undefined => target == "undefined",
    TypeKind::Null => target == "object",
    TypeKind::Object(_) | TypeKind::Array { .. } | TypeKind::Ref { .. } => target == "object",
    TypeKind::Intrinsic { kind, ty } => match kind {
      IntrinsicKind::NoInfer => matches_typeof(&store.type_kind(*ty), target, store),
      IntrinsicKind::BuiltinIteratorReturn => false,
      _ => target == "string",
    },
    TypeKind::Any | TypeKind::Unknown | TypeKind::EmptyObject | TypeKind::TypeParam(_) => false,
    _ => false,
    }
  }

  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        if matches_typeof(&store.type_kind(member), target, store) {
          yes.push(member);
        } else {
          no.push(member);
        }
      }
      (store.union(yes), store.union(no))
    }
    TypeKind::Any | TypeKind::EmptyObject => (ty, ty),
    TypeKind::Intrinsic {
      kind: IntrinsicKind::NoInfer,
      ty: operand,
    } => narrow_by_typeof(operand, target, store),
    TypeKind::Intrinsic {
      kind: IntrinsicKind::BuiltinIteratorReturn,
      ..
    } => (ty, ty),
    TypeKind::Unknown => {
      let prim = store.primitive_ids();
      let yes = match target {
        "string" => prim.string,
        "number" => prim.number,
        "boolean" => prim.boolean,
        "bigint" => prim.bigint,
        "symbol" => prim.symbol,
        "undefined" => prim.undefined,
        _ => return (ty, ty),
      };
      (yes, ty)
    }
    _ => {
      if matches_typeof(&store.type_kind(ty), target, store) {
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
  expander: Option<&dyn RelateTypeExpander>,
) -> (TypeId, TypeId) {
  narrow_by_discriminant_path(
    ty,
    &[PathSegment::String(prop.to_string())],
    value,
    store,
    expander,
  )
}

/// Narrow by a discriminant property along a path (e.g. `x.meta.kind === "foo"`).
pub fn narrow_by_discriminant_path(
  ty: TypeId,
  path: &[PathSegment],
  value: &LiteralValue,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
) -> (TypeId, TypeId) {
  let mut seen = HashSet::new();
  let mut budget = 64usize;
  narrow_by_discriminant_path_inner(ty, path, value, store, expander, &mut seen, &mut budget)
}

fn narrow_by_discriminant_path_inner(
  ty: TypeId,
  path: &[PathSegment],
  value: &LiteralValue,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  seen: &mut HashSet<TypeId>,
  budget: &mut usize,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    TypeKind::Any | TypeKind::Unknown | TypeKind::EmptyObject | TypeKind::TypeParam(_) => (ty, ty),
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (t, f) =
          narrow_by_discriminant_path_inner(member, path, value, store, expander, seen, budget);
        if t != primitives.never {
          yes.push(t);
        }
        if f != primitives.never {
          no.push(f);
        }
      }
      (store.union(yes), store.union(no))
    }
    TypeKind::Ref { .. } => {
      let expanded = expand_ref_no_progress_guard(ty, store, expander, seen, budget);
      if expanded == ty {
        // Without progress we cannot establish whether the discriminant holds.
        return (ty, ty);
      }
      let (yes, no) =
        narrow_by_discriminant_path_inner(expanded, path, value, store, expander, seen, budget);
      // Preserve the reference when the narrowing is an all-or-nothing match, so
      // marker output keeps named types intact.
      if yes == expanded && no == primitives.never {
        (ty, primitives.never)
      } else if yes == primitives.never && no == expanded {
        (primitives.never, ty)
      } else {
        (yes, no)
      }
    }
    _ => {
      if matches_discriminant_path(ty, path, value, store, expander, seen, budget) {
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
  expander: Option<&dyn RelateTypeExpander>,
  seen: &mut HashSet<TypeId>,
  budget: &mut usize,
) -> bool {
  if path.is_empty() {
    return false;
  }
  let ty = expand_ref_no_progress_guard(ty, store, expander, seen, budget);
  match store.type_kind(ty) {
    TypeKind::Union(members) => members
      .iter()
      .any(|member| matches_discriminant_path(*member, path, value, store, expander, seen, budget)),
    TypeKind::Intersection(members) => members
      .iter()
      .any(|member| matches_discriminant_path(*member, path, value, store, expander, seen, budget)),
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
      let prop_ty = prop_ty.or_else(|| {
        let empty_name = store.intern_name(String::new());
        let probe_key = match first {
          PathSegment::String(_) => types_ts_interned::PropKey::String(empty_name),
          PathSegment::Number(_) => types_ts_interned::PropKey::Number(0),
        };
        shape.indexers.iter().find_map(|idx| {
          crate::type_queries::indexer_accepts_key(&probe_key, idx.key_type, store)
            .then_some(idx.value_type)
        })
      });
      let Some(prop_ty) = prop_ty else {
        return false;
      };
      if path.len() == 1 {
        matches_discriminant_value(prop_ty, value, store, expander, seen, budget)
      } else {
        matches_discriminant_path(prop_ty, &path[1..], value, store, expander, seen, budget)
      }
    }
    _ => false,
  }
}

fn matches_discriminant_value(
  ty: TypeId,
  value: &LiteralValue,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  seen: &mut HashSet<TypeId>,
  budget: &mut usize,
) -> bool {
  let ty = expand_ref_no_progress_guard(ty, store, expander, seen, budget);
  match store.type_kind(ty) {
    TypeKind::Union(members) => members
      .iter()
      .any(|member| matches_discriminant_value(*member, value, store, expander, seen, budget)),
    kind => match (kind, value) {
      (TypeKind::StringLiteral(name_id), LiteralValue::String(target)) => {
        store.name(name_id) == *target
      }
      (TypeKind::String, LiteralValue::String(_)) => true,
      (TypeKind::NumberLiteral(num), LiteralValue::Number(target)) => num.0.to_string() == *target,
      (TypeKind::Number, LiteralValue::Number(_)) => true,
      (TypeKind::BooleanLiteral(lit), LiteralValue::Boolean(target)) => lit == *target,
      (TypeKind::Boolean, LiteralValue::Boolean(_)) => true,
      (TypeKind::Null, LiteralValue::Null) => true,
      (TypeKind::Undefined, LiteralValue::Undefined) => true,
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
  let mut seen = HashSet::new();
  let mut budget = 64usize;
  narrow_by_in_check_inner(ty, prop, store, expander, &mut seen, &mut budget)
}

fn narrow_by_in_check_inner(
  ty: TypeId,
  prop: &str,
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  seen: &mut HashSet<TypeId>,
  budget: &mut usize,
) -> (TypeId, TypeId) {
  let primitives = store.primitive_ids();
  let original = store.canon(ty);
  let preserve_ref = matches!(store.type_kind(original), TypeKind::Ref { .. });
  let mut yes = Vec::new();
  let mut no = Vec::new();
  let ty = expand_ref_no_progress_guard(original, store, expander, seen, budget);
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_in_check_inner(member, prop, store, expander, seen, budget);
        if t != primitives.never {
          yes.push(t);
        }
        if f != primitives.never {
          no.push(f);
        }
      }
    }
    TypeKind::Intersection(members) => {
      let mut can_have = false;
      let mut can_lack = true;
      for member in members {
        let (t, f) = narrow_by_in_check_inner(member, prop, store, expander, seen, budget);
        can_have |= t != primitives.never;
        can_lack &= f != primitives.never;
      }
      if can_have {
        yes.push(ty);
      }
      if can_lack {
        no.push(ty);
      }
    }
    TypeKind::Array { .. } | TypeKind::Tuple(_) => {
      // Model only the high-value array properties we represent explicitly: a
      // numeric index signature and the `length` property.
      let is_numeric = prop
        .parse::<f64>()
        .map(|n| n.fract() == 0.0 && n >= 0.0)
        .unwrap_or(false);
      if prop == "length" || is_numeric {
        yes.push(ty);
      } else {
        no.push(ty);
      }
    }
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      let empty_name = store.intern_name(String::new());
      let probe_key = if prop.parse::<f64>().is_ok() {
        types_ts_interned::PropKey::Number(0)
      } else {
        types_ts_interned::PropKey::String(empty_name)
      };
      let has_indexer = shape
        .indexers
        .iter()
        .any(|idx| crate::type_queries::indexer_accepts_key(&probe_key, idx.key_type, store));
      let has_prop = shape.properties.iter().any(|p| match p.key {
        types_ts_interned::PropKey::String(name) => store.name(name) == prop,
        types_ts_interned::PropKey::Number(num) => num.to_string() == prop,
        _ => false,
      }) || has_indexer;
      if has_prop {
        yes.push(ty);
      } else {
        no.push(ty);
      }
    }
    // Unknown object-like types: preserve the original type on both branches
    // rather than incorrectly narrowing to `never`.
    TypeKind::Any
    | TypeKind::Unknown
    | TypeKind::EmptyObject
    | TypeKind::TypeParam(_)
    | TypeKind::Ref { .. } => {
      yes.push(ty);
      no.push(ty);
    }
    _ => no.push(ty),
  }
  let yes = store.union(yes);
  let no = store.union(no);
  if preserve_ref && ty != original {
    if yes == ty && no == primitives.never {
      (original, primitives.never)
    } else if yes == primitives.never && no == ty {
      (primitives.never, original)
    } else {
      (yes, no)
    }
  } else {
    (yes, no)
  }
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
    TypeKind::Any => (left_ty, left_ty),
    _ => {
      if let Some(target) = target {
        narrow_by_assignability(left_ty, target, store, relate)
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
  let mut seen = HashSet::new();
  let mut budget = 64usize;
  collect_instance_types(ty, store, expander, &mut targets, &mut seen, &mut budget);
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
  seen: &mut HashSet<TypeId>,
  budget: &mut usize,
) {
  let ty = expand_ref_no_progress_guard(ty, store, expander, seen, budget);
  match store.type_kind(ty) {
    TypeKind::Union(members) | TypeKind::Intersection(members) => {
      for member in members {
        collect_instance_types(member, store, expander, out, seen, budget);
      }
    }
    TypeKind::Callable { overloads } => {
      for sig in overloads {
        // `instanceof` narrows to the *instance* side of a constructor signature.
        // Our representation reuses `Callable` for both function and constructor
        // signatures, so be conservative and only treat clearly object-like
        // returns as potential instance types. This avoids accidentally using
        // ordinary function return types (e.g. `() => void`) as `instanceof`
        // narrowing targets.
        let ret = store.signature(sig).ret;
        match store.type_kind(ret) {
          TypeKind::Void
          | TypeKind::Undefined
          | TypeKind::Null
          | TypeKind::Never
          | TypeKind::String
          | TypeKind::StringLiteral(_)
          | TypeKind::TemplateLiteral(_)
          | TypeKind::Number
          | TypeKind::NumberLiteral(_)
          | TypeKind::Boolean
          | TypeKind::BooleanLiteral(_)
          | TypeKind::BigInt
          | TypeKind::BigIntLiteral(_)
          | TypeKind::Symbol
          | TypeKind::UniqueSymbol => {}
          _ => out.push(ret),
        }
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
