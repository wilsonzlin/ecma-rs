//! Helpers for computing flow-sensitive narrowing facts.
//!
//! The lightweight checker uses a bounded lattice of "facts" mapping variable
//! names to narrowed [`TypeId`]s. Facts are merged at control-flow joins by
//! taking the union of compatible types, ensuring convergence even in the
//! presence of loops.

use std::collections::HashMap;

use crate::program::{BuiltinTypes, TypeId, TypeKind, TypeStore};

/// Narrowing facts produced by evaluating an expression in a boolean context.
///
/// - `truthy` applies when the expression evaluates to a truthy value.
/// - `falsy` applies when the expression evaluates to a falsy value.
/// - `assertions` apply unconditionally after the expression completes
///   successfully (used for assertion functions).
#[derive(Clone, Debug, Default)]
pub struct Facts {
  pub truthy: HashMap<String, TypeId>,
  pub falsy: HashMap<String, TypeId>,
  pub assertions: HashMap<String, TypeId>,
}

impl Facts {
  /// Merge another set of facts into this one, joining types with union.
  pub fn merge(&mut self, other: Facts, store: &mut TypeStore, builtin: &BuiltinTypes) {
    for (k, v) in other.truthy {
      self
        .truthy
        .entry(k)
        .and_modify(|existing| *existing = store.union(vec![*existing, v], builtin))
        .or_insert(v);
    }
    for (k, v) in other.falsy {
      self
        .falsy
        .entry(k)
        .and_modify(|existing| *existing = store.union(vec![*existing, v], builtin))
        .or_insert(v);
    }
    for (k, v) in other.assertions {
      self
        .assertions
        .entry(k)
        .and_modify(|existing| *existing = store.union(vec![*existing, v], builtin))
        .or_insert(v);
    }
  }
}

/// Compute the truthy and falsy types for a given variable type.
pub fn truthy_falsy_types(
  ty: TypeId,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  let kind = store.kind(ty).clone();
  match kind {
    TypeKind::Union(members) => {
      let mut truthy = Vec::new();
      let mut falsy = Vec::new();
      for member in members {
        let (t, f) = truthy_falsy_types(member, store, builtin);
        if t != builtin.never {
          truthy.push(t);
        }
        if f != builtin.never {
          falsy.push(f);
        }
      }
      (store.union(truthy, builtin), store.union(falsy, builtin))
    }
    TypeKind::Null | TypeKind::Undefined => (builtin.never, ty),
    TypeKind::LiteralBoolean(false) => (builtin.never, ty),
    TypeKind::LiteralNumber(n) if n == "0" => (builtin.never, ty),
    TypeKind::LiteralString(s) if s.is_empty() => (builtin.never, ty),
    _ => (ty, builtin.never),
  }
}

/// Narrow a variable by a typeof comparison (e.g. `typeof x === "string"`).
pub fn narrow_by_typeof(
  ty: TypeId,
  target: &str,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  let matches = |k: &TypeKind| match k {
    TypeKind::String | TypeKind::LiteralString(_) => target == "string",
    TypeKind::Number | TypeKind::LiteralNumber(_) => target == "number",
    TypeKind::Boolean | TypeKind::LiteralBoolean(_) => target == "boolean",
    TypeKind::Undefined => target == "undefined",
    TypeKind::Null => target == "object",
    TypeKind::Object(_) => target == "object",
    _ => false,
  };

  let kind = store.kind(ty).clone();
  match kind {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        if matches(store.kind(member)) {
          yes.push(member);
        } else {
          no.push(member);
        }
      }
      (store.union(yes, builtin), store.union(no, builtin))
    }
    _ => {
      if matches(&kind) {
        (ty, builtin.never)
      } else {
        (builtin.never, ty)
      }
    }
  }
}

/// Narrow by a discriminant property check (e.g. `x.kind === "foo"`).
pub fn narrow_by_discriminant(
  ty: TypeId,
  prop: &str,
  value: &str,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_discriminant(member, prop, value, store, builtin);
        if t != builtin.never {
          yes.push(t);
        }
        if f != builtin.never {
          no.push(f);
        }
      }
    }
    TypeKind::Object(obj) => {
      if let Some(prop_data) = obj.props.get(prop) {
        let matches = match store.kind(prop_data.typ) {
          TypeKind::LiteralString(s) => s == value,
          TypeKind::String => true,
          _ => false,
        };
        if matches {
          yes.push(ty);
        } else {
          no.push(ty);
        }
      } else {
        no.push(ty);
      }
    }
    _ => no.push(ty),
  }

  (store.union(yes, builtin), store.union(no, builtin))
}

/// Narrow by an `in` check (`"prop" in x`).
pub fn narrow_by_in_check(
  ty: TypeId,
  prop: &str,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_in_check(member, prop, store, builtin);
        if t != builtin.never {
          yes.push(t);
        }
        if f != builtin.never {
          no.push(f);
        }
      }
    }
    TypeKind::Object(obj) => {
      let has_prop = if obj.props.contains_key(prop) {
        true
      } else if obj.string_index.is_some() {
        true
      } else if prop.parse::<usize>().is_ok() {
        obj.number_index.is_some()
      } else {
        false
      };
      if has_prop {
        yes.push(ty);
      } else {
        no.push(ty);
      }
    }
    _ => no.push(ty),
  }
  (store.union(yes, builtin), store.union(no, builtin))
}

/// Merge two variable environments using union to join types.
pub fn merge_envs(
  left: &HashMap<String, TypeId>,
  right: &HashMap<String, TypeId>,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> HashMap<String, TypeId> {
  let mut out = HashMap::new();
  for (k, v) in left {
    out.insert(k.clone(), *v);
  }
  for (k, v) in right {
    out
      .entry(k.clone())
      .and_modify(|existing| *existing = store.union(vec![*existing, *v], builtin))
      .or_insert(*v);
  }
  out
}
