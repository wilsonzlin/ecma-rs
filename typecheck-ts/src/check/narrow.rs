//! Helpers for computing flow-sensitive narrowing facts.
//!
//! The lightweight checker uses a bounded lattice of "facts" mapping variable
//! names to narrowed [`TypeId`]s. Facts are merged at control-flow joins by
//! taking the union of compatible types, ensuring convergence even in the
//! presence of loops.

use bumpalo::{collections::Vec as BumpVec, Bump};
use std::collections::HashMap;

use super::body::BodyCaches;
use crate::program::{BuiltinTypes, TypeId, TypeKind, TypeStore};

type SymbolName = String;

/// Narrowing facts produced by evaluating an expression in a boolean context.
///
/// - `truthy` applies when the expression evaluates to a truthy value.
/// - `falsy` applies when the expression evaluates to a falsy value.
/// - `assertions` apply unconditionally after the expression completes
///   successfully (used for assertion functions).
#[derive(Debug)]
pub struct Facts<'a> {
  pub truthy: FactMap<'a>,
  pub falsy: FactMap<'a>,
  pub assertions: FactMap<'a>,
}

#[derive(Debug)]
pub struct FactMap<'a> {
  entries: BumpVec<'a, (SymbolName, TypeId)>,
}

impl<'a> FactMap<'a> {
  pub fn new_in(bump: &'a Bump) -> Self {
    FactMap {
      entries: BumpVec::new_in(bump),
    }
  }

  pub fn insert(&mut self, key: SymbolName, value: TypeId) {
    if let Some((_, existing)) = self.entries.iter_mut().find(|(k, _)| *k == key) {
      *existing = value;
    } else {
      self.entries.push((key, value));
    }
  }

  pub fn iter(&self) -> impl Iterator<Item = &(SymbolName, TypeId)> {
    self.entries.iter()
  }

  pub fn is_empty(&self) -> bool {
    self.entries.is_empty()
  }
}

impl<'a> Facts<'a> {
  pub fn new_in(bump: &'a Bump) -> Self {
    Facts {
      truthy: FactMap::new_in(bump),
      falsy: FactMap::new_in(bump),
      assertions: FactMap::new_in(bump),
    }
  }

  /// Merge another set of facts into this one, joining types with union.
  pub fn merge(
    &mut self,
    other: Facts<'a>,
    store: &mut TypeStore,
    builtin: &BuiltinTypes,
    caches: &BodyCaches,
  ) {
    merge_map(&mut self.truthy, other.truthy, store, builtin, caches);
    merge_map(&mut self.falsy, other.falsy, store, builtin, caches);
    merge_map(
      &mut self.assertions,
      other.assertions,
      store,
      builtin,
      caches,
    );
  }
}

fn merge_map(
  target: &mut FactMap<'_>,
  other: FactMap<'_>,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
  caches: &BodyCaches,
) {
  for (name, ty) in other.entries {
    if let Some((_, existing)) = target.entries.iter_mut().find(|(k, _)| k == &name) {
      *existing = caches.union_from_iter(store, builtin, [*existing, ty]);
    } else {
      target.entries.push((name, ty));
    }
  }
}

/// Compute the truthy and falsy types for a given variable type.
pub fn truthy_falsy_types(
  ty: TypeId,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
  caches: &BodyCaches,
) -> (TypeId, TypeId) {
  let kind = store.kind(ty).clone();
  match kind {
    TypeKind::Union(members) => {
      let mut truthy = Vec::new();
      let mut falsy = Vec::new();
      for member in members {
        let (t, f) = truthy_falsy_types(member, store, builtin, caches);
        if t != builtin.never {
          truthy.push(t);
        }
        if f != builtin.never {
          falsy.push(f);
        }
      }
      (
        caches.union_from_iter(store, builtin, truthy),
        caches.union_from_iter(store, builtin, falsy),
      )
    }
    TypeKind::Null | TypeKind::Undefined => (builtin.never, ty),
    TypeKind::LiteralBoolean(false) => (builtin.never, ty),
    TypeKind::LiteralNumber(n) if n.parse::<f64>().ok().map_or(false, |v| v == 0.0) => {
      (builtin.never, ty)
    }
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
  caches: &BodyCaches,
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
      (
        caches.union_from_iter(store, builtin, yes),
        caches.union_from_iter(store, builtin, no),
      )
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
  caches: &BodyCaches,
) -> (TypeId, TypeId) {
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_discriminant(member, prop, value, store, builtin, caches);
        if t != builtin.never {
          yes.push(t);
        }
        if f != builtin.never {
          no.push(f);
        }
      }
    }
    TypeKind::Object(_) => match super::super::lookup_property_type(store, ty, prop, builtin) {
      Some(prop_ty) => {
        let prop_kind = store.kind(prop_ty).clone();
        let matches = match prop_kind {
          TypeKind::LiteralString(name) => name == value,
          TypeKind::String => true,
          _ => false,
        };
        if matches {
          yes.push(ty);
        } else {
          no.push(ty);
        }
      }
      None => no.push(ty),
    },
    _ => no.push(ty),
  }

  (
    caches.union_from_iter(store, builtin, yes),
    caches.union_from_iter(store, builtin, no),
  )
}

/// Narrow by an `in` check (`"prop" in x`).
pub fn narrow_by_in_check(
  ty: TypeId,
  prop: &str,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
  caches: &BodyCaches,
) -> (TypeId, TypeId) {
  let mut yes = Vec::new();
  let mut no = Vec::new();
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      for member in members {
        let (t, f) = narrow_by_in_check(member, prop, store, builtin, caches);
        if t != builtin.never {
          yes.push(t);
        }
        if f != builtin.never {
          no.push(f);
        }
      }
    }
    TypeKind::Object(_) => {
      if super::super::lookup_property_type(store, ty, prop, builtin).is_some() {
        yes.push(ty);
      } else {
        no.push(ty);
      }
    }
    _ => no.push(ty),
  }
  (
    caches.union_from_iter(store, builtin, yes),
    caches.union_from_iter(store, builtin, no),
  )
}

/// Narrow by an `instanceof` check, keeping only object-like members.
pub fn narrow_by_instanceof(
  ty: TypeId,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
  caches: &BodyCaches,
) -> (TypeId, TypeId) {
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_instanceof(member, store, builtin, caches);
        if y != builtin.never {
          yes.push(y);
        }
        if n != builtin.never {
          no.push(n);
        }
      }
      (
        caches.union_from_iter(store, builtin, yes),
        caches.union_from_iter(store, builtin, no),
      )
    }
    TypeKind::Object(_) | TypeKind::Array(_) | TypeKind::Function { .. } => (ty, builtin.never),
    _ => (builtin.never, ty),
  }
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
