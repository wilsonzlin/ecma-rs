use std::collections::HashMap;

use crate::{BuiltinTypes, TypeId, TypeKind, TypeStore};

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

/// Literal value used for equality-based narrowing.
#[derive(Clone, Debug)]
pub enum LiteralValue {
  String(String),
  Number(String),
  Boolean(bool),
  Null,
  Undefined,
}

/// Narrow by an equality comparison with a literal value.
pub fn narrow_by_literal(
  ty: TypeId,
  lit: &LiteralValue,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_literal(member, lit, store, builtin);
        if y != builtin.never {
          yes.push(y);
        }
        if n != builtin.never {
          no.push(n);
        }
      }
      (store.union(yes, builtin), store.union(no, builtin))
    }
    TypeKind::LiteralString(name) => match lit {
      LiteralValue::String(target) if name == *target => (ty, builtin.never),
      LiteralValue::String(_) => (builtin.never, ty),
      _ => (builtin.never, ty),
    },
    TypeKind::String => match lit {
      LiteralValue::String(target) => (store.literal_string(target.clone()), ty),
      _ => (builtin.never, ty),
    },
    TypeKind::LiteralNumber(value) => match lit {
      LiteralValue::Number(target) if value == *target => (ty, builtin.never),
      LiteralValue::Number(_) => (builtin.never, ty),
      _ => (builtin.never, ty),
    },
    TypeKind::Number => match lit {
      LiteralValue::Number(target) => (store.literal_number(target.clone()), ty),
      _ => (builtin.never, ty),
    },
    TypeKind::LiteralBoolean(value) => match lit {
      LiteralValue::Boolean(target) if value == *target => (ty, builtin.never),
      LiteralValue::Boolean(_) => (builtin.never, ty),
      _ => (builtin.never, ty),
    },
    TypeKind::Boolean => match lit {
      LiteralValue::Boolean(target) => (store.literal_boolean(*target), ty),
      _ => (builtin.never, ty),
    },
    TypeKind::Null => match lit {
      LiteralValue::Null => (ty, builtin.never),
      _ => (builtin.never, ty),
    },
    TypeKind::Undefined => match lit {
      LiteralValue::Undefined => (ty, builtin.never),
      _ => (builtin.never, ty),
    },
    _ => (builtin.never, ty),
  }
}

/// Compute the truthy and falsy types for a given variable type.
pub fn truthy_falsy_types(
  ty: TypeId,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  match store.kind(ty).clone() {
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
    TypeKind::LiteralBoolean(true) => (ty, builtin.never),
    TypeKind::LiteralNumber(value) => {
      let parsed = value.parse::<f64>().unwrap_or_default();
      if parsed == 0.0 || parsed.is_nan() {
        (builtin.never, ty)
      } else {
        (ty, builtin.never)
      }
    }
    TypeKind::LiteralString(text) if text.is_empty() => (builtin.never, ty),
    TypeKind::Boolean => (store.literal_boolean(true), store.literal_boolean(false)),
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
    TypeKind::Null | TypeKind::Object(_) | TypeKind::Array(_) => target == "object",
    _ => false,
  };

  match store.kind(ty).clone() {
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
      if matches(store.kind(ty)) {
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
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (t, f) = narrow_by_discriminant(member, prop, value, store, builtin);
        if t != builtin.never {
          yes.push(t);
        }
        if f != builtin.never {
          no.push(f);
        }
      }
      (store.union(yes, builtin), store.union(no, builtin))
    }
    TypeKind::Object(obj) => {
      let mut matched = false;
      let mut remaining = Vec::new();
      if let Some(property) = obj.props.get(prop) {
        match store.kind(property.typ) {
          TypeKind::LiteralString(name) if name == value => matched = true,
          _ => {}
        }
      }
      if matched {
        (ty, builtin.never)
      } else {
        remaining.push(ty);
        (builtin.never, store.union(remaining, builtin))
      }
    }
    _ => (builtin.never, ty),
  }
}

/// Narrow via the `in` operator.
pub fn narrow_by_in_check(
  ty: TypeId,
  prop: &str,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (t, f) = narrow_by_in_check(member, prop, store, builtin);
        if t != builtin.never {
          yes.push(t);
        }
        if f != builtin.never {
          no.push(f);
        }
      }
      (store.union(yes, builtin), store.union(no, builtin))
    }
    TypeKind::Object(obj) => {
      if obj.props.contains_key(prop) {
        (ty, builtin.never)
      } else {
        (builtin.never, ty)
      }
    }
    _ => (builtin.never, ty),
  }
}

/// Narrow by an `instanceof` check. This simplified helper treats all object
/// types as matching and primitives as non-matching.
pub fn narrow_by_instanceof(
  ty: TypeId,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_instanceof(member, store, builtin);
        if y != builtin.never {
          yes.push(y);
        }
        if n != builtin.never {
          no.push(n);
        }
      }
      (store.union(yes, builtin), store.union(no, builtin))
    }
    TypeKind::Object(_) => (ty, builtin.never),
    _ => (builtin.never, ty),
  }
}

/// Narrow a value based on a type predicate assertion.
pub fn narrow_by_asserted(
  ty: TypeId,
  asserted: TypeId,
  store: &mut TypeStore,
  builtin: &BuiltinTypes,
) -> (TypeId, TypeId) {
  match store.kind(ty).clone() {
    TypeKind::Union(members) => {
      let mut yes = Vec::new();
      let mut no = Vec::new();
      for member in members {
        let (y, n) = narrow_by_asserted(member, asserted, store, builtin);
        if y != builtin.never {
          yes.push(y);
        }
        if n != builtin.never {
          no.push(n);
        }
      }
      (store.union(yes, builtin), store.union(no, builtin))
    }
    _ => {
      if ty == asserted {
        (ty, builtin.never)
      } else {
        (asserted, ty)
      }
    }
  }
}
