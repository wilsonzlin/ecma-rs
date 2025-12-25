//! Flow graph utilities for per-body analysis.
//!
//! The current implementation intentionally keeps the flow model lightweight:
//! environments are maps of variable names to narrowed [`TypeId`]s, merged via
//! union at joins. The `FlowState` is a helper used by `check_body` to thread
//! these environments through statement and expression evaluation.

use std::collections::HashMap;

use super::narrow::Facts;
use crate::{BuiltinTypes, TypeId, TypeStore};

/// Per-point variable environment used during flow-sensitive checks.
#[derive(Clone, Debug, Default)]
pub struct Env {
  vars: HashMap<String, TypeId>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      vars: HashMap::new(),
    }
  }

  pub fn get(&self, name: &str) -> Option<TypeId> {
    self.vars.get(name).copied()
  }

  pub fn set(&mut self, name: String, ty: TypeId) {
    self.vars.insert(name, ty);
  }

  pub fn apply_facts(&mut self, facts: &Facts) {
    for (name, ty) in facts.truthy.iter() {
      self.vars.insert(name.clone(), *ty);
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(name.clone(), *ty);
    }
  }

  pub fn merge(&mut self, other: &Env, store: &mut TypeStore, builtin: &BuiltinTypes) {
    for (name, ty) in other.vars.iter() {
      self
        .vars
        .entry(name.clone())
        .and_modify(|existing| *existing = store.union(vec![*existing, *ty], builtin))
        .or_insert(*ty);
    }
  }
}
