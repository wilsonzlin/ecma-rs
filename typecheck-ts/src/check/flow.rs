//! Flow-sensitive environment utilities for per-body analysis.

use std::collections::HashMap;

use hir_js::NameId;
use types_ts_interned::{TypeId, TypeStore};

use super::flow_narrow::Facts;

/// Per-point variable environment used during flow-sensitive checks.
#[derive(Clone, Debug, Default)]
pub struct Env {
  vars: HashMap<NameId, TypeId>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      vars: HashMap::new(),
    }
  }

  pub fn with_initial(initial: &HashMap<NameId, TypeId>) -> Self {
    let mut env = Env::new();
    env.vars.extend(initial.iter().map(|(k, v)| (*k, *v)));
    env
  }

  pub fn get(&self, name: NameId) -> Option<TypeId> {
    self.vars.get(&name).copied()
  }

  pub fn set(&mut self, name: NameId, ty: TypeId) {
    self.vars.insert(name, ty);
  }

  pub fn apply_facts(&mut self, facts: &Facts) {
    for (name, ty) in facts.truthy.iter() {
      self.vars.insert(*name, *ty);
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(*name, *ty);
    }
  }

  /// Apply falsy-directed facts to the environment, also honoring assertions
  /// that hold regardless of branch.
  pub fn apply_falsy(&mut self, facts: &Facts) {
    for (name, ty) in facts.falsy.iter() {
      self.vars.insert(*name, *ty);
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(*name, *ty);
    }
  }

  pub fn apply_map(&mut self, facts: &HashMap<NameId, TypeId>) {
    for (name, ty) in facts.iter() {
      self.vars.insert(*name, *ty);
    }
  }

  pub fn merge(&mut self, other: &Env, store: &TypeStore) {
    self.merge_from(other, store);
  }

  /// Join another environment into this one, returning whether any mapping
  /// changed. Types are merged using union to conservatively approximate all
  /// reaching flows.
  pub fn merge_from(&mut self, other: &Env, store: &TypeStore) -> bool {
    let mut changed = false;
    for (name, ty) in other.vars.iter() {
      match self.vars.get_mut(name) {
        Some(existing) => {
          let next = store.union(vec![*existing, *ty]);
          if next != *existing {
            *existing = next;
            changed = true;
          }
        }
        None => {
          self.vars.insert(*name, *ty);
          changed = true;
        }
      }
    }
    changed
  }
}
