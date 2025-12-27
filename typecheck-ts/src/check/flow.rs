//! Flow-sensitive environment utilities for per-body analysis.

use std::collections::{HashMap, HashSet};

use hir_js::NameId;
use types_ts_interned::{TypeId, TypeStore};

use super::flow_bindings::FlowBindingId;
use super::flow_narrow::Facts;

/// Unique key for a flow-tracked binding, distinguishing shadowed locals even
/// when they share the same name.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum BindingKey {
  Symbol(FlowBindingId),
  External(NameId),
}

impl BindingKey {
  pub fn name(self) -> Option<NameId> {
    match self {
      BindingKey::External(name) => Some(name),
      BindingKey::Symbol(_) => None,
    }
  }
}

/// Segment within an access path (currently limited to static property keys).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PathSegment {
  String(String),
  Number(String),
}

/// Canonical key for flow facts and environment entries. Tracks a root local and
/// zero or more property segments (e.g. `x`, `x.kind`, `x.meta.kind`).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FlowKey {
  pub root: BindingKey,
  pub segments: Vec<PathSegment>,
}

impl FlowKey {
  pub fn root(root: BindingKey) -> Self {
    Self {
      root,
      segments: Vec::new(),
    }
  }

  pub fn with_segment(&self, segment: PathSegment) -> Self {
    let mut segments = self.segments.clone();
    segments.push(segment);
    FlowKey {
      root: self.root,
      segments,
    }
  }

  /// Returns true if `self` is a prefix (including exact match) of `other`.
  pub fn is_prefix_of(&self, other: &FlowKey) -> bool {
    self.root == other.root && other.segments.starts_with(&self.segments)
  }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum InitState {
  Unassigned,
  MaybeAssigned,
  Assigned,
}

impl InitState {
  pub fn join(self, other: InitState) -> InitState {
    match (self, other) {
      (InitState::Assigned, InitState::Assigned) => InitState::Assigned,
      (InitState::Unassigned, InitState::Unassigned) => InitState::Unassigned,
      _ => InitState::MaybeAssigned,
    }
  }
}

/// Per-point variable environment used during flow-sensitive checks.
#[derive(Clone, Debug, Default)]
pub struct Env {
  vars: HashMap<FlowKey, TypeId>,
  init: HashMap<BindingKey, InitState>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      vars: HashMap::new(),
      init: HashMap::new(),
    }
  }

  pub fn with_initial(initial: &HashMap<BindingKey, TypeId>) -> Self {
    let mut env = Env::new();
    for (key, ty) in initial.iter() {
      env.vars.insert(FlowKey::root(*key), *ty);
      env.init.insert(*key, InitState::Assigned);
    }
    env
  }

  pub fn get_var(&self, name: BindingKey) -> Option<TypeId> {
    self.get_path(&FlowKey::root(name))
  }

  pub fn set_var(&mut self, name: BindingKey, ty: TypeId) {
    let key = FlowKey::root(name);
    self.invalidate_prefix(&key);
    self.vars.insert(key, ty);
  }

  pub fn get_path(&self, path: &FlowKey) -> Option<TypeId> {
    self.vars.get(path).copied()
  }

  pub fn get(&self, name: BindingKey) -> Option<TypeId> {
    self.get_var(name)
  }

  pub fn set(&mut self, name: BindingKey, ty: TypeId) {
    self.set_var(name, ty);
  }

  pub fn set_path(&mut self, path: FlowKey, ty: TypeId) {
    self.invalidate_prefix(&path);
    self.vars.insert(path, ty);
  }

  pub fn invalidate_prefix(&mut self, prefix: &FlowKey) {
    self.vars.retain(|key, _| !prefix.is_prefix_of(key));
  }

  pub fn invalidate_all(&mut self) {
    self.vars.clear();
  }

  /// Remove any tracked information for a variable, clearing previous narrowings.
  pub fn invalidate(&mut self, name: BindingKey) {
    self.invalidate_prefix(&FlowKey::root(name));
  }

  /// Clear any tracked property narrowings rooted at `name`. Currently there are
  /// no separate property entries, but this hook is used to invalidate access
  /// paths when writes occur.
  pub fn clear_properties_of(&mut self, name: BindingKey) {
    self
      .vars
      .retain(|key, _| key.root != name || key.segments.is_empty());
  }

  /// Clear all tracked property-specific narrowings.
  pub fn clear_all_properties(&mut self) {
    self.vars.retain(|key, _| key.segments.is_empty());
  }

  pub fn mark_assigned(&mut self, name: NameId) {
    self
      .init
      .insert(BindingKey::External(name), InitState::Assigned);
  }

  pub fn mark_unassigned(&mut self, name: NameId) {
    self
      .init
      .insert(BindingKey::External(name), InitState::Unassigned);
  }

  pub fn set_init_state(&mut self, key: BindingKey, state: InitState) {
    self.init.insert(key, state);
  }

  pub fn init_state(&self, key: BindingKey) -> InitState {
    self
      .init
      .get(&key)
      .copied()
      .unwrap_or(InitState::Unassigned)
  }

  pub fn apply_facts(&mut self, facts: &Facts) {
    for (name, ty) in facts.truthy.iter() {
      self.vars.insert(name.clone(), *ty);
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(name.clone(), *ty);
    }
  }

  /// Apply falsy-directed facts to the environment, also honoring assertions
  /// that hold regardless of branch.
  pub fn apply_falsy(&mut self, facts: &Facts) {
    for (name, ty) in facts.falsy.iter() {
      self.vars.insert(name.clone(), *ty);
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(name.clone(), *ty);
    }
  }

  pub fn apply_map(&mut self, facts: &HashMap<FlowKey, TypeId>) {
    for (name, ty) in facts.iter() {
      self.vars.insert(name.clone(), *ty);
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
          self.vars.insert(name.clone(), *ty);
          changed = true;
        }
      }
    }
    let mut all_keys: HashSet<BindingKey> = self.init.keys().copied().collect();
    all_keys.extend(other.init.keys().copied());
    for key in all_keys {
      let left = self
        .init
        .get(&key)
        .copied()
        .unwrap_or(InitState::Unassigned);
      let right = other
        .init
        .get(&key)
        .copied()
        .unwrap_or(InitState::Unassigned);
      let joined = left.join(right);
      if left != joined {
        self.init.insert(key, joined);
        changed = true;
      }
    }
    changed
  }
}
