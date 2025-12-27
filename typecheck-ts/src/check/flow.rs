//! Flow-sensitive environment utilities for per-body analysis.

use std::collections::HashMap;

use semantic_js::ts::SymbolId;
use types_ts_interned::{TypeId, TypeStore};

use super::flow_narrow::Facts;

pub type FlowBindingId = SymbolId;

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
  pub root: FlowBindingId,
  pub segments: Vec<PathSegment>,
}

impl FlowKey {
  pub fn root(root: FlowBindingId) -> Self {
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

/// Per-variable state tracked by the flow-sensitive analysis.
#[derive(Clone, Copy, Debug)]
pub struct VarState {
  pub ty: TypeId,
  pub assigned: bool,
}

impl VarState {
  pub fn new(ty: TypeId, assigned: bool) -> Self {
    Self { ty, assigned }
  }
}

/// Per-point variable environment used during flow-sensitive checks.
#[derive(Clone, Debug, Default)]
pub struct Env {
  vars: HashMap<FlowKey, VarState>,
}

impl Env {
  pub fn new() -> Self {
    Env {
      vars: HashMap::new(),
    }
  }

  pub fn with_initial(initial: &HashMap<FlowBindingId, TypeId>) -> Self {
    let mut env = Env::new();
    env.vars.extend(
      initial
        .iter()
        .map(|(k, v)| (FlowKey::root(*k), VarState::new(*v, true))),
    );
    env
  }

  pub fn get_var(&self, name: FlowBindingId) -> Option<TypeId> {
    self.get_path(&FlowKey::root(name))
  }

  pub fn get_var_state(&self, name: FlowBindingId) -> Option<VarState> {
    self.get_path_state(&FlowKey::root(name))
  }

  pub fn get(&self, name: FlowBindingId) -> Option<TypeId> {
    self.get_var(name)
  }

  pub fn set_var(&mut self, name: FlowBindingId, ty: TypeId) {
    self.set_var_with_assigned(name, ty, true);
  }

  pub fn set(&mut self, name: FlowBindingId, ty: TypeId) {
    self.set_var(name, ty);
  }

  pub fn set_var_with_assigned(&mut self, name: FlowBindingId, ty: TypeId, assigned: bool) {
    let key = FlowKey::root(name);
    self.invalidate_prefix(&key);
    self.vars.insert(key, VarState::new(ty, assigned));
  }

  pub fn set_with_assigned(&mut self, name: FlowBindingId, ty: TypeId, assigned: bool) {
    self.set_var_with_assigned(name, ty, assigned);
  }

  pub fn get_path(&self, path: &FlowKey) -> Option<TypeId> {
    self.vars.get(path).map(|state| state.ty)
  }

  pub fn get_path_state(&self, path: &FlowKey) -> Option<VarState> {
    self.vars.get(path).copied()
  }

  pub fn set_path(&mut self, path: FlowKey, ty: TypeId) {
    self.set_path_with_assigned(path, ty, true);
  }

  pub fn set_path_with_assigned(&mut self, path: FlowKey, ty: TypeId, assigned: bool) {
    self.invalidate_prefix(&path);
    self.vars.insert(path, VarState::new(ty, assigned));
  }

  pub fn invalidate_prefix(&mut self, prefix: &FlowKey) {
    self.vars.retain(|key, _| !prefix.is_prefix_of(key));
  }

  pub fn invalidate_all(&mut self) {
    self.vars.clear();
  }

  /// Remove any tracked information for a variable, clearing previous narrowings.
  pub fn invalidate(&mut self, name: FlowBindingId) {
    self.invalidate_prefix(&FlowKey::root(name));
  }

  /// Clear any tracked property narrowings rooted at `name`. Currently there are
  /// no separate property entries, but this hook is used to invalidate access
  /// paths when writes occur.
  pub fn clear_properties_of(&mut self, name: FlowBindingId) {
    self
      .vars
      .retain(|key, _| key.root != name || key.segments.is_empty());
  }

  /// Clear all tracked property-specific narrowings.
  pub fn clear_all_properties(&mut self) {
    self.vars.retain(|key, _| key.segments.is_empty());
  }

  pub fn apply_facts(&mut self, facts: &Facts) {
    for (name, ty) in facts.truthy.iter() {
      self.vars.insert(name.clone(), VarState::new(*ty, true));
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(name.clone(), VarState::new(*ty, true));
    }
  }

  /// Apply falsy-directed facts to the environment, also honoring assertions
  /// that hold regardless of branch.
  pub fn apply_falsy(&mut self, facts: &Facts) {
    for (name, ty) in facts.falsy.iter() {
      self.vars.insert(name.clone(), VarState::new(*ty, true));
    }
    for (name, ty) in facts.assertions.iter() {
      self.vars.insert(name.clone(), VarState::new(*ty, true));
    }
  }

  pub fn apply_map(&mut self, facts: &HashMap<FlowKey, TypeId>) {
    for (name, ty) in facts.iter() {
      self.vars.insert(name.clone(), VarState::new(*ty, true));
    }
  }

  pub fn merge(&mut self, other: &Env, store: &TypeStore) {
    self.merge_from(other, store);
  }

  /// Join another environment into this one, returning whether any mapping
  /// changed. Types are merged using union to conservatively approximate all
  /// reaching flows. A variable is only considered definitely assigned if all
  /// incoming flows mark it as assigned.
  pub fn merge_from(&mut self, other: &Env, store: &TypeStore) -> bool {
    let mut changed = false;
    for (name, other_state) in other.vars.iter() {
      match self.vars.get_mut(name) {
        Some(existing) => {
          let next_ty = store.union(vec![existing.ty, other_state.ty]);
          let assigned = existing.assigned && other_state.assigned;
          if next_ty != existing.ty || assigned != existing.assigned {
            existing.ty = next_ty;
            existing.assigned = assigned;
            changed = true;
          }
        }
        None => {
          self
            .vars
            .insert(name.clone(), VarState::new(other_state.ty, false));
          changed = true;
        }
      }
    }
    changed
  }
}
