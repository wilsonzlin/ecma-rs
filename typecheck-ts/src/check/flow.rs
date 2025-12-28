//! Flow-sensitive environment utilities for per-body analysis.

use std::collections::{HashMap, HashSet};

use semantic_js::ts::SymbolId;
use types_ts_interned::{TypeId, TypeStore};

pub type FlowBindingId = SymbolId;
use super::flow_narrow::Facts;

/// Path segment for an object/property access tracked during flow analysis.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum PathSegment {
  String(String),
  Number(String),
}

/// Stable key representing a binding and optional property path.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct FlowKey {
  pub root: FlowBindingId,
  pub segments: Vec<PathSegment>,
}

impl FlowKey {
  pub fn root(root: FlowBindingId) -> Self {
    FlowKey {
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

  fn is_prefix_of(&self, other: &FlowKey) -> bool {
    self.root == other.root && other.segments.starts_with(&self.segments)
  }
}

/// Flow-tracked state for a particular binding path.
#[derive(Clone, Copy, Debug)]
pub struct PathState {
  pub ty: TypeId,
  pub assigned: bool,
}

/// Per-point variable environment used during flow-sensitive checks.
#[derive(Clone, Debug)]
pub struct Env {
  unknown: TypeId,
  paths: HashMap<FlowKey, PathState>,
}

impl Env {
  pub fn new(unknown: TypeId) -> Self {
    Env {
      unknown,
      paths: HashMap::new(),
    }
  }

  pub fn with_initial(initial: &HashMap<FlowBindingId, TypeId>, unknown: TypeId) -> Self {
    let mut env = Env::new(unknown);
    for (binding, ty) in initial {
      env.set_var_with_assigned(*binding, *ty, true);
    }
    env
  }

  pub fn get_path_state(&self, key: &FlowKey) -> Option<PathState> {
    self.paths.get(key).copied()
  }

  pub fn get_path(&self, key: &FlowKey) -> Option<TypeId> {
    self.get_path_state(key).map(|s| s.ty)
  }

  pub fn set_var(&mut self, binding: FlowBindingId, ty: TypeId) {
    self.set_var_with_assigned(binding, ty, true);
  }

  pub fn set_var_with_assigned(&mut self, binding: FlowBindingId, ty: TypeId, assigned: bool) {
    self
      .paths
      .insert(FlowKey::root(binding), PathState { ty, assigned });
  }

  pub fn set_path(&mut self, key: FlowKey, ty: TypeId) {
    self.set_path_with_assigned(key, ty, true);
  }

  pub fn set_path_with_assigned(&mut self, key: FlowKey, ty: TypeId, assigned: bool) {
    self.paths.insert(key, PathState { ty, assigned });
  }

  pub fn apply_facts(&mut self, facts: &Facts) {
    for (key, ty) in facts.truthy.iter().chain(facts.assertions.iter()) {
      self.paths.insert(
        key.clone(),
        PathState {
          ty: *ty,
          assigned: true,
        },
      );
    }
  }

  /// Apply falsy-directed facts to the environment, also honoring assertions
  /// that hold regardless of branch.
  pub fn apply_falsy(&mut self, facts: &Facts) {
    for (key, ty) in facts.falsy.iter().chain(facts.assertions.iter()) {
      self.paths.insert(
        key.clone(),
        PathState {
          ty: *ty,
          assigned: true,
        },
      );
    }
  }

  pub fn apply_map(&mut self, facts: &HashMap<FlowKey, TypeId>) {
    for (key, ty) in facts.iter() {
      self.paths.insert(
        key.clone(),
        PathState {
          ty: *ty,
          assigned: true,
        },
      );
    }
  }

  pub fn invalidate_prefix(&mut self, key: &FlowKey) {
    for (path, state) in self.paths.iter_mut() {
      if key.is_prefix_of(path) {
        state.ty = self.unknown;
      }
    }
  }

  pub fn invalidate_all(&mut self) {
    for state in self.paths.values_mut() {
      state.ty = self.unknown;
    }
  }

  /// Join another environment into this one, returning whether any mapping
  /// changed. Types are merged using union to conservatively approximate all
  /// reaching flows.
  pub fn merge_from(&mut self, other: &Env, store: &TypeStore) -> bool {
    let mut changed = false;
    let mut keys: HashSet<FlowKey> = self.paths.keys().cloned().collect();
    keys.extend(other.paths.keys().cloned());

    for key in keys {
      let left = self.paths.get(&key).copied().unwrap_or(PathState {
        ty: self.unknown,
        assigned: false,
      });
      let right = other.paths.get(&key).copied().unwrap_or(PathState {
        ty: other.unknown,
        assigned: false,
      });
      let merged_ty = store.union(vec![left.ty, right.ty]);
      let merged_assigned = left.assigned && right.assigned;
      match self.paths.get_mut(&key) {
        Some(state) => {
          if state.ty != merged_ty || state.assigned != merged_assigned {
            state.ty = merged_ty;
            state.assigned = merged_assigned;
            changed = true;
          }
        }
        None => {
          self.paths.insert(
            key,
            PathState {
              ty: merged_ty,
              assigned: merged_assigned,
            },
          );
          changed = true;
        }
      }
    }

    changed
  }

  pub fn merge(&mut self, other: &Env, store: &TypeStore) {
    self.merge_from(other, store);
  }
}
