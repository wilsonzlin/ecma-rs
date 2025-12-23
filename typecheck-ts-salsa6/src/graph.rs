use crate::host::FileId;
use std::collections::BTreeMap;
use std::sync::Arc;

/// A resolved edge in the module graph.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleEdge {
  /// The raw module specifier as written in the source.
  pub specifier: Arc<str>,
  /// The resolved target file, if any.
  pub target: Option<FileId>,
}

impl ModuleEdge {
  /// Creates a new edge.
  pub fn new(specifier: Arc<str>, target: Option<FileId>) -> Self {
    Self { specifier, target }
  }
}

/// Deterministic module graph keyed by [`FileId`].
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ModuleGraph {
  /// Sorted adjacency list.
  pub edges: BTreeMap<FileId, Vec<ModuleEdge>>,
}

impl ModuleGraph {
  /// Returns an iterator over all files present in the graph.
  pub fn files(&self) -> impl Iterator<Item = FileId> + '_ {
    self.edges.keys().copied()
  }
}
