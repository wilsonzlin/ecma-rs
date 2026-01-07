use std::collections::HashMap;
use std::sync::Arc;

use diagnostics::Diagnostic;
use hir_js::DefId;
use salsa::Update;
use types_ts_interned::{IntrinsicKind, TypeId, TypeParamDecl, TypeStore};

/// Declared type information for a single file.
#[derive(Debug, Default, Clone, PartialEq, Eq)]
pub struct DeclTypes {
  /// Declared or annotated types for definitions in the file, keyed by the
  /// canonical [`DefId`].
  pub types: HashMap<DefId, TypeId>,
  /// Explicitly declared type parameters for each definition.
  pub type_params: HashMap<DefId, Vec<TypeParamDecl>>,
  /// Namespace members collected from nested definitions.
  pub namespace_members: HashMap<DefId, Vec<String>>,
  /// Intrinsic marker declarations (type aliases named after `IntrinsicKind`
  /// that lower to `intrinsic`).
  pub intrinsics: HashMap<DefId, IntrinsicKind>,
  /// Diagnostics produced while lowering declarations.
  pub diagnostics: Vec<Diagnostic>,
}

impl DeclTypes {
  pub fn into_shared(self) -> Arc<Self> {
    Arc::new(self)
  }
}

#[derive(Clone)]
pub struct SharedTypeStore(pub Arc<TypeStore>);

impl SharedTypeStore {
  pub fn arc(&self) -> Arc<TypeStore> {
    Arc::clone(&self.0)
  }
}

impl std::fmt::Debug for SharedTypeStore {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_tuple("SharedTypeStore").finish()
  }
}

impl PartialEq for SharedTypeStore {
  fn eq(&self, other: &Self) -> bool {
    Arc::ptr_eq(&self.0, &other.0)
  }
}

impl Eq for SharedTypeStore {}

unsafe impl Update for SharedTypeStore {
  unsafe fn maybe_update(old_pointer: *mut Self, new_value: Self) -> bool {
    let old_value = &mut *old_pointer;
    if Arc::ptr_eq(&old_value.0, &new_value.0) {
      false
    } else {
      *old_value = new_value;
      true
    }
  }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharedDeclTypes(pub Arc<DeclTypes>);

unsafe impl Update for SharedDeclTypes {
  unsafe fn maybe_update(old_pointer: *mut Self, new_value: Self) -> bool {
    let old_value = &mut *old_pointer;
    if *old_value == new_value {
      false
    } else {
      *old_value = new_value;
      true
    }
  }
}
