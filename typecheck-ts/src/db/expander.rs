use std::sync::Arc;

use types_ts_interned::{
  DefId, EvaluatorCaches, ExpandedType, IntrinsicKind, RelateTypeExpander, TypeExpander, TypeId,
  TypeKind, TypeParamId, TypeStore,
};

use crate::expand::{instantiate_expanded, RefKey, RefRecursionGuard};

/// Database handle required by [`DbTypeExpander`]. Implementors are expected to
/// surface queries for retrieving a shared [`TypeStore`], declared types for
/// definitions, and any type parameters that should be substituted when
/// instantiating references.
pub trait TypeExpanderDb: Send + Sync {
  /// Shared type store backing all interned types for this revision.
  fn type_store(&self) -> Arc<TypeStore>;

  /// Declared type of a definition prior to instantiation.
  fn decl_type(&self, def: DefId) -> Option<TypeId>;

  /// Type parameters declared on the definition, if any.
  fn type_params(&self, def: DefId) -> Arc<[TypeParamId]> {
    let _: DefId = def;
    Arc::from([])
  }

  /// Fully inferred type of the definition, if available.
  fn type_of_def(&self, _def: DefId) -> Option<TypeId> {
    None
  }

  /// Intrinsic kind for a definition, if it represents a lib `intrinsic` alias.
  fn intrinsic_kind(&self, _def: DefId) -> Option<IntrinsicKind> {
    None
  }

  /// Combined expansion helper that defaults to declared type information.
  fn ref_expansion(&self, def: DefId) -> Option<ExpandedType> {
    let ty = self.type_of_def(def).or_else(|| self.decl_type(def))?;
    Some(ExpandedType {
      params: self.type_params(def).as_ref().to_vec(),
      ty,
    })
  }
}

/// Expander that sources definition information from a database instead of
/// borrowed program tables, making it suitable for use inside salsa queries or
/// other parallel evaluation contexts.
pub struct DbTypeExpander<'db> {
  db: &'db dyn TypeExpanderDb,
  store: Arc<TypeStore>,
  caches: EvaluatorCaches,
  guard: RefRecursionGuard,
}

impl<'db> DbTypeExpander<'db> {
  pub fn new(db: &'db dyn TypeExpanderDb, caches: EvaluatorCaches) -> Self {
    let store = db.type_store();
    Self {
      db,
      store,
      caches,
      guard: RefRecursionGuard::new(),
    }
  }

  fn expanded(&self, def: DefId) -> Option<ExpandedType> {
    let expanded = self.db.ref_expansion(def);
    if expanded.is_none() && std::env::var("DEBUG_EXPAND").is_ok() {
      eprintln!("DEBUG_EXPAND missing ref expansion for def {:?}", def);
    }
    expanded
  }
}

impl<'db> TypeExpander for DbTypeExpander<'db> {
  fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType> {
    debug_assert!(std::ptr::eq(store, self.store.as_ref()));

    if let Some(kind) = self.db.intrinsic_kind(def) {
      let operand = args.first().copied().unwrap_or_else(|| store.primitive_ids().unknown);
      let ty = store.intern_type(TypeKind::Intrinsic { kind, ty: operand });
      return Some(ExpandedType {
        params: Vec::new(),
        ty,
      });
    }

    self.expanded(def)
  }
}

impl<'db> RelateTypeExpander for DbTypeExpander<'db> {
  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    debug_assert!(std::ptr::eq(store, self.store.as_ref()));
    if let Some(cached) = self.caches.get_ref(def, args) {
      return Some(cached);
    }

    if let Some(kind) = self.db.intrinsic_kind(def) {
      let operand = args.first().copied().unwrap_or_else(|| store.primitive_ids().unknown);
      let ty = store.intern_type(TypeKind::Intrinsic { kind, ty: operand });
      self.caches.insert_ref(def, args, ty);
      return Some(ty);
    }
    let expanded = match self.expanded(def) {
      Some(expanded) => expanded,
      None => return None,
    };

    let key = RefKey::new(def, args);
    if !self.guard.begin(&key) {
      return Some(store.intern_type(TypeKind::Ref {
        def,
        args: key.args,
      }));
    }
    let instantiated = instantiate_expanded(&self.store, self, &self.caches, &expanded, &key.args);
    self.guard.end(&key);
    self.caches.insert_ref(def, &key.args, instantiated);
    Some(instantiated)
  }
}
