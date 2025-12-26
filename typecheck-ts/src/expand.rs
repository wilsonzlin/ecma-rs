use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};

use types_ts_interned::{
  DefId, EvaluatorCaches, ExpandedType, RelateTypeExpander, TypeEvaluator, TypeExpander, TypeId,
  TypeKind, TypeParamId, TypeStore,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct RefKey {
  def: DefId,
  args: Vec<TypeId>,
}

impl RefKey {
  fn new(def: DefId, args: &[TypeId]) -> Self {
    Self {
      def,
      args: args.to_vec(),
    }
  }
}

/// Expands `TypeKind::Ref` nodes by querying the program's type tables. The
/// expander is safe to share across threads and memoizes instantiated results
/// for assignability checks.
pub(crate) struct ProgramTypeExpander<'a> {
  store: Arc<TypeStore>,
  def_types: &'a HashMap<DefId, TypeId>,
  type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
  caches: EvaluatorCaches,
  memoized: Mutex<HashMap<RefKey, TypeId>>,
  in_progress: Mutex<HashSet<RefKey>>,
}

impl<'a> ProgramTypeExpander<'a> {
  pub(crate) fn new(
    store: Arc<TypeStore>,
    def_types: &'a HashMap<DefId, TypeId>,
    type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
    caches: EvaluatorCaches,
  ) -> Self {
    Self {
      store,
      def_types,
      type_params,
      caches,
      memoized: Mutex::new(HashMap::new()),
      in_progress: Mutex::new(HashSet::new()),
    }
  }

  fn expanded(&self, def: DefId) -> Option<ExpandedType> {
    let ty = *self.def_types.get(&def)?;
    let params = self.type_params.get(&def).cloned().unwrap_or_default();
    Some(ExpandedType { params, ty })
  }
}

impl<'a> TypeExpander for ProgramTypeExpander<'a> {
  fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    self.expanded(def)
  }
}

impl<'a> RelateTypeExpander for ProgramTypeExpander<'a> {
  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    debug_assert!(std::ptr::eq(store, self.store.as_ref()));

    let expanded = match self.expanded(def) {
      Some(expanded) => expanded,
      None => return None,
    };

    let key = RefKey::new(def, args);
    if let Some(cached) = self.memoized.lock().unwrap().get(&key).copied() {
      return Some(cached);
    }

    {
      let mut in_progress = self.in_progress.lock().unwrap();
      if !in_progress.insert(key.clone()) {
        return Some(store.intern_type(TypeKind::Ref {
          def,
          args: key.args,
        }));
      }
    }

    let instantiated = if expanded.params.is_empty() {
      expanded.ty
    } else {
      let bindings = expanded.params.iter().copied().zip(args.iter().copied());
      let mut evaluator =
        TypeEvaluator::with_caches(Arc::clone(&self.store), self, self.caches.clone());
      evaluator.evaluate_with_bindings(expanded.ty, bindings)
    };

    self
      .memoized
      .lock()
      .unwrap()
      .insert(key.clone(), instantiated);
    self.in_progress.lock().unwrap().remove(&key);
    Some(instantiated)
  }
}
