use ahash::RandomState;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;
use types_ts_interned::{
  DefId, EvaluatorCaches, ExpandedType, RelateTypeExpander, TypeEvaluator, TypeExpander, TypeId,
  TypeKind, TypeParamId, TypeStore,
};

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) struct RefKey {
  pub(crate) def: DefId,
  pub(crate) args: Vec<TypeId>,
}

impl RefKey {
  pub(crate) fn new(def: DefId, args: &[TypeId]) -> Self {
    Self {
      def,
      args: args.to_vec(),
    }
  }
}

pub(crate) fn stable_hash_builder() -> RandomState {
  RandomState::with_seeds(0, 0, 0, 0)
}

#[derive(Debug)]
pub(crate) struct RefRecursionGuard {
  in_progress: Mutex<HashSet<(ThreadId, RefKey), RandomState>>,
}

impl RefRecursionGuard {
  pub(crate) fn new() -> Self {
    Self {
      in_progress: Mutex::new(HashSet::with_hasher(stable_hash_builder())),
    }
  }

  pub(crate) fn begin(&self, key: &RefKey) -> bool {
    let thread_key = (std::thread::current().id(), key.clone());
    self.in_progress.lock().unwrap().insert(thread_key)
  }

  pub(crate) fn end(&self, key: &RefKey) {
    let thread_key = (std::thread::current().id(), key.clone());
    self.in_progress.lock().unwrap().remove(&thread_key);
  }
}

pub(crate) fn instantiate_expanded<E: TypeExpander>(
  store: &Arc<TypeStore>,
  expander: &E,
  caches: &EvaluatorCaches,
  expanded: &ExpandedType,
  args: &[TypeId],
) -> TypeId {
  if expanded.params.is_empty() {
    expanded.ty
  } else {
    let bindings = expanded.params.iter().copied().zip(args.iter().copied());
    let mut evaluator = TypeEvaluator::with_caches(Arc::clone(store), expander, caches.clone());
    evaluator.evaluate_with_bindings(expanded.ty, bindings)
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
  guard: RefRecursionGuard,
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
      guard: RefRecursionGuard::new(),
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

    if let Some(cached) = self.caches.get_ref(def, args) {
      return Some(cached);
    }

    let key = RefKey::new(def, args);
    let expanded = match self.expanded(def) {
      Some(expanded) => expanded,
      None => return None,
    };
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
