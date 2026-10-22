use ahash::RandomState;
use std::collections::{HashMap, HashSet};
use std::sync::{Arc, Mutex};
use std::thread::ThreadId;
use types_ts_interned::{
  DefId, EvaluatorCaches, ExpandedType, IntrinsicKind, RelateTypeExpander, TypeEvaluator,
  TypeExpander, TypeId, TypeKind, TypeParamDecl, TypeParamId, TypeStore,
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

/// tsc: a type reference with fewer arguments than the definition's type
/// parameters is filled with the declared defaults (`Iterator<Foo>` ≡
/// `Iterator<Foo, any, any>`). Without this, partial refs never unify with
/// their fully-applied form and expansion substitutes nothing for the missing
/// parameters (`Generator<Foo, void, unknown>` vs `Iterable<Foo>` failing
/// structurally). Only complete fills normalize; a missing non-defaulted
/// parameter leaves the args as written.
pub(crate) fn fill_default_type_args(
  decls: Option<&[TypeParamDecl]>,
  args: &[TypeId],
) -> Vec<TypeId> {
  let Some(decls) = decls else {
    return args.to_vec();
  };
  if args.len() >= decls.len() {
    return args.to_vec();
  }
  let mut filled: Vec<TypeId> = args.to_vec();
  for decl in decls.iter().skip(args.len()) {
    match decl.default {
      Some(default) => filled.push(default),
      None => return args.to_vec(),
    }
  }
  filled
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
    let id = std::thread::current().id();
    self.in_progress.lock().unwrap().insert((id, key.clone()))
  }

  pub(crate) fn end(&self, key: &RefKey) {
    let id = std::thread::current().id();
    self.in_progress.lock().unwrap().remove(&(id, key.clone()));
  }
}

pub(crate) fn instantiate_expanded<E: TypeExpander>(
  store: &Arc<TypeStore>,
  expander: &E,
  caches: &EvaluatorCaches,
  root_def: DefId,
  expanded: &ExpandedType,
  args: &[TypeId],
) -> TypeId {
  if expanded.params.is_empty() {
    expanded.ty
  } else {
    let bindings = expanded.params.iter().copied().zip(args.iter().copied());

    // Instantiating a referenced definition for assignability checks should
    // avoid expanding recursive self references. The official TypeScript libs
    // define types like `PromiseLike<T>` where members mention
    // `PromiseLike<TResult>`; fully expanding those nested refs while
    // instantiating causes unbounded recursion (args change, so simple
    // cycle-detection by `(def, args)` cannot trigger).
    //
    // We keep expansion of *other* refs (to preserve existing behavior), but
    // intentionally leave refs to the root definition unexpanded so that
    // recursion remains lazy and guarded by the evaluator/relation engines.
    struct SkipSelfExpander<'a, E: TypeExpander> {
      inner: &'a E,
      root_def: DefId,
    }

    impl<'a, E: TypeExpander> TypeExpander for SkipSelfExpander<'a, E> {
      fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType> {
        if def == self.root_def {
          None
        } else {
          self.inner.expand(store, def, args)
        }
      }
    }

    let adapter = SkipSelfExpander {
      inner: expander,
      root_def,
    };
    let mut evaluator = TypeEvaluator::with_caches(Arc::clone(store), &adapter, caches.clone());
    evaluator.evaluate_with_bindings(expanded.ty, bindings)
  }
}

/// Expands `TypeKind::Ref` nodes by querying the program's type tables. The
/// expander is safe to share across threads and memoizes instantiated results
/// for assignability checks.
pub struct ProgramTypeExpander<'a> {
  store: Arc<TypeStore>,
  def_types: &'a HashMap<DefId, TypeId>,
  type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
  type_param_decls: &'a HashMap<DefId, Arc<[TypeParamDecl]>>,
  intrinsics: &'a HashMap<DefId, IntrinsicKind>,
  class_instances: &'a HashMap<DefId, TypeId>,
  enum_defs: &'a HashSet<DefId>,
  caches: EvaluatorCaches,
  guard: RefRecursionGuard,
}

impl<'a> ProgramTypeExpander<'a> {
  pub fn new(
    store: Arc<TypeStore>,
    def_types: &'a HashMap<DefId, TypeId>,
    type_params: &'a HashMap<DefId, Vec<TypeParamId>>,
    type_param_decls: &'a HashMap<DefId, Arc<[TypeParamDecl]>>,
    intrinsics: &'a HashMap<DefId, IntrinsicKind>,
    class_instances: &'a HashMap<DefId, TypeId>,
    enum_defs: &'a HashSet<DefId>,
    caches: EvaluatorCaches,
  ) -> Self {
    Self {
      store,
      def_types,
      type_params,
      type_param_decls,
      intrinsics,
      class_instances,
      enum_defs,
      caches,
      guard: RefRecursionGuard::new(),
    }
  }

  fn expanded(&self, def: DefId) -> Option<ExpandedType> {
    let params = self.type_params.get(&def).cloned().unwrap_or_default();
    if let Some(instance) = self.class_instances.get(&def) {
      return Some(ExpandedType {
        params,
        ty: *instance,
      });
    }
    let ty = *self.def_types.get(&def)?;
    Some(ExpandedType { params, ty })
  }
}

impl<'a> TypeExpander for ProgramTypeExpander<'a> {
  fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType> {
    debug_assert!(std::ptr::eq(store, self.store.as_ref()));

    if let Some(kind) = self.intrinsics.get(&def).copied() {
      let operand = args
        .first()
        .copied()
        .unwrap_or_else(|| store.primitive_ids().unknown);
      let ty = store.intern_type(TypeKind::Intrinsic { kind, ty: operand });
      return Some(ExpandedType {
        params: Vec::new(),
        ty,
      });
    }

    self.expanded(def)
  }
}

impl<'a> RelateTypeExpander for ProgramTypeExpander<'a> {
  fn is_enum_type(&self, def: DefId) -> bool {
    self.enum_defs.contains(&def)
  }

  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    debug_assert!(std::ptr::eq(store, self.store.as_ref()));

    // tsc: a type reference with fewer arguments than the definition's type
    // parameters is filled with the declared defaults (`Iterator<Foo>` ≡
    // `Iterator<Foo, any, any>`). Without this, partial refs never unify with
    // their fully-applied form and expansion substitutes nothing for the
    // missing parameters (`Generator<Foo, void, unknown>` vs `Iterable<Foo>`
    // failing structurally). Only complete fills normalize; a missing
    // non-defaulted parameter leaves the args as written.
    // tsc fills missing type arguments with their declared defaults
    // (`Iterator<Foo>` ≡ `Iterator<Foo, any, any>`) — see
    // `fill_default_type_args`.
    let filled = fill_default_type_args(self.type_param_decls.get(&def).map(|d| d.as_ref()), args);
    let args: &[TypeId] = &filled;

    if let Some(cached) = self.caches.get_ref(def, args) {
      // Deferred/cycle refs (same `def`) must not stick — re-expand once sibling
      // instantiations or definition tables are complete.
      let deferred_same_def = matches!(
        store.type_kind(cached),
        TypeKind::Ref {
          def: cached_def,
          ..
        } if cached_def == def
      );
      if !deferred_same_def {
        return Some(cached);
      }
    }

    if let Some(kind) = self.intrinsics.get(&def).copied() {
      let operand = args
        .first()
        .copied()
        .unwrap_or_else(|| store.primitive_ids().unknown);
      let ty = store.intern_type(TypeKind::Intrinsic { kind, ty: operand });
      self.caches.insert_ref(def, args, ty);
      return Some(ty);
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
    let instantiated =
      instantiate_expanded(&self.store, self, &self.caches, def, &expanded, &key.args);
    self.guard.end(&key);
    let deferred_same_def = matches!(
      store.type_kind(instantiated),
      TypeKind::Ref {
        def: cached_def,
        ..
      } if cached_def == def
    );
    if !deferred_same_def {
      self.caches.insert_ref(def, &key.args, instantiated);
    }
    Some(instantiated)
  }

  fn type_param_decls(&self, def: DefId) -> Option<Arc<[TypeParamDecl]>> {
    self.type_param_decls.get(&def).cloned()
  }
}
