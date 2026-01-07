use super::*;

impl Program {
  /// Interned type of a definition, using the `types-ts-interned` store.
  pub fn type_of_def_interned(&self, def: DefId) -> TypeId {
    match self.type_of_def_interned_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        let state = self.lock_state();
        state
          .interned_store
          .as_ref()
          .map(|s| s.primitive_ids().unknown)
          .unwrap_or(TypeId(0))
      }
    }
  }

  /// Interned, *expanded* type of a definition.
  ///
  /// For named type declarations (type aliases, interfaces, classes, enums),
  /// [`Program::type_of_def_interned`] returns a `TypeKind::Ref` pointing at the
  /// definition itself so callers can preserve the name. This helper returns
  /// the stored definition type instead (e.g. the RHS of a type alias).
  pub fn declared_type_of_def_interned(&self, def: DefId) -> TypeId {
    match self.declared_type_of_def_interned_fallible(def) {
      Ok(ty) => ty,
      Err(fatal) => {
        self.record_fatal(fatal);
        let state = self.lock_state();
        state
          .interned_store
          .as_ref()
          .map(|s| s.primitive_ids().unknown)
          .unwrap_or(TypeId(0))
      }
    }
  }

  pub fn declared_type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized")
        .clone();
      let expanded = match state.interned_def_types.get(&def).copied() {
        Some(existing) if !matches!(store.type_kind(existing), tti::TypeKind::Unknown) => existing,
        _ => {
          ProgramState::type_of_def(state, def)?;
          state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or(store.primitive_ids().unknown)
        }
      };
      Ok(expanded)
    })
  }

  pub fn type_of_def_interned_fallible(&self, def: DefId) -> Result<TypeId, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized")
        .clone();
      let expanded = match state.interned_def_types.get(&def).copied() {
        Some(existing) if !matches!(store.type_kind(existing), tti::TypeKind::Unknown) => existing,
        _ => {
          ProgramState::type_of_def(state, def)?;
          state
            .interned_def_types
            .get(&def)
            .copied()
            .unwrap_or(store.primitive_ids().unknown)
        }
      };
      let wants_named_ref = state
        .def_data
        .get(&def)
        .map(|data| {
          matches!(
            data.kind,
            DefKind::Interface(_) | DefKind::TypeAlias(_) | DefKind::Class(_) | DefKind::Enum(_)
          )
        })
        .unwrap_or(false);
      if wants_named_ref {
        let mut args = state
          .interned_type_params
          .get(&def)
          .cloned()
          .unwrap_or_default();
        args.sort_by_key(|param| param.0);
        let args: Vec<_> = args
          .into_iter()
          .map(|param| store.intern_type(tti::TypeKind::TypeParam(param)))
          .collect();
        return Ok(store.canon(store.intern_type(tti::TypeKind::Ref { def, args })));
      }
      Ok(expanded)
    })
  }

  /// Expanded kind summary for an interned type.
  pub fn type_kind(&self, ty: TypeId) -> TypeKindSummary {
    match self.type_kind_fallible(ty) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        TypeKindSummary::Unknown
      }
    }
  }

  pub fn type_kind_fallible(&self, ty: TypeId) -> Result<TypeKindSummary, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let result = queries.type_kind(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(result)
    })
  }

  /// Raw interned type kind without expansion.
  pub fn interned_type_kind(&self, ty: TypeId) -> tti::TypeKind {
    match self.interned_type_kind_fallible(ty) {
      Ok(kind) => kind,
      Err(fatal) => {
        self.record_fatal(fatal);
        tti::TypeKind::Unknown
      }
    }
  }

  pub fn interned_type_kind_fallible(&self, ty: TypeId) -> Result<tti::TypeKind, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      Ok(store.type_kind(ty))
    })
  }

  /// Explain why `src` is not assignable to `dst`.
  ///
  /// Returns `None` if `src` is assignable to `dst`.
  pub fn explain_assignability(&self, src: TypeId, dst: TypeId) -> Option<ExplainTree> {
    match self.explain_assignability_fallible(src, dst) {
      Ok(tree) => tree,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn explain_assignability_fallible(
    &self,
    src: TypeId,
    dst: TypeId,
  ) -> Result<Option<ExplainTree>, FatalError> {
    self.with_interned_state(|state| {
      let src = state.ensure_interned_type(src);
      let dst = state.ensure_interned_type(dst);
      let store = Arc::clone(
        state
          .interned_store
          .as_ref()
          .expect("interned store initialized"),
      );
      let caches = state.checker_caches.for_body();
      let expander = RefExpander::new(
        Arc::clone(&store),
        &state.interned_def_types,
        &state.interned_type_params,
        &state.interned_type_param_decls,
        &state.interned_intrinsics,
        &state.interned_class_instances,
        caches.eval.clone(),
      );
      let hooks = relate_hooks();
      let hooks = tti::RelateHooks {
        expander: Some(&expander),
        is_same_origin_private_member: hooks.is_same_origin_private_member,
      };
      // Use a fresh relation cache so explanation trees contain full structure
      // instead of "cached" sentinel nodes from prior checker passes.
      let relation_cache = tti::RelationCache::new(state.compiler_options.cache.relation_config());
      let options = store.options();
      let ctx = RelateCtx::with_hooks_cache_and_normalizer_caches(
        Arc::clone(&store),
        options,
        hooks,
        relation_cache,
        caches.eval.clone(),
      );

      let result = ctx.explain_assignable(src, dst);
      if result.result {
        return Ok(None);
      }

      Ok(result.reason.or_else(|| {
        Some(tti::ReasonNode {
          src,
          dst,
          relation: tti::RelationKind::Assignable,
          outcome: false,
          note: Some("no explanation available".into()),
          children: Vec::new(),
        })
      }))
    })
  }

  /// Properties visible on a type after expansion.
  pub fn properties_of(&self, ty: TypeId) -> Vec<PropertyInfo> {
    match self.properties_of_fallible(ty) {
      Ok(props) => props,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn properties_of_fallible(&self, ty: TypeId) -> Result<Vec<PropertyInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let mut props = queries.properties_of(ty);
      for prop in props.iter_mut() {
        prop.ty = state.prefer_named_refs(prop.ty);
      }
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(props)
    })
  }

  pub fn property_type(&self, ty: TypeId, key: PropertyKey) -> Option<TypeId> {
    match self.property_type_fallible(ty, key) {
      Ok(res) => res,
      Err(fatal) => {
        self.record_fatal(fatal);
        None
      }
    }
  }

  pub fn property_type_fallible(
    &self,
    ty: TypeId,
    key: PropertyKey,
  ) -> Result<Option<TypeId>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let prop = queries
        .property_type(ty, key)
        .map(|ty| state.prefer_named_refs(ty));
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(prop)
    })
  }

  pub fn call_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    match self.call_signatures_fallible(ty) {
      Ok(sigs) => sigs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn call_signatures_fallible(&self, ty: TypeId) -> Result<Vec<SignatureInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let sigs = queries.call_signatures(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(sigs)
    })
  }

  pub fn construct_signatures(&self, ty: TypeId) -> Vec<SignatureInfo> {
    match self.construct_signatures_fallible(ty) {
      Ok(sigs) => sigs,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn construct_signatures_fallible(
    &self,
    ty: TypeId,
  ) -> Result<Vec<SignatureInfo>, FatalError> {
    self.with_interned_state(|state| {
      let ty = state.ensure_interned_type(ty);
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let sigs = queries.construct_signatures(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(sigs)
    })
  }

  pub fn indexers(&self, ty: TypeId) -> Vec<IndexerInfo> {
    match self.indexers_fallible(ty) {
      Ok(indexers) => indexers,
      Err(fatal) => {
        self.record_fatal(fatal);
        Vec::new()
      }
    }
  }

  pub fn indexers_fallible(&self, ty: TypeId) -> Result<Vec<IndexerInfo>, FatalError> {
    self.with_interned_state(|state| {
      let store = state
        .interned_store
        .as_ref()
        .expect("interned store initialized");
      let expander = ProgramTypeExpander {
        def_types: &state.interned_def_types,
        type_params: &state.interned_type_params,
        intrinsics: &state.interned_intrinsics,
      };
      let caches = state.checker_caches.for_body();
      let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());
      let indexers = queries.indexers(ty);
      if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
        state.cache_stats.merge(&caches.stats());
      }
      Ok(indexers)
    })
  }
}
