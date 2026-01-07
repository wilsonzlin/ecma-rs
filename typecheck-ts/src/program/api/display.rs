use super::*;

impl Program {
  /// Helper to render a type as displayable string.
  pub fn display_type(&self, ty: TypeId) -> TypeDisplay {
    let (store, ty, resolver) = {
      let mut state = self.lock_state();
      state.ensure_analyzed(&self.host, &self.roots);
      if let Err(fatal) = state.ensure_interned_types(&self.host, &self.roots) {
        state.diagnostics.push(fatal_to_diagnostic(fatal));
      }
      let resolver = state
        .def_data
        .iter()
        .map(|(id, data)| (tti::DefId(id.0), data.name.clone()))
        .collect::<HashMap<_, _>>();
      let store = Arc::clone(&state.store);
      let ty = if store.contains_type_id(ty) {
        store.canon(ty)
      } else {
        store.primitive_ids().unknown
      };
      let can_evaluate = true;
      let ty = match store.type_kind(ty) {
        tti::TypeKind::Mapped(mapped) => {
          if !can_evaluate {
            ty
          } else {
            const MAX_DISPLAY_MAPPED_KEYS: usize = 64;
            let should_expand = match store.type_kind(mapped.source) {
              tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
                members.len() <= MAX_DISPLAY_MAPPED_KEYS
              }
              _ => true,
            };
            if !should_expand {
              ty
            } else {
              let caches = state.checker_caches.for_body();
              let expander = ProgramTypeExpander {
                def_types: &state.interned_def_types,
                type_params: &state.interned_type_params,
                intrinsics: &state.interned_intrinsics,
              };
              let queries =
                TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
              let evaluated = queries.evaluate(ty);
              let evaluated = state.prefer_named_class_refs_in_store(&store, evaluated);
              let ok = match store.type_kind(evaluated) {
                tti::TypeKind::Object(obj) => {
                  let shape = store.shape(store.object(obj).shape);
                  shape.properties.len() <= MAX_DISPLAY_MAPPED_KEYS
                }
                _ => false,
              };
              if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
                state.cache_stats.merge(&caches.stats());
              }
              if ok {
                evaluated
              } else {
                ty
              }
            }
          }
        }
        tti::TypeKind::Intrinsic { .. } if can_evaluate => {
          let caches = state.checker_caches.for_body();
          let expander = ProgramTypeExpander {
            def_types: &state.interned_def_types,
            type_params: &state.interned_type_params,
            intrinsics: &state.interned_intrinsics,
          };
          let queries =
            TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
          let evaluated = queries.evaluate(ty);
          let evaluated = state.prefer_named_refs_in_store(&store, evaluated);
          if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
            state.cache_stats.merge(&caches.stats());
          }
          evaluated
        }
        tti::TypeKind::Ref { def, .. }
          if can_evaluate && state.interned_intrinsics.contains_key(&DefId(def.0)) =>
        {
          let caches = state.checker_caches.for_body();
          let expander = ProgramTypeExpander {
            def_types: &state.interned_def_types,
            type_params: &state.interned_type_params,
            intrinsics: &state.interned_intrinsics,
          };
          let queries =
            TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
          let evaluated = queries.evaluate(ty);
          let evaluated = state.prefer_named_refs_in_store(&store, evaluated);
          if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
            state.cache_stats.merge(&caches.stats());
          }
          evaluated
        }
        tti::TypeKind::Ref { def, args }
          if can_evaluate
            && args.is_empty()
            && state
              .def_data
              .get(&DefId(def.0))
              .is_some_and(|data| matches!(data.kind, DefKind::Function(_) | DefKind::Var(_))) =>
        {
          match state.resolve_value_ref_type(ty) {
            Ok(resolved) => resolved,
            Err(fatal) => {
              state.diagnostics.push(fatal_to_diagnostic(fatal));
              ty
            }
          }
        }
        tti::TypeKind::Ref { def, .. } if can_evaluate => {
          let should_expand = state
            .def_data
            .get(&DefId(def.0))
            .is_some_and(|data| matches!(data.kind, DefKind::TypeAlias(_)));
          if !should_expand {
            ty
          } else {
            fn is_simple_display_type(store: &tti::TypeStore, ty: tti::TypeId) -> bool {
              match store.type_kind(ty) {
                tti::TypeKind::Any
                | tti::TypeKind::Unknown
                | tti::TypeKind::Never
                | tti::TypeKind::Void
                | tti::TypeKind::Null
                | tti::TypeKind::Undefined
                | tti::TypeKind::Boolean
                | tti::TypeKind::Number
                | tti::TypeKind::String
                | tti::TypeKind::BigInt
                | tti::TypeKind::Symbol
                | tti::TypeKind::UniqueSymbol
                | tti::TypeKind::BooleanLiteral(_)
                | tti::TypeKind::NumberLiteral(_)
                | tti::TypeKind::StringLiteral(_)
                | tti::TypeKind::BigIntLiteral(_)
                | tti::TypeKind::TemplateLiteral(_) => true,
                tti::TypeKind::Union(members) => {
                  const MAX_SIMPLE_UNION_MEMBERS: usize = 32;
                  members.len() <= MAX_SIMPLE_UNION_MEMBERS
                    && members
                      .iter()
                      .all(|member| is_simple_display_type(store, *member))
                }
                _ => false,
              }
            }

            let caches = state.checker_caches.for_body();
            let expander = ProgramTypeExpander {
              def_types: &state.interned_def_types,
              type_params: &state.interned_type_params,
              intrinsics: &state.interned_intrinsics,
            };
            let queries =
              TypeQueries::with_caches(Arc::clone(&store), &expander, caches.eval.clone());
            let evaluated = queries.evaluate(ty);
            let evaluated = state.prefer_named_refs_in_store(&store, evaluated);
            if matches!(state.compiler_options.cache.mode, CacheMode::PerBody) {
              state.cache_stats.merge(&caches.stats());
            }
            // Preserve user-defined alias names when they only expand to a
            // primitive keyword type. Those names often carry meaning (e.g.
            // they encode intent or come from a `typeof import()` query),
            // whereas printing `number`/`string` would lose that context.
            let expands_to_keyword = matches!(
              store.type_kind(evaluated),
              tti::TypeKind::Any
                | tti::TypeKind::Unknown
                | tti::TypeKind::Never
                | tti::TypeKind::Void
                | tti::TypeKind::Null
                | tti::TypeKind::Undefined
                | tti::TypeKind::Boolean
                | tti::TypeKind::Number
                | tti::TypeKind::String
                | tti::TypeKind::BigInt
                | tti::TypeKind::Symbol
                | tti::TypeKind::UniqueSymbol
            );
            if evaluated != ty && !expands_to_keyword && is_simple_display_type(&store, evaluated) {
              evaluated
            } else {
              ty
            }
          }
        }
        _ => ty,
      };
      let ty = state.prefer_named_class_refs_in_store(&store, ty);
      (store, ty, resolver)
    };
    let resolver = Arc::new(resolver);
    TypeDisplay {
      store,
      ty,
      resolver: Some(Arc::new(move |def| resolver.get(&def).cloned())),
    }
  }
}
