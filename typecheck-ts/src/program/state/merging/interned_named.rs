use super::*;

impl ProgramState {
  pub(in super::super) fn rebuild_interned_named_def_types(&mut self) {
    self.interned_named_def_types.clear();
    let store = self.store.as_ref();
    let def_sort_key =
      |def: DefId, data: &DefData| (data.file.0, data.span.start, data.span.end, def.0);
    let mut entries: Vec<(tti::TypeId, (u32, u32, u32, u64), DefId)> = Vec::new();
    for (def, ty) in self.interned_def_types.iter() {
      let Some(data) = self.def_data.get(def) else {
        continue;
      };
      if !matches!(
        data.kind,
        DefKind::Interface(_) | DefKind::TypeAlias(_) | DefKind::Class(_) | DefKind::Enum(_)
      ) {
        continue;
      }
      let ty = store.canon(*ty);
      if matches!(
        store.type_kind(ty),
        tti::TypeKind::Unknown | tti::TypeKind::Any | tti::TypeKind::Never
      ) {
        continue;
      }
      entries.push((ty, def_sort_key(*def, data), *def));
    }
    entries.sort_by(|a, b| (a.0 .0, a.1).cmp(&(b.0 .0, b.1)));
    for (ty, _key, def) in entries.into_iter() {
      self.interned_named_def_types.entry(ty).or_insert(def);
    }
  }

  pub(in super::super) fn collect_function_decl_types(
    &mut self,
    store: &Arc<tti::TypeStore>,
    def_by_name: &HashMap<(FileId, String), DefId>,
    def_types: &mut HashMap<DefId, tti::TypeId>,
    type_params: &mut HashMap<DefId, Vec<TypeParamId>>,
  ) {
    if self.asts.is_empty() && self.hir_lowered.is_empty() {
      return;
    }
    let resolver_defs = Arc::new(def_by_name.clone());
    let mut def_by_span: HashMap<(FileId, TextRange), DefId> = HashMap::new();
    let mut defs_by_name: HashMap<(FileId, String), Vec<DefId>> = HashMap::new();
    for (def_id, data) in self.def_data.iter() {
      if !matches!(data.kind, DefKind::Function(_)) {
        continue;
      }
      def_by_span.insert((data.file, data.span), *def_id);
      defs_by_name
        .entry((data.file, data.name.clone()))
        .or_default()
        .push(*def_id);
    }

    let mut sigs_by_name: HashMap<(FileId, String), Vec<(tti::SignatureId, bool)>> = HashMap::new();
    let mut def_type_params: HashMap<DefId, Vec<TypeParamId>> = HashMap::new();
    let mut hir_files: HashSet<FileId> = HashSet::new();

    // HIR-only for TS/TSX/DTS: lower top-level function signatures from
    // `hir_js::FunctionData` (no AST `TypeLowerer`). JS/JSX keep the AST path
    // for JSDoc `@param`/`@returns`/`@template`.
    //
    // Only files that have a parsed AST entry are eligible — same set the
    // residual AST walk uses. Running over every `hir_lowered` key would also
    // re-lower lib `.d.ts` bodies here and corrupt early interned callable
    // types used for contextual typing.
    let mut hir_file_list: Vec<FileId> = self
      .asts
      .keys()
      .copied()
      .filter(|file| self.hir_lowered.contains_key(file))
      .collect();
    hir_file_list.sort_by_key(|f| f.0);
    for file in hir_file_list {
      if matches!(
        self.file_kinds.get(&file),
        Some(FileKind::Js | FileKind::Jsx)
      ) {
        continue;
      }
      if self.collect_function_decl_types_from_hir(
        file,
        store,
        &resolver_defs,
        &def_by_span,
        &mut sigs_by_name,
        &mut def_type_params,
      ) {
        hir_files.insert(file);
      }
    }

    // Residual AST path: JS/JSX (JSDoc) and files without HIR.
    let mut ast_entries: Vec<_> = self
      .asts
      .iter()
      .filter(|(file, _)| !hir_files.contains(file))
      .map(|(file, ast)| (*file, Arc::clone(ast)))
      .collect();
    ast_entries.sort_by_key(|(file, _)| file.0);
    for (file, ast) in ast_entries.into_iter() {
      let resolver = Arc::new(DeclTypeResolver::new(
        file,
        Arc::clone(&resolver_defs),
        Arc::clone(&self.qualified_def_members),
      ));
      let jsdoc_source = matches!(
        self.file_kinds.get(&file),
        Some(FileKind::Js | FileKind::Jsx)
      )
      .then(|| db::file_text(&self.typecheck_db, file));
      for stmt in ast.stx.body.iter() {
        let Stmt::FunctionDecl(func) = stmt.stx.as_ref() else {
          continue;
        };
        let span = loc_to_span(file, stmt.loc).range;
        let Some(def_id) = def_by_span.get(&(file, span)).copied() else {
          continue;
        };
        let Some(name) = func.stx.name.as_ref() else {
          continue;
        };
        let has_body = func.stx.function.stx.body.is_some();
        // FuncDecl node loc starts at `function`; inner Func.loc starts at `(`.
        let jsdoc_offset = loc_to_span(file, func.loc).range.start;
        let jsdoc = jsdoc_source
          .as_deref()
          .and_then(|src| crate::jsdoc::leading_jsdoc_tags(src, jsdoc_offset));
        let (sig_id, params, diags) = Self::lower_function_signature(
          store,
          file,
          func.stx.as_ref(),
          Some(resolver.clone()),
          self.compiler_options.no_implicit_any,
          jsdoc_source.as_deref(),
          jsdoc_offset,
        );
        if !diags.is_empty() {
          for diag in diags {
            self.push_program_diagnostic(diag);
          }
        }
        // `@constructor` / `@class`: value type is constructable; instance type
        // is registered as a file typedef alias (see `collect_file_typedefs`).
        if jsdoc.as_ref().is_some_and(|t| t.constructor) {
          let typedefs = jsdoc_source
            .as_deref()
            .map(crate::jsdoc::collect_file_typedefs)
            .unwrap_or_default();
          let env = crate::jsdoc::JsdocLowerEnv::new()
            .with_resolver(Some(resolver.as_ref()))
            .with_typedefs((!typedefs.is_empty()).then_some(&typedefs));
          let instance = crate::jsdoc::lower_jsdoc_type_with(store, &name.stx.name, &env);
          let sig = store.signature(sig_id);
          let constructable = crate::jsdoc::constructable_type(store, sig.params.clone(), instance);
          def_types
            .entry(def_id)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(store, *existing, constructable);
            })
            .or_insert(constructable);
          if !params.is_empty() {
            def_type_params.entry(def_id).or_insert(params);
          }
          continue;
        }
        sigs_by_name
          .entry((file, name.stx.name.clone()))
          .or_default()
          .push((sig_id, has_body));
        if !params.is_empty() {
          def_type_params.entry(def_id).or_insert(params);
        }
      }
    }

    for ((file, name), mut sigs) in sigs_by_name.into_iter() {
      let has_overloads = sigs.len() > 1;
      if has_overloads {
        sigs.retain(|(_, has_body)| !*has_body);
      }
      if sigs.is_empty() {
        continue;
      }
      // Preserve declaration / collection order (HIR sorts by span; AST walks
      // source order). Sorting by SignatureId would make a later, more specific
      // overload win (e.g. `E` before earlier `Object`) and diverge from tsc.
      let mut sig_ids: Vec<_> = sigs.into_iter().map(|(id, _)| id).collect();
      let mut seen = HashSet::new();
      sig_ids.retain(|id| seen.insert(*id));
      let callable = store.intern_type(tti::TypeKind::Callable { overloads: sig_ids });
      if let Some(def_ids) = defs_by_name.get(&(file, name)) {
        let shared_params = def_ids
          .iter()
          .find_map(|id| def_type_params.get(id).cloned());
        for def_id in def_ids {
          def_types
            .entry(*def_id)
            .and_modify(|existing| {
              *existing = ProgramState::merge_interned_decl_types(store, *existing, callable);
            })
            .or_insert(callable);
          if let Some(params) = def_type_params
            .get(def_id)
            .cloned()
            .or_else(|| shared_params.clone())
          {
            type_params.entry(*def_id).or_insert(params);
          }
        }
      }
    }
  }

  /// Lower top-level named function decl signatures from HIR `FunctionData`.
  ///
  /// Mirrors the residual AST walk over `ast.stx.body` `FunctionDecl`s (not
  /// namespace-nested / `declare global` members). Returns `false` when the file
  /// has no usable HIR.
  fn collect_function_decl_types_from_hir(
    &mut self,
    file: FileId,
    store: &Arc<tti::TypeStore>,
    resolver_defs: &Arc<HashMap<(FileId, String), DefId>>,
    def_by_span: &HashMap<(FileId, TextRange), DefId>,
    sigs_by_name: &mut HashMap<(FileId, String), Vec<(tti::SignatureId, bool)>>,
    def_type_params: &mut HashMap<DefId, Vec<TypeParamId>>,
  ) -> bool {
    let Some(lowered) = self.hir_lowered.get(&file).cloned() else {
      return false;
    };
    let resolver = DeclTypeResolver::new(
      file,
      Arc::clone(resolver_defs),
      Arc::clone(&self.qualified_def_members),
    );
    let resolve_name = |path: &[String]| -> Option<DefId> { resolver.resolve_type_name(path) };

    // Match the residual AST walk: only top-level `function` / `declare function`
    // module items. Skip arrow/function *expressions* (HIR may give them
    // `DefKind::Function` with `parent: None`, e.g. name `<arrow>`).
    let item_ids: HashSet<_> = lowered.hir.items.iter().copied().collect();
    let mut hir_funcs: Vec<_> = lowered
      .defs
      .iter()
      .filter(|def| {
        def.path.kind == HirDefKind::Function
          && item_ids.contains(&def.id)
          && def.parent.is_none()
          && !def.in_global
          && def.body.is_some()
      })
      .collect();
    hir_funcs.sort_by_key(|def| (def.span.start, def.span.end, def.id.0));

    let no_implicit_any = self.compiler_options.no_implicit_any;
    for hir_def in hir_funcs {
      let Some(name) = lowered.names.resolve(hir_def.name) else {
        continue;
      };
      if name.is_empty() {
        continue;
      }
      let Some(def_id) = def_by_span.get(&(file, hir_def.span)).copied() else {
        continue;
      };
      let Some(body_id) = hir_def.body else {
        continue;
      };
      let Some(body) = lowered.body(body_id) else {
        continue;
      };
      let Some(func) = body.function.as_ref() else {
        continue;
      };
      if func.is_arrow {
        continue;
      }

      let local_defs = crate::program::check::decls::LocalDefIndex::from_lowered(lowered.as_ref());
      let mut diagnostics = Vec::new();
      let mut lowerer = crate::program::check::decls::HirDeclLowerer::new(
        Arc::clone(store),
        &lowered.types,
        self.semantics.as_deref(),
        HashMap::new(),
        file,
        self.file_key_for_id(file),
        local_defs,
        &mut diagnostics,
        None,
        None,
        None,
        None,
        Some(&self.module_namespace_defs),
        Some(&self.value_defs),
      )
      .with_type_name_resolver(&resolve_name);
      let sig = lowerer.lower_value_function_signature(hir_def.id, func, body, &lowered.names);

      // Match AST `lower_function_signature` `--noImplicitAny` for unannotated
      // params without defaults (HIR missing annotation → `any` already).
      if no_implicit_any {
        let mut binder_idx = 0usize;
        for (idx, hir_param) in func.params.iter().enumerate() {
          let name = body
            .pats
            .get(hir_param.pat.0 as usize)
            .and_then(|pat| match &pat.kind {
              hir_js::PatKind::Ident(name_id) => {
                lowered.names.resolve(*name_id).map(|n| n.to_string())
              }
              _ => None,
            });
          let is_this = idx == 0 && matches!(name.as_deref(), Some("this"));
          if is_this {
            continue;
          }
          let had_annotation = sig
            .param_types_for_binder
            .get(binder_idx)
            .copied()
            .flatten()
            .is_some();
          let has_default = hir_param.default.is_some();
          if !had_annotation && !has_default {
            let span = body
              .pats
              .get(hir_param.pat.0 as usize)
              .map(|p| p.span)
              .unwrap_or(hir_def.span);
            diagnostics.push(codes::IMPLICIT_ANY.error(
              codes::implicit_any_message(name.as_deref()),
              Span::new(file, span),
            ));
          }
          binder_idx += 1;
        }
      }
      for diag in diagnostics {
        self.push_program_diagnostic(diag);
      }

      let type_param_ids: Vec<_> = sig.type_params.iter().map(|d| d.id).collect();
      let signature = tti::Signature {
        params: sig.params,
        ret: sig.return_ann.unwrap_or(store.primitive_ids().unknown),
        type_params: sig.type_params,
        this_param: sig.this_param,
      };
      let sig_id = store.intern_signature(signature);
      sigs_by_name
        .entry((file, name.to_string()))
        .or_default()
        .push((sig_id, func.has_body));
      if !type_param_ids.is_empty() {
        def_type_params.entry(def_id).or_insert(type_param_ids);
      }
    }
    // File has HIR and is TS/TSX/DTS: skip residual AST even when there are no
    // top-level function decls (JSDoc-only AST path is for JS/JSX).
    true
  }

  pub(in super::super) fn check_class_implements(
    &mut self,
    host: &Arc<dyn Host>,
    store: &Arc<tti::TypeStore>,
    def_types: &HashMap<DefId, tti::TypeId>,
    type_params: &HashMap<DefId, Vec<TypeParamId>>,
    type_param_decls: &HashMap<DefId, Arc<[tti::TypeParamDecl]>>,
    lowered_entries: &[(FileId, Arc<LowerResult>)],
    hir_def_maps: &HashMap<FileId, HashMap<HirDefId, DefId>>,
    def_by_name: &HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId>,
  ) -> Result<(), FatalError> {
    if lowered_entries.is_empty() {
      return Ok(());
    }

    let mut ordered_globals: Vec<(String, FileId, DefId)> = def_by_name
      .iter()
      .filter_map(|((file, parent, name, ns), def)| {
        (parent.is_none() && *ns == sem_ts::Namespace::TYPE).then_some((name.clone(), *file, *def))
      })
      .collect();
    ordered_globals.sort_by(|(name_a, file_a, def_a), (name_b, file_b, def_b)| {
      (name_a.as_str(), file_a.0, def_a.0).cmp(&(name_b.as_str(), file_b.0, def_b.0))
    });
    let mut global_types_by_name: HashMap<String, DefId> = HashMap::new();
    for (name, _file, def) in ordered_globals.into_iter() {
      global_types_by_name.entry(name).or_insert(def);
    }

    let caches = self.checker_caches.for_body();
    let expander = RefExpander::new(
      Arc::clone(store),
      def_types,
      type_params,
      type_param_decls,
      &self.interned_intrinsics,
      &self.interned_class_instances,
      &self.interned_enum_defs,
      caches.eval.clone(),
    );
    let mut hooks = relate_hooks();
    hooks.expander = Some(&expander);
    hooks.should_stop = Some(self.cancelled.as_ref());
    let relate = RelateCtx::with_hooks_and_cache(
      Arc::clone(store),
      store.options(),
      hooks,
      caches.relation.clone(),
    );
    let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());

    fn resolve_member_symbol<'a>(
      names: &'a hir_js::NameInterner,
      name: &hir_js::PropertyName,
    ) -> Option<&'a str> {
      match name {
        hir_js::PropertyName::Symbol(id) => names.resolve(*id),
        _ => None,
      }
    }

    fn member_span_for_symbol(
      names: &hir_js::NameInterner,
      members: &[hir_js::ClassMemberSig],
      symbol: &str,
    ) -> Option<TextRange> {
      for member in members {
        if member.static_ {
          continue;
        }
        let name = match &member.kind {
          hir_js::ClassMemberSigKind::Field { name, .. } => name,
          hir_js::ClassMemberSigKind::Method { name, .. } => name,
          hir_js::ClassMemberSigKind::Getter { name, .. } => name,
          hir_js::ClassMemberSigKind::Setter { name, .. } => name,
          _ => continue,
        };
        if resolve_member_symbol(names, name) == Some(symbol) {
          return Some(member.span);
        }
      }
      None
    }

    fn find_symbol_key_range(text: &str, span: TextRange, symbol: &str) -> Option<TextRange> {
      let start = span.start as usize;
      let end = span.end as usize;
      let slice = text.get(start..end)?;
      let direct = format!("[Symbol.{symbol}]");
      if let Some(offset) = slice.find(&direct) {
        let start = span.start.saturating_add(offset as u32);
        let end = start.saturating_add(direct.len() as u32);
        return Some(TextRange::new(start, end));
      }
      let computed = format!("[Symbol[\"{symbol}\"]]");
      if let Some(offset) = slice.find(&computed) {
        let start = span.start.saturating_add(offset as u32);
        let end = start.saturating_add(computed.len() as u32);
        return Some(TextRange::new(start, end));
      }
      None
    }

    for (file_idx, (file, lowered)) in lowered_entries.iter().enumerate() {
      if (file_idx % 16) == 0 {
        self.check_cancelled()?;
      }
      if self.compiler_options.skip_lib_check && self.file_kinds.get(file) == Some(&FileKind::Dts) {
        continue;
      }
      let Ok(text) = self.load_text(*file, host) else {
        continue;
      };
      let def_map = hir_def_maps.get(file);
      for def in lowered.defs.iter() {
        let Some(hir_js::DefTypeInfo::Class {
          implements,
          members,
          ..
        }) = def.type_info.as_ref()
        else {
          continue;
        };
        if implements.is_empty() {
          continue;
        }
        let Some(arenas) = lowered.type_arenas(def.id) else {
          continue;
        };
        let mapped = def_map
          .and_then(|map| map.get(&def.id).copied())
          .unwrap_or(def.id);
        let Some(class_ty) = def_types.get(&mapped).copied() else {
          continue;
        };
        for implemented in implements.iter().copied() {
          let mut expr_id = implemented;
          loop {
            let Some(expr) = arenas.type_exprs.get(expr_id.0 as usize) else {
              break;
            };
            match &expr.kind {
              hir_js::TypeExprKind::Parenthesized(inner) => expr_id = *inner,
              _ => break,
            }
          }
          let Some(expr) = arenas.type_exprs.get(expr_id.0 as usize) else {
            continue;
          };
          let hir_js::TypeExprKind::TypeRef(type_ref) = &expr.kind else {
            continue;
          };
          if !type_ref.type_args.is_empty() {
            continue;
          }
          let hir_js::TypeName::Ident(name_id) = &type_ref.name else {
            continue;
          };
          let Some(name) = lowered.names.resolve(*name_id).map(|s| s.to_string()) else {
            continue;
          };
          let def_id = def_by_name
            .get(&(*file, None, name.clone(), sem_ts::Namespace::TYPE))
            .copied()
            .or_else(|| global_types_by_name.get(&name).copied());
          let Some(def_id) = def_id else {
            continue;
          };
          let iface_ty = store.intern_type(tti::TypeKind::Ref {
            def: def_id,
            args: Vec::new(),
          });
          if relate.is_assignable(class_ty, iface_ty) {
            continue;
          }

          let mut mismatched: Option<PropertyKey> = None;
          for prop in queries.properties_of(iface_ty) {
            let Some(actual) = queries.property_type(class_ty, prop.key.clone()) else {
              continue;
            };
            if !relate.is_assignable(actual, prop.ty) {
              mismatched = Some(prop.key);
              break;
            }
          }
          let Some(PropertyKey::Symbol(symbol)) = mismatched else {
            continue;
          };
          let Some(member_span) = member_span_for_symbol(&lowered.names, members, &symbol) else {
            continue;
          };
          let key_span =
            find_symbol_key_range(text.as_ref(), member_span, &symbol).unwrap_or(member_span);
          self
            .diagnostics
            .push(codes::PROPERTY_IN_TYPE_NOT_ASSIGNABLE_TO_BASE.error(
              "property not assignable to base type",
              Span::new(*file, key_span),
            ));
        }
      }
    }

    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      self.cache_stats.merge(&caches.stats());
    }

    Ok(())
  }

  /// Emit TS2430 when an interface's own members are not assignable to the
  /// corresponding members of each `extends` base.
  ///
  /// Interface types are interned as `Own & Base…`, which is always a subtype of
  /// each base; incompatible property overrides must be checked against the
  /// own-only object constituent of that intersection (same lowering as
  /// `def_types`, so lib generics like `Array<T>` keep their variance).
  pub(in super::super) fn check_interface_extends(
    &mut self,
    host: &Arc<dyn Host>,
    store: &Arc<tti::TypeStore>,
    def_types: &HashMap<DefId, tti::TypeId>,
    type_params: &HashMap<DefId, Vec<TypeParamId>>,
    type_param_decls: &HashMap<DefId, Arc<[tti::TypeParamDecl]>>,
    lowered_entries: &[(FileId, Arc<LowerResult>)],
    hir_def_maps: &HashMap<FileId, HashMap<HirDefId, DefId>>,
    def_by_name: &HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId>,
  ) -> Result<(), FatalError> {
    if lowered_entries.is_empty() {
      return Ok(());
    }

    let mut ordered_globals: Vec<(String, FileId, DefId)> = def_by_name
      .iter()
      .filter_map(|((file, parent, name, ns), def)| {
        (parent.is_none() && *ns == sem_ts::Namespace::TYPE).then_some((name.clone(), *file, *def))
      })
      .collect();
    ordered_globals.sort_by(|(name_a, file_a, def_a), (name_b, file_b, def_b)| {
      (name_a.as_str(), file_a.0, def_a.0).cmp(&(name_b.as_str(), file_b.0, def_b.0))
    });
    let mut global_types_by_name: HashMap<String, DefId> = HashMap::new();
    for (name, _file, def) in ordered_globals.into_iter() {
      global_types_by_name.entry(name).or_insert(def);
    }

    let caches = self.checker_caches.for_body();
    let expander = RefExpander::new(
      Arc::clone(store),
      def_types,
      type_params,
      type_param_decls,
      &self.interned_intrinsics,
      &self.interned_class_instances,
      &self.interned_enum_defs,
      caches.eval.clone(),
    );
    let mut hooks = relate_hooks();
    hooks.expander = Some(&expander);
    hooks.should_stop = Some(self.cancelled.as_ref());
    let relate = RelateCtx::with_hooks_and_cache(
      Arc::clone(store),
      store.options(),
      hooks,
      caches.relation.clone(),
    );
    let queries = TypeQueries::with_caches(Arc::clone(store), &expander, caches.eval.clone());

    fn interface_name_span(text: &str, def_span: TextRange, name: &str) -> TextRange {
      let start = def_span.start as usize;
      let end = (def_span.end as usize).min(text.len());
      let Some(slice) = text.get(start..end) else {
        return def_span;
      };
      let needle = format!("interface {name}");
      if let Some(pos) = slice.find(&needle) {
        let name_start = start + pos + "interface ".len();
        let name_end = name_start + name.len();
        if name_end <= text.len() {
          return TextRange::new(name_start as u32, name_end as u32);
        }
      }
      if let Some(pos) = slice.find(name) {
        let name_start = start + pos;
        let name_end = name_start + name.len();
        if name_end <= text.len() {
          return TextRange::new(name_start as u32, name_end as u32);
        }
      }
      def_span
    }

    /// Own object constituent of an interface type `Own & Base…`.
    fn own_object_constituent(store: &tti::TypeStore, ty: tti::TypeId) -> Option<tti::TypeId> {
      match store.type_kind(ty) {
        tti::TypeKind::Object(_) => Some(ty),
        tti::TypeKind::Intersection(members) => members
          .into_iter()
          .find(|&member| matches!(store.type_kind(member), tti::TypeKind::Object(_))),
        _ => None,
      }
    }

    for (file_idx, (file, lowered)) in lowered_entries.iter().enumerate() {
      if (file_idx % 16) == 0 {
        self.check_cancelled()?;
      }
      if self.compiler_options.skip_lib_check && self.file_kinds.get(file) == Some(&FileKind::Dts) {
        continue;
      }
      let Ok(text) = self.load_text(*file, host) else {
        continue;
      };
      let def_map = hir_def_maps.get(file);

      for def in lowered.defs.iter() {
        let Some(hir_js::DefTypeInfo::Interface { extends, .. }) = def.type_info.as_ref() else {
          continue;
        };
        if extends.is_empty() {
          continue;
        }
        let Some(iface_name) = lowered.names.resolve(def.name) else {
          continue;
        };
        let Some(arenas) = lowered.type_arenas(def.id) else {
          continue;
        };
        let mapped = def_map
          .and_then(|map| map.get(&def.id).copied())
          .unwrap_or(def.id);
        let Some(iface_ty) = def_types.get(&mapped).copied() else {
          continue;
        };
        let Some(own_ty) = own_object_constituent(store, iface_ty) else {
          continue;
        };
        let own_props = queries.properties_of(own_ty);
        if own_props.is_empty() {
          continue;
        }

        let parent_key: Option<DefId> = def.parent.and_then(|hir_parent| {
          def_map
            .and_then(|map| map.get(&hir_parent).copied())
            .or(Some(hir_parent))
        });

        let name_span = interface_name_span(text.as_ref(), def.span, iface_name);
        for &base_expr in extends.iter() {
          let mut expr_id = base_expr;
          loop {
            let Some(expr) = arenas.type_exprs.get(expr_id.0 as usize) else {
              break;
            };
            match &expr.kind {
              hir_js::TypeExprKind::Parenthesized(inner) => expr_id = *inner,
              _ => break,
            }
          }
          let Some(expr) = arenas.type_exprs.get(expr_id.0 as usize) else {
            continue;
          };
          let hir_js::TypeExprKind::TypeRef(type_ref) = &expr.kind else {
            continue;
          };
          if !type_ref.type_args.is_empty() {
            // Generic base instantiations are a follow-on; property checks still
            // cover the common non-generic `extends A` fixtures.
            continue;
          }
          let hir_js::TypeName::Ident(name_id) = &type_ref.name else {
            continue;
          };
          let Some(base_name) = lowered.names.resolve(*name_id).map(|s| s.to_string()) else {
            continue;
          };
          let base_def = def_by_name
            .get(&(
              *file,
              parent_key,
              base_name.clone(),
              sem_ts::Namespace::TYPE,
            ))
            .copied()
            .or_else(|| {
              def_by_name
                .get(&(*file, None, base_name.clone(), sem_ts::Namespace::TYPE))
                .copied()
            })
            .or_else(|| global_types_by_name.get(&base_name).copied());
          let Some(base_def) = base_def else {
            continue;
          };
          let base_ty = def_types.get(&base_def).copied().unwrap_or_else(|| {
            store.intern_type(tti::TypeKind::Ref {
              def: base_def,
              args: Vec::new(),
            })
          });

          let mut incompatible = false;
          for prop in own_props.iter() {
            let Some(base_prop_ty) = queries.property_type(base_ty, prop.key.clone()) else {
              continue;
            };
            // tsc: an interface type parameter is nominal to its container and
            // never unifies with a *method's* type parameter — a concrete
            // member mentioning the interface's `T` cannot satisfy a generic
            // base signature (`interface I<T> extends A { a: (x: T) => T[] }`
            // is TS2430, "two different types with this name exist"). Compare
            // nominally in that case; generic own members still unify.
            let ok = if !type_has_generic_signature(store.as_ref(), prop.ty)
              && type_has_generic_signature(store.as_ref(), base_prop_ty)
              && type_mentions_type_param(store.as_ref(), prop.ty)
            {
              false
            } else {
              relate.is_assignable(prop.ty, base_prop_ty)
            };
            if !ok {
              incompatible = true;
              break;
            }
          }
          if incompatible {
            self
              .diagnostics
              .push(codes::INTERFACE_INCORRECTLY_EXTENDS.error(
                format!("Interface '{iface_name}' incorrectly extends interface '{base_name}'."),
                Span::new(*file, name_span),
              ));
            break;
          }
        }
      }
    }

    if matches!(self.compiler_options.cache.mode, CacheMode::PerBody) {
      self.cache_stats.merge(&caches.stats());
    }

    Ok(())
  }

  fn lower_function_signature(
    store: &Arc<tti::TypeStore>,
    file: FileId,
    func: &FuncDecl,
    resolver: Option<Arc<dyn TypeResolver>>,
    no_implicit_any: bool,
    jsdoc_source: Option<&str>,
    jsdoc_offset: u32,
  ) -> (tti::SignatureId, Vec<TypeParamId>, Vec<Diagnostic>) {
    let mut lowerer = match resolver.clone() {
      Some(resolver) => TypeLowerer::with_resolver(Arc::clone(store), resolver),
      None => TypeLowerer::new(Arc::clone(store)),
    };
    lowerer.set_file(file);
    let prim = store.primitive_ids();
    let mut type_param_decls = Vec::new();
    if let Some(params) = func.function.stx.type_parameters.as_ref() {
      type_param_decls = lowerer.register_type_params(params);
    }
    let jsdoc = jsdoc_source.and_then(|src| crate::jsdoc::leading_jsdoc_tags(src, jsdoc_offset));
    let typedefs = jsdoc_source
      .map(crate::jsdoc::collect_file_typedefs)
      .unwrap_or_default();
    if type_param_decls.is_empty() {
      if let Some(tags) = jsdoc.as_ref() {
        if !tags.templates.is_empty() {
          lowerer.push_type_param_scope();
          for t in tags.templates.iter() {
            type_param_decls.push(lowerer.register_jsdoc_type_param(t.name.to_owned(), None));
          }
          let tp_map = lowerer.type_param_map();
          let env = crate::jsdoc::JsdocLowerEnv::new()
            .with_resolver(resolver.as_deref())
            .with_typedefs((!typedefs.is_empty()).then_some(&typedefs))
            .with_type_params((!tp_map.is_empty()).then_some(&tp_map));
          for (decl, t) in type_param_decls.iter_mut().zip(tags.templates.iter()) {
            if let Some(raw) = t.constraint {
              decl.constraint = Some(crate::jsdoc::lower_jsdoc_type_with(store, raw, &env));
            }
          }
        }
      }
    }
    let type_param_ids: Vec<_> = type_param_decls.iter().map(|d| d.id).collect();
    let tp_map = lowerer.type_param_map();
    let jsdoc_env = crate::jsdoc::JsdocLowerEnv::new()
      .with_resolver(resolver.as_deref())
      .with_typedefs((!typedefs.is_empty()).then_some(&typedefs))
      .with_type_params((!tp_map.is_empty()).then_some(&tp_map));
    // Whole-signature `@type {function…}` / `(…) => T` when there are no
    // per-param `@param` / `@returns` tags (mirrors body `function_type`).
    let jsdoc_type_sig = jsdoc.as_ref().and_then(|tags| {
      if !tags.params.is_empty() || tags.returns.is_some() {
        return None;
      }
      let raw = tags.type_tag?;
      let ty = crate::jsdoc::lower_jsdoc_type_with(store, raw, &jsdoc_env);
      match store.type_kind(ty) {
        tti::TypeKind::Callable { overloads } => overloads.first().map(|id| store.signature(*id)),
        _ => None,
      }
    });
    let mut params = Vec::new();
    let mut this_param = None;
    let mut diagnostics = Vec::new();
    // Fold nested `@param opts.x` into root object types. TS8032 is reported
    // from body `bind_params` to avoid duplicate diagnostics on decls.
    let jsdoc_resolved = jsdoc.as_ref().map(|tags| {
      let owned: Vec<crate::jsdoc::OwnedJsdocParam> = tags
        .params
        .iter()
        .map(|p| crate::jsdoc::OwnedJsdocParam {
          ty: p.ty.to_owned(),
          name: p.name.map(str::to_owned),
          optional: p.optional,
        })
        .collect();
      crate::jsdoc::resolve_jsdoc_params(store, &owned, &jsdoc_env).0
    });
    for (idx, param) in func.function.stx.parameters.iter().enumerate() {
      let name = match &*param.stx.pattern.stx.pat.stx {
        Pat::Id(id) => Some(id.stx.name.clone()),
        _ => None,
      };
      let is_this = idx == 0 && matches!(name.as_deref(), Some("this"));
      let annotation = param
        .stx
        .type_annotation
        .as_ref()
        .map(|ann| lowerer.lower_type_expr(ann));
      let jsdoc_resolved_param = name
        .as_deref()
        .and_then(|n| jsdoc_resolved.as_ref().and_then(|m| m.get(n)));
      let jsdoc_ty = if annotation.is_none() {
        jsdoc_resolved_param.map(|p| p.ty)
      } else {
        None
      };
      let jsdoc_type_param_ty = if annotation.is_none() && jsdoc_ty.is_none() {
        jsdoc_type_sig
          .as_ref()
          .and_then(|sig| sig.params.get(idx))
          .map(|p| p.ty)
      } else {
        None
      };
      let had_annotation = annotation.is_some();
      let had_jsdoc_param = jsdoc_ty.is_some() || jsdoc_type_param_ty.is_some();
      let mut ty = annotation
        .or(jsdoc_ty)
        .or(jsdoc_type_param_ty)
        .unwrap_or(prim.unknown);
      // A parameter initializer lets TypeScript infer the parameter's type from
      // the initializer, so an unannotated parameter with a default value is not
      // treated as implicitly `any` and does not trigger `--noImplicitAny`.
      let has_default = param.stx.default_value.is_some();
      if !had_annotation && !had_jsdoc_param && !is_this && no_implicit_any {
        // Match TypeScript's error-recovery semantics: keep checking by treating
        // the missing annotation as `any` while emitting `--noImplicitAny` (only
        // when there is no initializer to infer the type from).
        ty = prim.any;
        if !has_default {
          let span = loc_to_span(file, param.stx.pattern.stx.pat.loc);
          diagnostics
            .push(codes::IMPLICIT_ANY.error(codes::implicit_any_message(name.as_deref()), span));
        }
      }
      if idx == 0 && matches!(name.as_deref(), Some("this")) {
        this_param = Some(ty);
        continue;
      }
      let mut optional = param.stx.optional;
      if let Some(p) = jsdoc_resolved_param {
        optional = optional || p.optional;
      }
      if let Some(sig) = jsdoc_type_sig.as_ref() {
        if let Some(p) = sig.params.get(idx) {
          optional = optional || p.optional;
        }
      }
      params.push(tti::Param {
        name: name.as_deref().map(|name| store.intern_name(name)),
        ty,
        optional,
        rest: param.stx.rest,
      });
    }
    let annotated_ret = func
      .function
      .stx
      .return_type
      .as_ref()
      .map(|r| lowerer.lower_type_expr(r));
    let jsdoc_ret = if annotated_ret.is_none() {
      jsdoc
        .as_ref()
        .and_then(|tags| tags.returns)
        .map(|raw| crate::jsdoc::lower_jsdoc_type_with(store, raw, &jsdoc_env))
    } else {
      None
    };
    let jsdoc_type_ret = if annotated_ret.is_none() && jsdoc_ret.is_none() {
      jsdoc_type_sig.as_ref().map(|sig| sig.ret)
    } else {
      None
    };
    let ret = annotated_ret
      .or(jsdoc_ret)
      .or(jsdoc_type_ret)
      .unwrap_or(prim.unknown);
    let sig = tti::Signature {
      params,
      ret,
      type_params: type_param_decls,
      this_param,
    };
    let sig_id = store.intern_signature(sig);
    diagnostics.extend(lowerer.take_diagnostics());
    (sig_id, type_param_ids, diagnostics)
  }
}

/// Whether `ty` exposes any signature with its own type parameters (a generic
/// method/function type), for the nominal interface-extends comparison.
fn type_has_generic_signature(store: &tti::TypeStore, ty: tti::TypeId) -> bool {
  let generic = |sig_id: &tti::SignatureId| !store.signature(*sig_id).type_params.is_empty();
  match store.type_kind(ty) {
    tti::TypeKind::Callable { overloads } => overloads.iter().any(generic),
    tti::TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      shape.call_signatures.iter().any(generic) || shape.construct_signatures.iter().any(generic)
    }
    _ => false,
  }
}

/// Whether `ty` mentions any type parameter (a concrete member type that
/// references a generic parameter, e.g. the interface's own `T`). Shallow
/// recursive walk, depth-capped.
fn type_mentions_type_param(store: &tti::TypeStore, ty: tti::TypeId) -> bool {
  fn go(store: &tti::TypeStore, ty: tti::TypeId, depth: usize) -> bool {
    if depth > 16 {
      return false;
    }
    match store.type_kind(ty) {
      tti::TypeKind::TypeParam(_) => true,
      tti::TypeKind::Array { ty, .. } => go(store, ty, depth + 1),
      tti::TypeKind::Tuple(elems) => elems.iter().any(|e| go(store, e.ty, depth + 1)),
      tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
        members.iter().any(|m| go(store, *m, depth + 1))
      }
      tti::TypeKind::Callable { overloads } => overloads.iter().any(|sig_id| {
        let sig = store.signature(*sig_id);
        sig.params.iter().any(|p| go(store, p.ty, depth + 1))
          || go(store, sig.ret, depth + 1)
          || sig
            .this_param
            .is_some_and(|this| go(store, this, depth + 1))
      }),
      tti::TypeKind::Object(obj) => {
        let shape = store.shape(store.object(obj).shape);
        shape
          .properties
          .iter()
          .any(|p| go(store, p.data.ty, depth + 1))
          || shape
            .indexers
            .iter()
            .any(|idx| go(store, idx.key_type, depth + 1) || go(store, idx.value_type, depth + 1))
          || shape
            .call_signatures
            .iter()
            .chain(shape.construct_signatures.iter())
            .any(|sig_id| {
              let sig = store.signature(*sig_id);
              sig.params.iter().any(|p| go(store, p.ty, depth + 1)) || go(store, sig.ret, depth + 1)
            })
      }
      tti::TypeKind::Ref { args, .. } => args.iter().any(|a| go(store, *a, depth + 1)),
      _ => false,
    }
  }
  go(store, ty, 0)
}
