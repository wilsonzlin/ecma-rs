use super::*;

impl ProgramState {
  pub(in super::super) fn rebuild_interned_named_def_types(&mut self) {
    self.interned_named_def_types.clear();
    let Some(store) = self.interned_store.as_ref() else {
      return;
    };
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
    if self.asts.is_empty() {
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

    let mut ast_entries: Vec<_> = self
      .asts
      .iter()
      .map(|(file, ast)| (*file, Arc::clone(ast)))
      .collect();
    ast_entries.sort_by_key(|(file, _)| file.0);
    let mut sigs_by_name: HashMap<(FileId, String), Vec<(tti::SignatureId, bool)>> = HashMap::new();
    let mut def_type_params: HashMap<DefId, Vec<TypeParamId>> = HashMap::new();
    for (file, ast) in ast_entries.into_iter() {
      let resolver = Arc::new(DeclTypeResolver::new(
        file,
        Arc::clone(&resolver_defs),
        Arc::clone(&self.qualified_def_members),
      ));
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
        let (sig_id, params, diags) = Self::lower_function_signature(
          store,
          file,
          func.stx.as_ref(),
          Some(resolver.clone()),
          self.compiler_options.no_implicit_any,
        );
        if !diags.is_empty() {
          for diag in diags {
            self.push_program_diagnostic(diag);
          }
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
      let mut sig_ids: Vec<_> = sigs.into_iter().map(|(id, _)| id).collect();
      sig_ids.sort();
      sig_ids.dedup();
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
      caches.eval.clone(),
    );
    let mut hooks = relate_hooks();
    hooks.expander = Some(&expander);
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

  fn lower_function_signature(
    store: &Arc<tti::TypeStore>,
    file: FileId,
    func: &FuncDecl,
    resolver: Option<Arc<dyn TypeResolver>>,
    no_implicit_any: bool,
  ) -> (tti::SignatureId, Vec<TypeParamId>, Vec<Diagnostic>) {
    let mut lowerer = match resolver {
      Some(resolver) => TypeLowerer::with_resolver(Arc::clone(store), resolver),
      None => TypeLowerer::new(Arc::clone(store)),
    };
    lowerer.set_file(file);
    let prim = store.primitive_ids();
    let mut type_param_decls = Vec::new();
    if let Some(params) = func.function.stx.type_parameters.as_ref() {
      type_param_decls = lowerer.register_type_params(params);
    }
    let type_param_ids: Vec<_> = type_param_decls.iter().map(|d| d.id).collect();
    let mut params = Vec::new();
    let mut this_param = None;
    let mut diagnostics = Vec::new();
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
      let mut ty = annotation.unwrap_or(prim.unknown);
      if annotation.is_none() && !is_this && no_implicit_any {
        // Match TypeScript's error-recovery semantics: keep checking by treating
        // the missing annotation as `any` while emitting `--noImplicitAny`.
        ty = prim.any;
        let span = loc_to_span(file, param.stx.pattern.stx.pat.loc);
        diagnostics
          .push(codes::IMPLICIT_ANY.error(codes::implicit_any_message(name.as_deref()), span));
      }
      if idx == 0 && matches!(name.as_deref(), Some("this")) {
        this_param = Some(ty);
        continue;
      }
      params.push(tti::Param {
        name: name.as_deref().map(|name| store.intern_name(name)),
        ty,
        optional: param.stx.optional,
        rest: param.stx.rest,
      });
    }
    let ret = func
      .function
      .stx
      .return_type
      .as_ref()
      .map(|r| lowerer.lower_type_expr(r))
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
