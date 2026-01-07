use super::*;

impl ProgramState {
  pub(super) fn canonical_defs(
    &mut self,
  ) -> Result<HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId>, FatalError> {
    self.check_cancelled()?;
    let mut parent_by_def: HashMap<DefId, Option<DefId>> = HashMap::new();
    let mut lowered_entries: Vec<_> = self
      .hir_lowered
      .iter()
      .map(|(file, lowered)| (*file, lowered.clone()))
      .collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);
    for (_file, lowered) in lowered_entries.iter() {
      self.check_cancelled()?;
      for def in lowered.defs.iter() {
        parent_by_def.insert(def.id, def.parent);
      }
    }

    let mut def_entries: Vec<(DefId, DefData)> = Vec::with_capacity(self.def_data.len());
    for (idx, (id, data)) in self.def_data.iter().enumerate() {
      if (idx % 2048) == 0 {
        self.check_cancelled()?;
      }
      def_entries.push((*id, data.clone()));
    }
    self.check_cancelled()?;
    def_entries.sort_by_key(|(id, data)| (data.file.0, data.span.start, id.0));
    let mut def_by_name: HashMap<(FileId, Option<DefId>, String, sem_ts::Namespace), DefId> =
      HashMap::new();
    for (idx, (def_id, data)) in def_entries.into_iter().enumerate() {
      if (idx % 256) == 0 {
        self.check_cancelled()?;
      }
      let namespaces = Self::def_namespaces(&data.kind);
      let parent = parent_by_def.get(&def_id).copied().flatten();
      for ns in [
        sem_ts::Namespace::VALUE,
        sem_ts::Namespace::TYPE,
        sem_ts::Namespace::NAMESPACE,
      ] {
        if !namespaces.contains(ns) {
          continue;
        }
        if (idx % 256) == 0 {
          self.check_cancelled()?;
        }
        let key = (data.file, parent, data.name.clone(), ns);
        let mut mapped_def = def_id;
        if let DefKind::Import(import) = &data.kind {
          self.check_cancelled()?;
          if let Some(target) = self
            .exports_for_import(import)?
            .get(&import.original)
            .and_then(|entry| entry.def)
          {
            mapped_def = target;
          }
        }
        match def_by_name.entry(key) {
          std::collections::hash_map::Entry::Vacant(slot) => {
            slot.insert(mapped_def);
          }
          std::collections::hash_map::Entry::Occupied(mut slot) => {
            let existing = slot.get_mut();
            let current = self.def_priority(*existing, ns);
            let new_pri = self.def_priority(mapped_def, ns);
            if new_pri < current || (new_pri == current && mapped_def < *existing) {
              *existing = mapped_def;
            }
          }
        }
      }
    }

    // TypeScript's global declarations merge across `.d.ts` files. The semantic
    // binder already performs this merge when populating `global_symbols`, but
    // the checker-side canonical map is keyed by `(file, parent, name, ns)`.
    //
    // When we vendor the full upstream `lib.*.d.ts` set, important interfaces
    // like `Promise` and `SymbolConstructor` are declared/augmented across many
    // files. Map every top-level global declaration that participates in a
    // merged global symbol group to a single canonical `DefId` so that
    // `ensure_interned_types` can merge their shapes.
    if let Some(sem) = self.semantics.as_deref() {
      let symbols = sem.symbols();
      for (_global_name, group) in sem.global_symbols().iter() {
        for ns in [
          sem_ts::Namespace::VALUE,
          sem_ts::Namespace::TYPE,
          sem_ts::Namespace::NAMESPACE,
        ] {
          let Some(symbol) = group.symbol_for(ns, symbols) else {
            continue;
          };
          let decls = sem.symbol_decls(symbol, ns);
          if decls.is_empty() {
            continue;
          }

          // Only consider top-level declarations here; nested `declare global`
          // blocks currently use distinct parents and are handled elsewhere.
          let mut best: Option<(u8, DefId)> = None;
          let mut top_level_decls = Vec::new();
          for decl in decls.iter().copied() {
            let decl_data = symbols.decl(decl);
            let def = decl_data.def_id;
            let parent = parent_by_def.get(&def).copied().flatten();
            if parent.is_some() {
              continue;
            }
            top_level_decls.push(decl_data);
            let pri = self.def_priority(def, ns);
            best = best
              .map(|(best_pri, best_id)| {
                if pri < best_pri || (pri == best_pri && def < best_id) {
                  (pri, def)
                } else {
                  (best_pri, best_id)
                }
              })
              .or(Some((pri, def)));
          }

          let Some((_, canonical)) = best else {
            continue;
          };

          for decl_data in top_level_decls {
            let key = (decl_data.file, None, decl_data.name.clone(), ns);
            if let Some(slot) = def_by_name.get_mut(&key) {
              *slot = canonical;
            }
          }
        }
      }
    }
    Ok(def_by_name)
  }

  pub(super) fn rebuild_namespace_member_index(&mut self) -> Result<(), FatalError> {
    let mut index = NamespaceMemberIndex::default();
    let mut lowered_entries: Vec<_> = self.hir_lowered.iter().collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);

    let namespaces_for_hir_kind = |kind: HirDefKind| -> sem_ts::Namespace {
      match kind {
        HirDefKind::Class | HirDefKind::Enum => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Interface | HirDefKind::TypeAlias => sem_ts::Namespace::TYPE,
        HirDefKind::Namespace | HirDefKind::Module => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::NAMESPACE
        }
        HirDefKind::ImportBinding => {
          sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE | sem_ts::Namespace::NAMESPACE
        }
        _ => sem_ts::Namespace::VALUE,
      }
    };

    for (file_idx, (_file, lowered)) in lowered_entries.into_iter().enumerate() {
      if (file_idx % 16) == 0 {
        self.check_cancelled()?;
      }
      for (idx, def) in lowered.defs.iter().enumerate() {
        if (idx % 4096) == 0 {
          self.check_cancelled()?;
        }
        let Some(parent) = def.parent else {
          continue;
        };
        let Some(name) = lowered.names.resolve(def.name) else {
          continue;
        };
        let name = name.to_string();
        let namespaces = namespaces_for_hir_kind(def.path.kind);
        for ns in [
          sem_ts::Namespace::VALUE,
          sem_ts::Namespace::TYPE,
          sem_ts::Namespace::NAMESPACE,
        ] {
          if !namespaces.contains(ns) {
            continue;
          }
          let mut member_def = def.id;
          if ns.contains(sem_ts::Namespace::VALUE)
            && matches!(def.path.kind, HirDefKind::Class | HirDefKind::Enum)
          {
            if let Some(value_def) = self.value_defs.get(&def.id).copied() {
              member_def = value_def;
            }
          }
          index.insert(parent, ns, name.clone(), member_def);
        }
      }
    }

    index.finalize();
    self.namespace_member_index = Some(Arc::new(index));
    Ok(())
  }

  pub(super) fn rebuild_callable_overloads(&mut self) {
    self.callable_overloads.clear();
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      let mut seen_symbols = HashSet::new();
      for def_id in self
        .def_data
        .iter()
        .filter_map(|(def_id, data)| matches!(data.kind, DefKind::Function(_)).then_some(def_id))
      {
        let Some(symbol) =
          semantics.symbol_for_def(sem_ts::DefId(def_id.0), sem_ts::Namespace::VALUE)
        else {
          continue;
        };
        if !seen_symbols.insert(symbol) {
          continue;
        }
        let mut defs = Vec::new();
        let mut seen_defs = HashSet::new();
        for decl_id in semantics.symbol_decls(symbol, sem_ts::Namespace::VALUE) {
          let decl = symbols.decl(*decl_id);
          if !matches!(decl.kind, sem_ts::DeclKind::Function) {
            continue;
          }
          if let Some(mapped) = self.map_decl_to_program_def(decl, sem_ts::Namespace::VALUE) {
            if seen_defs.insert(mapped) {
              defs.push(mapped);
            }
          }
        }
        if !defs.is_empty() {
          for def in defs.iter().copied() {
            if let Some(def_data) = self.def_data.get(&def) {
              self
                .callable_overloads
                .entry((def_data.file, def_data.name.clone()))
                .or_insert_with(|| defs.clone());
            }
          }
        }
      }
    }

    let mut grouped: BTreeMap<(FileId, String), Vec<(DefId, TextRange)>> = BTreeMap::new();
    for (id, data) in self
      .def_data
      .iter()
      .filter(|(_, data)| matches!(data.kind, DefKind::Function(_)))
    {
      grouped
        .entry((data.file, data.name.clone()))
        .or_default()
        .push((*id, data.span));
    }
    for ((file, name), mut defs) in grouped.into_iter() {
      defs.sort_by_key(|(id, span)| (span.start, span.end, id.0));
      let mut ordered: Vec<_> = defs.into_iter().map(|(id, _)| id).collect();
      let key = (file, name.clone());
      if let Some(existing) = self.callable_overloads.get(&key).cloned() {
        ordered.extend(existing);
      }
      ordered.sort_by_key(|id| {
        let span = self
          .def_data
          .get(id)
          .map(|data| data.span)
          .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
        (span.start, span.end, id.0)
      });
      ordered.dedup();
      self.callable_overloads.insert(key, ordered);
    }
  }

  pub(super) fn callable_overload_defs(&mut self, def: DefId) -> Option<Vec<DefId>> {
    let (file, name) = {
      let data = self.def_data.get(&def)?;
      if !matches!(data.kind, DefKind::Function(_)) {
        return None;
      }
      (data.file, data.name.clone())
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let key = (file, name);
    Some(
      self
        .callable_overloads
        .get(&key)
        .cloned()
        .unwrap_or_else(|| vec![def]),
    )
  }

  pub(super) fn merged_overload_callable_type(
    &mut self,
    defs: &[DefId],
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    if defs.is_empty() {
      return None;
    }
    let has_overloads = defs.len() > 1;
    let mut collect = |skip_bodies: bool,
                       state: &mut ProgramState,
                       overloads: &mut Vec<tti::SignatureId>,
                       seen_sigs: &mut HashSet<tti::SignatureId>| {
      for def in defs.iter().copied() {
        if skip_bodies && has_overloads {
          if let Some(def_data) = state.def_data.get(&def) {
            if let DefKind::Function(func) = &def_data.kind {
              if func.body.is_some() && func.return_ann.is_none() {
                continue;
              }
            }
          }
        }
        if !state.interned_def_types.contains_key(&def) {
          let _ = state.type_of_def(def);
        }
        let ty = state.interned_def_types.get(&def).copied().or_else(|| {
          state.def_types.get(&def).copied().map(|store_ty| {
            let mapped = store.canon(convert_type_for_display(store_ty, state, store, cache));
            state.interned_def_types.insert(def, mapped);
            mapped
          })
        });
        let Some(ty) = ty else {
          continue;
        };
        if let tti::TypeKind::Callable { overloads: sigs } = store.type_kind(ty) {
          for sig in sigs.iter().copied() {
            if seen_sigs.insert(sig) {
              overloads.push(sig);
            }
          }
        }
      }
    };
    let mut overloads = Vec::new();
    let mut seen_sigs = HashSet::new();
    collect(true, self, &mut overloads, &mut seen_sigs);
    if overloads.is_empty() && has_overloads {
      collect(false, self, &mut overloads, &mut seen_sigs);
    }
    if overloads.is_empty() {
      return None;
    }
    Some(store.canon(store.intern_type(tti::TypeKind::Callable { overloads })))
  }

  pub(super) fn callable_overload_type_for_def(
    &mut self,
    def: DefId,
    store: &Arc<tti::TypeStore>,
    cache: &mut HashMap<TypeId, tti::TypeId>,
  ) -> Option<tti::TypeId> {
    let defs = self.callable_overload_defs(def)?;
    if defs.len() < 2 {
      return None;
    }
    let merged = self.merged_overload_callable_type(&defs, store, cache)?;
    for member in defs {
      self.interned_def_types.insert(member, merged);
    }
    Some(merged)
  }

  pub(super) fn merge_callable_overload_types(&mut self) {
    let Some(store) = self.interned_store.clone() else {
      return;
    };
    if self.callable_overloads.is_empty() {
      self.rebuild_callable_overloads();
    }
    let mut cache = HashMap::new();
    let mut keys: Vec<_> = self.callable_overloads.keys().cloned().collect();
    keys.sort_by(|a, b| (a.0 .0, &a.1).cmp(&(b.0 .0, &b.1)));
    for key in keys.into_iter() {
      let Some(defs) = self.callable_overloads.get(&key).cloned() else {
        continue;
      };
      if defs.len() < 2 {
        continue;
      }
      if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache) {
        for def in defs.into_iter() {
          self.interned_def_types.insert(def, merged);
        }
      }
    }
  }

  pub(super) fn interned_unknown(&self) -> TypeId {
    self
      .interned_store
      .as_ref()
      .map(|s| s.primitive_ids().unknown)
      .unwrap_or(self.builtin.unknown)
  }

  pub(super) fn find_namespace_def(&self, file: FileId, name: &str) -> Option<DefId> {
    self
      .def_data
      .iter()
      .find_map(|(id, data)| match &data.kind {
        DefKind::Namespace(_) | DefKind::Module(_) if data.file == file && data.name == name => {
          Some(*id)
        }
        _ => None,
      })
  }

  pub(super) fn merge_namespace_value_types(&mut self) -> Result<(), FatalError> {
    let Some(store) = self.interned_store.clone() else {
      return Ok(());
    };
    fn is_ident_char(byte: u8) -> bool {
      byte.is_ascii_alphanumeric() || matches!(byte, b'_' | b'$')
    }

    fn find_name_span(source: &str, name: &str, range: TextRange) -> TextRange {
      let bytes = source.as_bytes();
      let start = (range.start as usize).min(bytes.len());
      let end = (range.end as usize).min(bytes.len());
      let slice = &source[start..end];
      let mut offset = 0usize;
      while offset <= slice.len() {
        let Some(pos) = slice[offset..].find(name) else {
          break;
        };
        let abs_start = start + offset + pos;
        let abs_end = abs_start + name.len();
        if abs_end > bytes.len() {
          break;
        }
        let before_ok = abs_start == 0 || !is_ident_char(bytes[abs_start - 1]);
        let after_ok = abs_end == bytes.len() || !is_ident_char(bytes[abs_end]);
        if before_ok && after_ok {
          return TextRange::new(abs_start as u32, abs_end as u32);
        }
        offset = offset.saturating_add(pos.saturating_add(name.len().max(1)));
      }
      range
    }

    let is_top_level = |state: &ProgramState, file: FileId, def: DefId| -> bool {
      let Some(lowered) = state.hir_lowered.get(&file) else {
        return true;
      };
      let Some(hir_def) = lowered.def(def) else {
        return true;
      };
      let mut parent = hir_def.parent;
      while let Some(parent_id) = parent {
        let Some(parent_def) = lowered.def(parent_id) else {
          return false;
        };
        if matches!(parent_def.path.kind, HirDefKind::VarDeclarator) {
          parent = parent_def.parent;
          continue;
        }
        return false;
      }
      true
    };

    let mut entries: Vec<_> = self
      .namespace_object_types
      .iter()
      .map(|(k, v)| (k.clone(), *v))
      .collect();
    entries.sort_by(|a, b| (a.0 .0, &a.0 .1).cmp(&(b.0 .0, &b.0 .1)));
    for ((file, name), (ns_interned, ns_store)) in entries.into_iter() {
      let ns_def = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          (data.file == file
            && data.name == name
            && matches!(data.kind, DefKind::Namespace(_) | DefKind::Module(_))
            && is_top_level(self, file, *id))
          .then_some(*id)
        })
        .min_by_key(|id| {
          let span = self
            .def_data
            .get(id)
            .map(|d| d.span)
            .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
          (span.start, span.end, id.0)
        });
      let value_def = self
        .def_data
        .iter()
        .filter_map(|(id, data)| {
          (data.file == file
            && data.name == name
            && matches!(
              data.kind,
              DefKind::Function(_) | DefKind::Class(_) | DefKind::Enum(_)
            )
            && is_top_level(self, file, *id))
          .then_some(*id)
        })
        .min_by_key(|id| {
          let span = self
            .def_data
            .get(id)
            .map(|d| d.span)
            .unwrap_or_else(|| TextRange::new(u32::MAX, u32::MAX));
          (span.start, span.end, id.0)
        });

      if let (Some(ns_def), Some(val_def)) = (ns_def, value_def) {
        let Some((ns_span, ns_export)) = self
          .def_data
          .get(&ns_def)
          .map(|data| (data.span, data.export))
        else {
          continue;
        };
        let Some((val_span, val_export)) = self
          .def_data
          .get(&val_def)
          .map(|data| (data.span, data.export))
        else {
          continue;
        };

        let file_text = db::file_text(&self.typecheck_db, file);
        let namespace_name_span = find_name_span(file_text.as_ref(), &name, ns_span);
        let value_name_span = find_name_span(file_text.as_ref(), &name, val_span);

        let mut has_error = false;
        if ns_export != val_export {
          has_error = true;
          self.push_program_diagnostic(codes::MERGED_DECLARATIONS_EXPORT_MISMATCH.error(
            format!(
              "Individual declarations in merged declaration '{name}' must be all exported or all local."
            ),
            Span::new(file, namespace_name_span),
          ));
          self.push_program_diagnostic(codes::MERGED_DECLARATIONS_EXPORT_MISMATCH.error(
            format!(
              "Individual declarations in merged declaration '{name}' must be all exported or all local."
            ),
            Span::new(file, value_name_span),
          ));
        }

        if ns_span.start < val_span.start {
          has_error = true;
          self.push_program_diagnostic(codes::NAMESPACE_BEFORE_MERGE_TARGET.error(
            "A namespace declaration cannot be located prior to a class or function with which it is merged.",
            Span::new(file, namespace_name_span),
          ));
        }

        if has_error {
          continue;
        }

        let mut val_interned = self
          .def_types
          .get(&val_def)
          .copied()
          .and_then(|val_store_ty| {
            let mut cache = HashMap::new();
            Some(store.canon(convert_type_for_display(
              val_store_ty,
              self,
              &store,
              &mut cache,
            )))
          })
          .or_else(|| self.interned_def_types.get(&val_def).copied());
        if val_interned
          .map(|ty| {
            matches!(
              store.type_kind(ty),
              tti::TypeKind::Any | tti::TypeKind::Unknown
            )
          })
          .unwrap_or(false)
        {
          val_interned = self.interned_def_types.get(&val_def).copied();
        }
        if let Some(val_ty_interned) = val_interned {
          let merged = store.intersection(vec![val_ty_interned, ns_interned]);
          self.interned_def_types.insert(ns_def, merged);
          self.interned_def_types.insert(val_def, merged);
        }
        if let Some(val_ty) = self.def_types.get(&val_def).copied() {
          self.def_types.insert(ns_def, ns_store);
          self.def_types.insert(val_def, val_ty);
        }
      }
    }
    Ok(())
  }

  pub(super) fn rebuild_interned_named_def_types(&mut self) {
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

  pub(super) fn collect_function_decl_types(
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

  pub(super) fn check_class_implements(
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

  pub(super) fn merge_namespace_store_types(
    &mut self,
    existing: TypeId,
    incoming: TypeId,
  ) -> TypeId {
    match (
      self.type_store.kind(existing).clone(),
      self.type_store.kind(incoming).clone(),
    ) {
      (TypeKind::Object(mut a), TypeKind::Object(b)) => {
        for (name, prop) in b.props.into_iter() {
          a.props.insert(name, prop);
        }
        if a.string_index.is_none() {
          a.string_index = b.string_index;
        }
        if a.number_index.is_none() {
          a.number_index = b.number_index;
        }
        self.type_store.object(a)
      }
      _ => self
        .type_store
        .union(vec![existing, incoming], &self.builtin),
    }
  }

  pub(super) fn merge_interned_object_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Object(obj_a), tti::TypeKind::Object(obj_b)) => {
        let mut shape = store.shape(store.object(obj_a).shape);
        let other = store.shape(store.object(obj_b).shape);
        let mut merged = Vec::new();
        for prop in shape
          .properties
          .into_iter()
          .chain(other.properties.into_iter())
        {
          if let Some(existing) = merged
            .iter_mut()
            .find(|p: &&mut Property| p.key == prop.key)
          {
            *existing = prop;
          } else {
            merged.push(prop);
          }
        }
        shape.properties = merged;
        shape.call_signatures.extend(other.call_signatures);
        shape
          .construct_signatures
          .extend(other.construct_signatures);
        shape.indexers.extend(other.indexers);
        let shape_id = store.intern_shape(shape);
        let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
        store.intern_type(tti::TypeKind::Object(obj_id))
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  fn merge_callable_with_object(
    store: &Arc<tti::TypeStore>,
    overloads: &[tti::SignatureId],
    object: tti::ObjectId,
    object_ty: tti::TypeId,
  ) -> tti::TypeId {
    let shape = store.shape(store.object(object).shape);
    let mut merged = overloads.to_vec();
    merged.extend(shape.call_signatures.iter().copied());
    let mut seen = HashSet::new();
    merged.retain(|sig| seen.insert(*sig));
    let callable = store.intern_type(tti::TypeKind::Callable { overloads: merged });
    let has_extras = !shape.properties.is_empty()
      || !shape.construct_signatures.is_empty()
      || !shape.indexers.is_empty();
    if has_extras {
      store.intersection(vec![callable, object_ty])
    } else {
      callable
    }
  }

  pub(super) fn merge_interned_decl_types(
    store: &Arc<tti::TypeStore>,
    existing: tti::TypeId,
    incoming: tti::TypeId,
  ) -> tti::TypeId {
    match (store.type_kind(existing), store.type_kind(incoming)) {
      (tti::TypeKind::Callable { overloads: a }, tti::TypeKind::Callable { overloads: b }) => {
        let mut merged = Vec::with_capacity(a.len() + b.len());
        merged.extend(a);
        merged.extend(b.into_iter());
        let mut seen_ids = HashSet::new();
        merged.retain(|sig| seen_ids.insert(*sig));
        let mut unique = Vec::new();
        let mut seen: HashMap<
          (
            Vec<(tti::TypeId, bool, bool)>,
            Vec<tti::TypeParamDecl>,
            Option<tti::TypeId>,
          ),
          (tti::SignatureId, bool, bool),
        > = HashMap::new();
        for id in merged.into_iter() {
          let sig = store.signature(id);
          let key = (
            sig
              .params
              .iter()
              .map(|p| (p.ty, p.optional, p.rest))
              .collect::<Vec<_>>(),
            sig.type_params.clone(),
            sig.this_param,
          );
          let has_names = sig.params.iter().any(|p| p.name.is_some());
          let ret_kind = store.type_kind(sig.ret);
          let ret_unknown = matches!(ret_kind, tti::TypeKind::Unknown | tti::TypeKind::Any);
          if let Some((prev, prev_named, prev_unknown)) = seen.get(&key).copied() {
            let mut replace = false;
            if prev_unknown && !ret_unknown {
              replace = true;
            } else if !prev_named && has_names && prev_unknown == ret_unknown {
              replace = true;
            }
            if replace {
              if let Some(pos) = unique.iter().position(|s| *s == prev) {
                unique[pos] = id;
              }
              seen.insert(key, (id, has_names, ret_unknown));
            }
          } else {
            seen.insert(key.clone(), (id, has_names, ret_unknown));
            unique.push(id);
          }
        }
        store.intern_type(tti::TypeKind::Callable { overloads: unique })
      }
      (tti::TypeKind::Callable { overloads }, tti::TypeKind::Object(obj)) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, incoming)
      }
      (tti::TypeKind::Object(obj), tti::TypeKind::Callable { overloads }) => {
        ProgramState::merge_callable_with_object(store, &overloads, obj, existing)
      }
      (tti::TypeKind::Object(_), tti::TypeKind::Object(_)) => {
        ProgramState::merge_interned_object_types(store, existing, incoming)
      }
      _ => store.intersection(vec![existing, incoming]),
    }
  }

  pub(super) fn merge_interface_symbol_types(&mut self, def: DefId) -> Result<(), FatalError> {
    let Some(store) = self.interned_store.as_ref() else {
      return Ok(());
    };
    let Some(semantics) = self.semantics.as_ref() else {
      return Ok(());
    };
    let Some(symbol) = semantics.symbol_for_def(def, sem_ts::Namespace::TYPE) else {
      return Ok(());
    };

    let symbols = semantics.symbols();
    let mut interface_defs: Vec<DefId> = semantics
      .symbol_decls(symbol, sem_ts::Namespace::TYPE)
      .iter()
      .filter_map(|decl_id| {
        let decl = symbols.decl(*decl_id);
        if !matches!(decl.kind, sem_ts::DeclKind::Interface) {
          return None;
        }
        self.map_decl_to_program_def(decl, sem_ts::Namespace::TYPE)
      })
      .collect();

    if interface_defs.len() <= 1 {
      return Ok(());
    }

    interface_defs.sort_by(|a, b| {
      let key = |def: &DefId| {
        self.def_data.get(def).map(|data| {
          (
            data.file.0,
            data.span.start,
            data.span.end,
            def.0,
            data.name.as_str(),
          )
        })
      };
      key(a).cmp(&key(b)).then_with(|| a.0.cmp(&b.0))
    });
    interface_defs.dedup();
    if interface_defs.len() <= 1 {
      return Ok(());
    }

    let prim = store.primitive_ids();
    let mut convert_cache = HashMap::new();
    let mut merged: Option<tti::TypeId> = None;
    for iface_def in interface_defs.iter().copied() {
      let mut ty = self
        .interned_def_types
        .get(&iface_def)
        .copied()
        .map(|ty| store.canon(ty));

      if matches!(
        ty.map(|ty| store.type_kind(ty)),
        Some(tti::TypeKind::Unknown)
      ) || ty.is_none()
      {
        ty = self
          .def_data
          .get(&iface_def)
          .and_then(|data| match &data.kind {
            DefKind::Interface(interface) => {
              let interned =
                convert_type_for_display(interface.typ, self, store, &mut convert_cache);
              Some(store.canon(interned))
            }
            _ => None,
          });
      }

      let Some(ty) = ty else {
        continue;
      };
      if matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
        continue;
      }
      merged = Some(match merged {
        Some(existing) => ProgramState::merge_interned_decl_types(store, existing, ty),
        None => ty,
      });
    }
    let merged = store.canon(merged.unwrap_or(prim.unknown));

    let imported = self.import_interned_type(merged);
    let legacy = if merged == prim.unknown {
      imported
    } else if imported == self.builtin.unknown {
      merged
    } else {
      imported
    };

    for iface_def in interface_defs {
      self.interned_def_types.insert(iface_def, merged);
      self.def_types.insert(iface_def, legacy);
      if let Some(data) = self.def_data.get_mut(&iface_def) {
        if let DefKind::Interface(existing) = &mut data.kind {
          if imported != self.builtin.unknown {
            existing.typ = imported;
          }
        }
      }
    }

    Ok(())
  }

  pub(super) fn merge_interface_symbol_types_all(&mut self) -> Result<(), FatalError> {
    let mut interface_defs: Vec<DefId> = self
      .def_data
      .iter()
      .filter_map(|(id, data)| matches!(data.kind, DefKind::Interface(_)).then_some(*id))
      .collect();
    interface_defs.sort_by_key(|def| def.0);

    let mut seen_symbols: HashSet<sem_ts::SymbolId> = HashSet::new();
    for def in interface_defs {
      let symbol = self
        .semantics
        .as_ref()
        .and_then(|semantics| semantics.symbol_for_def(def, sem_ts::Namespace::TYPE));
      if let Some(symbol) = symbol {
        if seen_symbols.insert(symbol) {
          self.merge_interface_symbol_types(def)?;
        }
      }
    }
    Ok(())
  }

  pub(super) fn refresh_import_def_types(&mut self) -> Result<(), FatalError> {
    let mut import_defs: Vec<DefId> = self
      .def_data
      .iter()
      .filter_map(|(def, data)| match data.kind {
        DefKind::Import(_) | DefKind::ImportAlias(_) => Some(*def),
        _ => None,
      })
      .collect();
    import_defs.sort_by(|a, b| {
      let key = |def: &DefId| {
        self.def_data.get(def).map(|data| {
          (
            data.file.0,
            data.span.start,
            data.span.end,
            data.name.as_str(),
            def.0,
          )
        })
      };
      key(a).cmp(&key(b)).then_with(|| a.0.cmp(&b.0))
    });
    import_defs.dedup();

    // Import binding definitions cache the resolved export type. Declaration
    // merging (notably interface merging for module augmentations) can update
    // the exported types after these import defs have already been computed.
    // Drop cached import types and recompute so downstream body checking sees
    // the merged surface.
    for def in import_defs.iter().copied() {
      self.def_types.remove(&def);
      self.interned_def_types.remove(&def);
    }
    for def in import_defs.into_iter() {
      self.type_of_def(def)?;
    }
    Ok(())
  }
}
