use super::*;

mod module_namespace;
mod namespaces;

impl ProgramState {
  pub(in super::super) fn ensure_interned_types(
    &mut self,
    host: &Arc<dyn Host>,
    roots: &[FileKey],
  ) -> Result<(), FatalError> {
    self.ensure_analyzed_result(host, roots)?;
    self.check_cancelled()?;
    let store = self.interned_store.clone().unwrap_or_else(|| {
      let store = tti::TypeStore::with_options((&self.compiler_options).into());
      self.interned_store = Some(Arc::clone(&store));
      self
        .typecheck_db
        .set_type_store(crate::db::types::SharedTypeStore(Arc::clone(&store)));
      store
    });
    self
      .typecheck_db
      .set_type_store(crate::db::types::SharedTypeStore(Arc::clone(&store)));
    let fingerprint = db::decl_types_fingerprint(&self.typecheck_db);
    if self.decl_types_fingerprint == Some(fingerprint) {
      return Ok(());
    }
    self.module_namespace_types.clear();
    self.module_namespace_in_progress.clear();
    // The interned type tables are rebuilt as a batch; invalidate any shared
    // caches that may have memoized partial ref expansions against the old
    // tables.
    self.checker_caches.invalidate_shared();
    self.interned_def_types.clear();
    self.interned_named_def_types.clear();
    self.interned_type_params.clear();
    self.interned_type_param_decls.clear();
    self.interned_intrinsics.clear();
    self.namespace_object_types.clear();
    self.check_cancelled()?;
    let mut def_types = HashMap::new();
    let mut type_params = HashMap::new();
    let mut type_param_decls = HashMap::new();
    let mut decl_files: Vec<_> = db::all_files(&self.typecheck_db).iter().copied().collect();
    decl_files.sort_by_key(|file| file.0);
    for (idx, file) in decl_files.iter().enumerate() {
      if (idx % 16) == 0 {
        self.check_cancelled()?;
      }
      let decls = db::decl_types(&self.typecheck_db, *file);
      for (def, ty) in decls.types.iter() {
        def_types
          .entry(*def)
          .and_modify(|existing| {
            *existing = ProgramState::merge_interned_decl_types(&store, *existing, *ty);
          })
          .or_insert(*ty);
      }
      for (def, params) in decls.type_params.iter() {
        if params.is_empty() {
          continue;
        }
        type_params.insert(*def, params.iter().map(|param| param.id).collect());
        type_param_decls.insert(*def, Arc::from(params.clone().into_boxed_slice()));
      }
      for (def, kind) in decls.intrinsics.iter() {
        self.interned_intrinsics.insert(*def, *kind);
      }
    }
    let def_by_name = self.canonical_defs()?;
    let mut qualified_def_members: HashMap<(DefId, String, sem_ts::Namespace), DefId> =
      HashMap::new();
    for ((_, parent, name, ns), def_id) in def_by_name.iter() {
      if let Some(parent) = *parent {
        qualified_def_members.insert((parent, name.clone(), *ns), *def_id);
      }
    }
    self.qualified_def_members = Arc::new(qualified_def_members);
    let mut hir_def_maps: HashMap<FileId, HashMap<HirDefId, DefId>> = HashMap::new();
    let hir_namespaces = |kind: HirDefKind| -> sem_ts::Namespace {
      match kind {
        HirDefKind::Class => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
        HirDefKind::Enum => sem_ts::Namespace::VALUE | sem_ts::Namespace::TYPE,
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
    let ns_priority = |ns: &sem_ts::Namespace| {
      if ns.contains(sem_ts::Namespace::TYPE) {
        0
      } else if ns.contains(sem_ts::Namespace::VALUE) {
        1
      } else {
        2
      }
    };
    let mut ordered_defs: Vec<_> = def_by_name.iter().collect();
    ordered_defs.sort_by(|a, b| {
      let ((file_a, parent_a, name_a, ns_a), _) = a;
      let ((file_b, parent_b, name_b, ns_b), _) = b;
      (file_a.0, *parent_a, name_a, ns_priority(ns_a), ns_a.bits()).cmp(&(
        file_b.0,
        *parent_b,
        name_b,
        ns_priority(ns_b),
        ns_b.bits(),
      ))
    });
    let mut flat_defs: HashMap<(FileId, String), DefId> = HashMap::new();
    for ((file, parent, name, _), def_id) in ordered_defs.into_iter() {
      if parent.is_some() {
        continue;
      }
      flat_defs.entry((*file, name.clone())).or_insert(*def_id);
    }

    let mut lowered_entries: Vec<_> = self
      .hir_lowered
      .iter()
      .map(|(file, lowered)| (*file, lowered.clone()))
      .collect();
    lowered_entries.sort_by_key(|(file, _)| file.0);
    for (file, lowered) in lowered_entries.iter() {
      self.check_cancelled()?;
      let mut def_map: HashMap<DefId, DefId> = HashMap::new();
      for def in lowered.defs.iter() {
        if let Some(name) = lowered.names.resolve(def.name) {
          let name = name.to_string();
          let parent = def.parent;
          let namespaces = hir_namespaces(def.path.kind);
          let preferred = match def.path.kind {
            HirDefKind::Class
            | HirDefKind::Enum
            | HirDefKind::Interface
            | HirDefKind::TypeAlias => [
              sem_ts::Namespace::TYPE,
              sem_ts::Namespace::VALUE,
              sem_ts::Namespace::NAMESPACE,
            ],
            HirDefKind::Namespace | HirDefKind::Module => [
              sem_ts::Namespace::NAMESPACE,
              sem_ts::Namespace::VALUE,
              sem_ts::Namespace::TYPE,
            ],
            _ => [
              sem_ts::Namespace::VALUE,
              sem_ts::Namespace::TYPE,
              sem_ts::Namespace::NAMESPACE,
            ],
          };
          let mapped = preferred.into_iter().find_map(|ns| {
            namespaces
              .contains(ns)
              .then_some(())
              .and_then(|_| def_by_name.get(&(*file, parent, name.clone(), ns)).copied())
          });
          if let Some(mapped) = mapped {
            def_map.insert(def.id, mapped);
          }
        }
      }
      hir_def_maps.insert(*file, def_map);
    }

    self.collect_function_decl_types(&store, &flat_defs, &mut def_types, &mut type_params);
    self.check_class_implements(
      host,
      &store,
      &def_types,
      &type_params,
      &type_param_decls,
      &lowered_entries,
      &hir_def_maps,
      &def_by_name,
    )?;

    // Populate declared types for ambient value declarations (notably `.d.ts`
    // `declare const ...: ...` bindings). These do not appear in HIR `type_info`
    // and are required for expanding `typeof` references during expression
    // checking (e.g. `window.document.title`).
    let mut declared_value_defs: Vec<(DefId, FileId, TextRange)> = self
      .def_data
      .iter()
      .filter_map(|(def, data)| match data.kind {
        DefKind::Var(_) => Some((*def, data.file, data.span)),
        _ => None,
      })
      .collect();
    declared_value_defs.sort_by_key(|(def, file, span)| (file.0, span.start, span.end, def.0));
    for (def, file, span) in declared_value_defs.into_iter() {
      if let Some(declared) = self.declared_type_for_span(file, span) {
        def_types
          .entry(def)
          .and_modify(|existing| {
            *existing = ProgramState::merge_interned_decl_types(&store, *existing, declared);
          })
          .or_insert(declared);
      }
    }

    namespaces::populate_namespace_object_types(
      self,
      &store,
      &lowered_entries,
      &hir_def_maps,
      &def_by_name,
      &mut def_types,
    );

    let import_defs: Vec<_> = self
      .def_data
      .iter()
      .filter_map(|(def, data)| {
        matches!(data.kind, DefKind::Import(_)).then_some((*def, data.clone()))
      })
      .collect();
    for (def_id, data) in import_defs {
      if def_types.contains_key(&def_id) {
        continue;
      }
      let DefKind::Import(import) = data.kind else {
        continue;
      };
      let exports = match self.exports_for_import(&import) {
        Ok(exports) => exports,
        Err(_) => continue,
      };
      let Some(entry) = exports.get(&import.original) else {
        continue;
      };
      let mut cache = HashMap::new();
      let ty = if let Some(target_def) = entry.def {
        let ty = def_types
          .get(&target_def)
          .copied()
          .or_else(|| self.interned_def_types.get(&target_def).copied())
          .or_else(|| {
            self.def_types.get(&target_def).copied().map(|store_ty| {
              store.canon(convert_type_for_display(store_ty, self, &store, &mut cache))
            })
          });
        ty.unwrap_or(store.primitive_ids().unknown)
      } else if let Some(ty) = entry.type_id {
        if store.contains_type_id(ty) {
          ty
        } else {
          store.canon(convert_type_for_display(ty, self, &store, &mut cache))
        }
      } else {
        continue;
      };
      def_types.insert(def_id, ty);
    }

    module_namespace::populate_module_namespace_types(self, &store, &mut def_types);

    // `lower_decl_types` canonicalizes declarations with the same name within a
    // file (e.g. multiple `interface Foo { ... }` blocks) by mapping them onto a
    // single `DefId`. In that case the non-canonical defs have no entry in
    // `decls.types`, and later declaration-merging passes would fall back to
    // converting legacy types for display (which is lossy for features like
    // `unique symbol`).
    //
    // Copy the canonical types (and their parameter lists) onto only the
    // *missing* interface defs so the merge steps stay lossless without
    // clobbering distinct augmentations in other files.
    for def_map in hir_def_maps.values() {
      for (hir_def, mapped) in def_map.iter() {
        if hir_def == mapped {
          continue;
        }
        if !self
          .def_data
          .get(hir_def)
          .is_some_and(|data| matches!(data.kind, DefKind::Interface(_)))
        {
          continue;
        }
        if !def_types.contains_key(hir_def) {
          if let Some(ty) = def_types.get(mapped).copied() {
            def_types.insert(*hir_def, ty);
          }
        }
        if !type_params.contains_key(hir_def) {
          if let Some(params) = type_params.get(mapped).cloned() {
            type_params.insert(*hir_def, params);
          }
        }
      }
    }

    // Module/global augmentation in `.d.ts` ecosystems relies heavily on
    // declaration merging across files. `semantic-js` already merges
    // declarations into shared symbols, but we also need to merge the computed
    // declared types so any declaration (base or augmentation) expands to the
    // same merged type.
    //
    // For the high-value 95% case, focus on interface merging (used heavily by
    // module augmentation and `declare global`). Other merge kinds (functions,
    // namespaces, value+namespace) are handled by dedicated passes.
    if let Some(semantics) = self.semantics.as_ref() {
      let symbols = semantics.symbols();
      let mut interface_groups: BTreeMap<sem_ts::SymbolId, Vec<DefId>> = BTreeMap::new();
      for (def, data) in self.def_data.iter() {
        if !matches!(data.kind, DefKind::Interface(_)) {
          continue;
        }
        let Some(symbol) = semantics.symbol_for_def(sem_ts::DefId(def.0), sem_ts::Namespace::TYPE)
        else {
          continue;
        };
        interface_groups.entry(symbol).or_default().push(*def);
      }

      // `semantic-js` exposes merged global declarations (especially the TS
      // `lib.*.d.ts` ecosystem) via `global_symbols`. The per-def `symbol_for_def`
      // mapping does not always point at the merged global symbol, so merge
      // interface declarations grouped by the global symbol as well.
      for group in semantics.global_symbols().values() {
        let Some(symbol) = group.symbol_for(sem_ts::Namespace::TYPE, symbols) else {
          continue;
        };
        let decls = semantics.symbol_decls(symbol, sem_ts::Namespace::TYPE);
        if decls.len() <= 1 {
          continue;
        }
        for decl_id in decls.iter().copied() {
          let decl = symbols.decl(decl_id);
          if !matches!(decl.kind, sem_ts::DeclKind::Interface) {
            continue;
          }
          if let Some(def) = self.map_decl_to_program_def(decl, sem_ts::Namespace::TYPE) {
            interface_groups.entry(symbol).or_default().push(def);
          }
        }
      }

      for defs in interface_groups.values_mut() {
        defs.sort_by_key(|def| {
          self
            .def_data
            .get(def)
            .map(|data| (data.file.0, data.span.start, data.span.end, def.0))
            .unwrap_or((u32::MAX, u32::MAX, u32::MAX, def.0))
        });
        defs.dedup();
      }

      for defs in interface_groups.values() {
        if defs.len() <= 1 {
          continue;
        }
        let mut merged: Option<tti::TypeId> = None;
        for def in defs.iter().copied() {
          let Some(incoming) = def_types.get(&def).copied() else {
            continue;
          };
          merged = Some(match merged {
            Some(existing) => ProgramState::merge_interned_decl_types(&store, existing, incoming),
            None => incoming,
          });
        }
        let Some(merged) = merged else {
          continue;
        };
        for def in defs.iter().copied() {
          def_types.insert(def, merged);
        }
      }
    }

    self.interned_store = Some(store);
    self.interned_def_types = def_types;
    self.interned_type_params = type_params;
    self.interned_type_param_decls = type_param_decls;
    self.merge_callable_overload_types();
    self.merge_namespace_value_types()?;
    self.merge_interface_symbol_types_all()?;
    self.refresh_import_def_types()?;
    self.rebuild_interned_named_def_types();
    let interned_entries: Vec<_> = self.interned_def_types.clone().into_iter().collect();
    for (def, ty) in interned_entries {
      let imported = self.import_interned_type(ty);
      let mapped = if imported == self.builtin.unknown {
        ty
      } else {
        imported
      };
      self.def_types.insert(def, mapped);
    }
    self.recompute_global_bindings();
    codes::normalize_diagnostics(&mut self.diagnostics);
    self.decl_types_fingerprint = Some(fingerprint);
    Ok(())
  }
}
