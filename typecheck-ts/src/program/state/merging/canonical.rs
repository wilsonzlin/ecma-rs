use super::*;

impl ProgramState {
  pub(in super::super) fn canonical_defs(
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

  pub(in super::super) fn rebuild_namespace_member_index(&mut self) -> Result<(), FatalError> {
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

}
