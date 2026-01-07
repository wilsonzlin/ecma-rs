use super::*;

impl ProgramState {
  pub(in super::super) fn merge_interface_symbol_types(
    &mut self,
    def: DefId,
  ) -> Result<(), FatalError> {
    let store = Arc::clone(&self.store);
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
    let mut merged: Option<tti::TypeId> = None;
    for iface_def in interface_defs.iter().copied() {
      if !self.interned_def_types.contains_key(&iface_def) {
        let _ = self.type_of_def(iface_def);
      }
      let Some(ty) = self
        .interned_def_types
        .get(&iface_def)
        .copied()
        .and_then(|ty| store.contains_type_id(ty).then_some(store.canon(ty)))
      else {
        continue;
      };
      if matches!(store.type_kind(ty), tti::TypeKind::Unknown) {
        continue;
      }
      merged = Some(match merged {
        Some(existing) => ProgramState::merge_interned_decl_types(&store, existing, ty),
        None => ty,
      });
    }
    let merged = store.canon(merged.unwrap_or(prim.unknown));

    for iface_def in interface_defs {
      self.interned_def_types.insert(iface_def, merged);
      if let Some(data) = self.def_data.get_mut(&iface_def) {
        if let DefKind::Interface(existing) = &mut data.kind {
          existing.typ = merged;
        }
      }
    }

    Ok(())
  }

  pub(in super::super) fn merge_interface_symbol_types_all(&mut self) -> Result<(), FatalError> {
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

  pub(in super::super) fn refresh_import_def_types(&mut self) -> Result<(), FatalError> {
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
      self.interned_def_types.remove(&def);
    }
    for def in import_defs.into_iter() {
      self.type_of_def(def)?;
    }
    Ok(())
  }
}
