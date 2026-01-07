use super::*;

impl ProgramState {
  pub(in super::super) fn rebuild_callable_overloads(&mut self) {
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

  pub(in super::super) fn callable_overload_defs(&mut self, def: DefId) -> Option<Vec<DefId>> {
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

  pub(in super::super) fn merged_overload_callable_type(
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

  pub(in super::super) fn callable_overload_type_for_def(
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

  pub(in super::super) fn merge_callable_overload_types(&mut self) {
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

  pub(in super::super) fn interned_unknown(&self) -> TypeId {
    self
      .interned_store
      .as_ref()
      .map(|s| s.primitive_ids().unknown)
      .unwrap_or(self.builtin.unknown)
  }
}
