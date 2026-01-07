use super::*;

impl ProgramState {
  pub(super) fn exports_of_file(&mut self, file: FileId) -> Result<ExportMap, FatalError> {
    if let Some(semantics) = self.semantics.clone() {
      let mut map = check::modules::exports_from_semantics(self, semantics.as_ref(), file)?;
      for entry in map.values_mut() {
        if let Some(def) = entry.def {
          if let Some(store) = self.interned_store.clone() {
            let mut cache = HashMap::new();
            if let Some(merged) = self.callable_overload_type_for_def(def, &store, &mut cache) {
              entry.type_id = Some(merged);
            }
          }
        }
        let mut unknown = false;
        if let Some(ty) = entry.type_id {
          if self.type_store.contains_id(ty) {
            unknown = matches!(self.type_store.kind(ty), TypeKind::Unknown);
          } else if let Some(store) = self.interned_store.as_ref() {
            if store.contains_type_id(ty) {
              unknown = matches!(store.type_kind(ty), tti::TypeKind::Unknown);
            }
          }
        }
        if entry.type_id.is_none() || unknown {
          if let Some(def) = entry.def {
            if let Some(ty) = self.export_type_for_def(def)? {
              entry.type_id = Some(ty);
            }
          }
        }
        if let Some(def) = entry.def {
          if let Some(store) = self.interned_store.clone() {
            if let Some(defs) = self.callable_overload_defs(def) {
              if defs.len() > 1 {
                let existing = entry
                  .type_id
                  .and_then(|ty| Some(callable_signatures(store.as_ref(), ty)))
                  .unwrap_or_default();
                if existing.len() < defs.len() {
                  let mut cache = HashMap::new();
                  if let Some(merged) =
                    self.merged_overload_callable_type(&defs, &store, &mut cache)
                  {
                    entry.type_id = Some(merged);
                  }
                }
              }
            }
          }
        }
      }
      if let Some(state) = self.files.get(&file) {
        for (name, local) in state.exports.iter() {
          match map.get_mut(name) {
            Some(entry) => {
              if entry.type_id.is_none() {
                entry.type_id = local.type_id;
              }
              if entry.def.is_none() {
                entry.def = local.def;
              }
            }
            None => {
              map.insert(name.clone(), local.clone());
            }
          }
        }
      }
      return Ok(map);
    }
    let Some(state) = self.files.get(&file).cloned() else {
      return Ok(ExportMap::new());
    };
    let mut map = state.exports.clone();
    for entry in map.values_mut() {
      if let Some(def) = entry.def {
        if let Some(store) = self.interned_store.clone() {
          let mut cache = HashMap::new();
          if let Some(merged) = self.callable_overload_type_for_def(def, &store, &mut cache) {
            entry.type_id = Some(merged);
          }
        }
      }
      let mut unknown = false;
      if let Some(ty) = entry.type_id {
        if self.type_store.contains_id(ty) {
          unknown = matches!(self.type_store.kind(ty), TypeKind::Unknown);
        } else if let Some(store) = self.interned_store.as_ref() {
          if store.contains_type_id(ty) {
            unknown = matches!(store.type_kind(ty), tti::TypeKind::Unknown);
          }
        }
      }
      if let Some(def) = entry.def {
        if unknown || entry.type_id.is_none() {
          if let Some(ty) = self.export_type_for_def(def)? {
            entry.type_id = Some(ty);
          }
        }
      }
      if let Some(def) = entry.def {
        if let Some(store) = self.interned_store.clone() {
          if let Some(defs) = self.callable_overload_defs(def) {
            if defs.len() > 1 {
              let existing = entry
                .type_id
                .and_then(|ty| Some(callable_signatures(store.as_ref(), ty)))
                .unwrap_or_default();
              if existing.len() < defs.len() {
                let mut cache = HashMap::new();
                if let Some(merged) = self.merged_overload_callable_type(&defs, &store, &mut cache)
                {
                  entry.type_id = Some(merged);
                }
              }
            }
          }
        }
      }
    }
    Ok(map)
  }

  pub(super) fn exports_of_ambient_module(&mut self, specifier: &str) -> Result<ExportMap, FatalError> {
    let Some(semantics) = self.semantics.clone() else {
      return Ok(ExportMap::new());
    };
    check::modules::exports_of_ambient_module(self, &semantics, specifier)
  }

  pub(super) fn exports_for_import(&mut self, import: &ImportData) -> Result<ExportMap, FatalError> {
    match &import.target {
      ImportTarget::File(file) => self.exports_of_file(*file),
      ImportTarget::Unresolved { specifier } => self.exports_of_ambient_module(specifier),
    }
  }

  pub(super) fn export_assignment_target_def(&self, file: FileId) -> Option<DefId> {
    let semantics = self.semantics.as_ref()?;
    let path = export_assignment_path_for_file(semantics.as_ref(), sem_ts::FileId(file.0))?;
    self.resolve_import_alias_target(file, &path)
  }

}
