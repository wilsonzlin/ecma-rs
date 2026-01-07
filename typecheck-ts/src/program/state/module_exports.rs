use super::*;

impl ProgramState {
  pub(super) fn exports_of_file(&mut self, file: FileId) -> Result<ExportMap, FatalError> {
    let store = Arc::clone(&self.store);
    if let Some(semantics) = self.semantics.clone() {
      let mut map = check::modules::exports_from_semantics(self, semantics.as_ref(), file)?;
      for entry in map.values_mut() {
        if let Some(def) = entry.def {
          if let Some(merged) = self.callable_overload_type_for_def(def, &store) {
            entry.type_id = Some(merged);
          }
        }
        let mut unknown = false;
        if let Some(ty) = entry.type_id {
          if store.contains_type_id(ty) {
            unknown = matches!(store.type_kind(ty), tti::TypeKind::Unknown);
          } else {
            unknown = true;
          }
        }
        if (entry.type_id.is_none() || unknown) && entry.def.is_some() {
          if let Some(def) = entry.def {
            entry.type_id = self.export_type_for_def(def)?;
          }
        }
        if let Some(def) = entry.def {
          if let Some(defs) = self.callable_overload_defs(def) {
            if defs.len() > 1 {
              let existing = entry
                .type_id
                .map(|ty| callable_signatures(store.as_ref(), ty))
                .unwrap_or_default();
              if existing.len() < defs.len() {
                if let Some(merged) = self.merged_overload_callable_type(&defs, &store) {
                  entry.type_id = Some(merged);
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
        if let Some(merged) = self.callable_overload_type_for_def(def, &store) {
          entry.type_id = Some(merged);
        }
      }
      let mut unknown = false;
      if let Some(ty) = entry.type_id {
        if store.contains_type_id(ty) {
          unknown = matches!(store.type_kind(ty), tti::TypeKind::Unknown);
        } else {
          unknown = true;
        }
      }
      if let Some(def) = entry.def {
        if unknown || entry.type_id.is_none() {
          entry.type_id = self.export_type_for_def(def)?;
        }
      }
      if let Some(def) = entry.def {
        if let Some(defs) = self.callable_overload_defs(def) {
          if defs.len() > 1 {
            let existing = entry
              .type_id
              .map(|ty| callable_signatures(store.as_ref(), ty))
              .unwrap_or_default();
            if existing.len() < defs.len() {
              if let Some(merged) = self.merged_overload_callable_type(&defs, &store) {
                entry.type_id = Some(merged);
              }
            }
          }
        }
      }
    }
    Ok(map)
  }

  pub(super) fn exports_of_ambient_module(
    &mut self,
    specifier: &str,
  ) -> Result<ExportMap, FatalError> {
    let Some(semantics) = self.semantics.clone() else {
      return Ok(ExportMap::new());
    };
    check::modules::exports_of_ambient_module(self, &semantics, specifier)
  }

  pub(super) fn exports_for_import(
    &mut self,
    import: &ImportData,
  ) -> Result<ExportMap, FatalError> {
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
