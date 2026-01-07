use super::*;

impl ProgramState {
  pub(in super::super) fn export_type_for_def(
    &mut self,
    def: DefId,
  ) -> Result<Option<TypeId>, FatalError> {
    let store = Arc::clone(&self.store);
    if let Some(merged) = self.callable_overload_type_for_def(def, &store) {
      return Ok(Some(merged));
    }
    if let Some(defs) = self.callable_overload_defs(def) {
      if defs.len() > 1 {
        if let Some(merged) = self.merged_overload_callable_type(&defs, &store) {
          return Ok(Some(merged));
        }
      }
    }
    let ty = self.type_of_def(def)?;
    Ok(Some(store.canon(ty)))
  }
}
