use super::*;

impl ProgramState {
  pub(in super::super) fn resolve_value_ref_type(&mut self, ty: TypeId) -> Result<TypeId, FatalError> {
    let Some(store) = self.interned_store.clone() else {
      return Ok(ty);
    };
    if std::env::var("DEBUG_OVERLOAD").is_ok() {
      if store.contains_type_id(ty) {
        eprintln!(
          "DEBUG resolve_value_ref_type input kind {:?}",
          store.type_kind(store.canon(ty))
        );
      } else {
        eprintln!("DEBUG resolve_value_ref_type input not in store");
      }
    }
    if !store.contains_type_id(ty) {
      return Ok(ty);
    }
    let canonical = store.canon(ty);
    if let tti::TypeKind::Ref { def, args } = store.type_kind(canonical) {
      if args.is_empty() {
        let def_id = DefId(def.0);
        if self.type_stack.contains(&def_id) {
          return Ok(canonical);
        }
        let should_resolve = self
          .def_data
          .get(&def_id)
          .map(|data| {
            matches!(
              data.kind,
              DefKind::Function(_)
                | DefKind::Var(_)
                | DefKind::Class(_)
                | DefKind::Enum(_)
                | DefKind::Namespace(_)
                | DefKind::Module(_)
                | DefKind::Import(_)
            )
          })
          .unwrap_or(false);
        if should_resolve {
          if std::env::var("DEBUG_OVERLOAD").is_ok() {
            if let Some(data) = self.def_data.get(&def_id) {
              eprintln!(
                "DEBUG resolve_value_ref_type ref to {} {:?}",
                data.name, data.kind
              );
            }
          }
          let resolved = self.type_of_def(def_id)?;
          let resolved = self.ensure_interned_type(resolved);
          if std::env::var("DEBUG_OVERLOAD").is_ok() {
            eprintln!(
              "DEBUG resolve_value_ref_type resolved kind {:?}",
              store.type_kind(resolved)
            );
          }
          if !matches!(store.type_kind(resolved), tti::TypeKind::Unknown) {
            return Ok(store.canon(resolved));
          }
        }
      }
    }
    Ok(canonical)
  }

}
