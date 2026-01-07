use super::*;

impl ProgramState {
  pub(in super::super) fn module_namespace_object_type(
    &mut self,
    exports: &ExportMap,
  ) -> Result<TypeId, FatalError> {
    let store = Arc::clone(&self.store);
    let prim = store.primitive_ids();
    let mut shape = tti::Shape::new();
    for (name, entry) in exports.iter() {
      if name == "*" {
        continue;
      }
      let resolved_def = entry
        .def
        .or_else(|| self.symbol_to_def.get(&entry.symbol).copied());
      if let Some(def) = resolved_def {
        if let Some(data) = self.def_data.get(&def) {
          if matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)) {
            continue;
          }
        }
      }
      let mut ty = entry.type_id;
      if ty.is_none() {
        if let Some(def) = resolved_def {
          ty = self.export_type_for_def(def)?;
          if ty.is_none() {
            ty = Some(self.type_of_def(def)?);
          }
        }
      }
      let ty = ty.unwrap_or(prim.unknown);
      let ty = if store.contains_type_id(ty) {
        store.canon(ty)
      } else {
        prim.unknown
      };
      let key = PropKey::String(store.intern_name(name.clone()));
      shape.properties.push(Property {
        key,
        data: PropData {
          ty,
          optional: false,
          readonly: true,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }
    let shape_id = store.intern_shape(shape);
    let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
    Ok(store.canon(store.intern_type(tti::TypeKind::Object(obj_id))))
  }

  pub(in super::super) fn module_namespace_type(
    &mut self,
    file: FileId,
  ) -> Result<TypeId, FatalError> {
    self.check_cancelled()?;
    let store = Arc::clone(&self.store);

    if let Some(cached) = self.module_namespace_types.get(&file).copied() {
      return Ok(cached);
    }

    let prim = store.primitive_ids();
    if self.module_namespace_in_progress.contains(&file) {
      return Ok(prim.unknown);
    }

    self.module_namespace_in_progress.insert(file);
    let computed = panic::catch_unwind(AssertUnwindSafe(|| {
      let exports = self.exports_of_file(file)?;
      let mut names: Vec<String> = if let Some(semantics) = self.semantics.as_ref() {
        semantics
          .exports_of_opt(sem_ts::FileId(file.0))
          .map(|exports| {
            exports
              .iter()
              .filter_map(|(name, group)| {
                group
                  .symbol_for(sem_ts::Namespace::VALUE, semantics.symbols())
                  .is_some()
                  .then_some(name.clone())
              })
              .collect()
          })
          .unwrap_or_default()
      } else {
        exports
          .iter()
          .filter_map(|(name, entry)| {
            let is_value = entry
              .def
              .and_then(|def| self.def_data.get(&def))
              .map(|data| !matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)))
              .unwrap_or(true);
            is_value.then_some(name.clone())
          })
          .collect()
      };
      names.sort();
      names.dedup();

      let mut shape = tti::Shape::new();
      for name in names.into_iter() {
        let entry = exports.get(&name);
        let ty = entry
          .and_then(|entry| entry.type_id)
          .or_else(|| {
            entry
              .and_then(|entry| entry.def)
              .and_then(|def| self.export_type_for_def(def).ok().flatten())
          })
          .or_else(|| {
            entry
              .and_then(|entry| entry.def)
              .and_then(|def| self.interned_def_types.get(&def).copied())
          })
          .unwrap_or(prim.unknown);
        let ty = if store.contains_type_id(ty) {
          store.canon(ty)
        } else {
          prim.unknown
        };
        let key = PropKey::String(store.intern_name(name.clone()));
        shape.properties.push(Property {
          key,
          data: PropData {
            ty,
            optional: false,
            readonly: true,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(tti::ObjectType { shape: shape_id });
      Ok(store.canon(store.intern_type(tti::TypeKind::Object(obj_id))))
    }));
    self.module_namespace_in_progress.remove(&file);
    let ty = match computed {
      Ok(Ok(ty)) => ty,
      Ok(Err(err)) => return Err(err),
      Err(payload) => panic::resume_unwind(payload),
    };
    self.module_namespace_types.insert(file, ty);
    Ok(ty)
  }
}
