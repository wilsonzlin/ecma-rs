use super::*;

impl TypeResolver for ProgramTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, sem_ts::Namespace::TYPE),
      _ => self
        .resolve_namespace_import_path(path, sem_ts::Namespace::TYPE)
        .or_else(|| self.resolve_namespace_member_path(path, sem_ts::Namespace::TYPE)),
    }
  }

  fn resolve_typeof(&self, path: &[String]) -> Option<DefId> {
    match path {
      [] => None,
      [name] => self.resolve_symbol_in_module(name, sem_ts::Namespace::VALUE),
      _ => self
        .resolve_namespace_import_path(path, sem_ts::Namespace::VALUE)
        .or_else(|| self.resolve_namespace_member_path(path, sem_ts::Namespace::VALUE)),
    }
  }

  fn resolve_import_type(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    let Some(from_key) = self.registry.lookup_key(self.current_file) else {
      return None;
    };
    let target_key = self.host.resolve(&from_key, module)?;
    let target_file = self.registry.lookup_id(&target_key)?;
    let mut module = sem_ts::FileId(target_file.0);
    let Some(path) = qualifier else {
      return None;
    };
    if path.is_empty() {
      return None;
    }
    self.resolve_export_path(path, &mut module, sem_ts::Namespace::TYPE)
  }

  fn resolve_import_typeof(&self, module: &str, qualifier: Option<&[String]>) -> Option<DefId> {
    let Some(from_key) = self.registry.lookup_key(self.current_file) else {
      return None;
    };
    let target_key = self.host.resolve(&from_key, module)?;
    let target_file = self.registry.lookup_id(&target_key)?;
    let mut module = sem_ts::FileId(target_file.0);
    let Some(path) = qualifier else {
      return self.module_namespace_defs.get(&target_file).copied();
    };
    if path.is_empty() {
      return self.module_namespace_defs.get(&target_file).copied();
    }
    self.resolve_export_path(path, &mut module, sem_ts::Namespace::VALUE)
  }
}
