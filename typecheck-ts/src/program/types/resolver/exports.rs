use super::*;

impl ProgramTypeResolver {
  pub(super) fn resolve_export_path(
    &self,
    segments: &[String],
    module: &mut sem_ts::FileId,
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      if let Some(exports) = self.exports.get(&FileId(module.0)) {
        if let Some(entry) = exports.get(segment) {
          if is_last {
            if let Some(def) = entry.def {
              return Some(def);
            }
          }
        }
      }
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let symbol = self.semantics.resolve_export(*module, segment, ns)?;
      if is_last {
        if let Some(def) = self.pick_decl(symbol, final_ns) {
          return Some(def);
        }
        if final_ns.contains(sem_ts::Namespace::VALUE) {
          if let sem_ts::SymbolOrigin::Import { from, imported } =
            &self.semantics.symbols().symbol(symbol).origin
          {
            if imported == "*" {
              if let sem_ts::ModuleRef::File(dep_file) = from {
                return self.module_namespace_defs.get(&FileId(dep_file.0)).copied();
              }
            }
          }
        }
        return None;
      }
      *module = self.import_origin_file(symbol)?;
    }
    None
  }

  fn resolve_export_symbol_in_module_ref(
    &self,
    module: &sem_ts::ModuleRef,
    name: &str,
    ns: sem_ts::Namespace,
  ) -> Option<sem_ts::SymbolId> {
    match module {
      sem_ts::ModuleRef::File(file) => self.semantics.resolve_export(*file, name, ns),
      sem_ts::ModuleRef::Ambient(specifier) => self
        .semantics
        .exports_of_ambient_module(specifier)?
        .get(name)?
        .symbol_for(ns, self.semantics.symbols()),
      sem_ts::ModuleRef::Unresolved(_) => None,
    }
  }

  pub(super) fn resolve_export_path_in_module_ref(
    &self,
    mut module: sem_ts::ModuleRef,
    segments: &[String],
    final_ns: sem_ts::Namespace,
  ) -> Option<DefId> {
    if segments.is_empty() {
      return None;
    }
    for (idx, segment) in segments.iter().enumerate() {
      let is_last = idx + 1 == segments.len();
      let ns = if is_last {
        final_ns
      } else {
        sem_ts::Namespace::NAMESPACE
      };
      let symbol = self.resolve_export_symbol_in_module_ref(&module, segment, ns)?;
      if is_last {
        return self.pick_decl(symbol, final_ns);
      }
      module = match &self.semantics.symbols().symbol(symbol).origin {
        sem_ts::SymbolOrigin::Import { from, .. } => from.clone(),
        _ => return None,
      };
    }
    None
  }
}
