use super::*;

impl Program {
  /// Export map for a file.
  pub fn exports_of(&self, file: FileId) -> ExportMap {
    match self.exports_of_fallible(file) {
      Ok(exports) => exports,
      Err(fatal) => {
        self.record_fatal(fatal);
        ExportMap::new()
      }
    }
  }

  pub fn exports_of_fallible(&self, file: FileId) -> Result<ExportMap, FatalError> {
    self.with_interned_state(|state| {
      let mut exports = state.exports_of_file(file)?;

      // `typecheck-ts-harness` gathers export type facts via `Program::exports_of`.
      // Its TypeScript oracle uses `checker.getTypeOfSymbolAtLocation(...)`, which
      // returns `any` for type-only exports (interfaces/type aliases). Keep Rust
      // export type facts aligned with that behaviour without affecting the
      // internal export map used for type checking/import resolution.
      let any = state.builtin.any;
      if let Some(semantics) = state.semantics.as_ref() {
        if let Some(sem_exports) = semantics.exports_of_opt(sem_ts::FileId(file.0)) {
          let symbols = semantics.symbols();
          for (name, entry) in exports.iter_mut() {
            let Some(group) = sem_exports.get(name) else {
              continue;
            };
            let is_value_export = group
              .symbol_for(sem_ts::Namespace::VALUE, symbols)
              .is_some()
              || group
                .symbol_for(sem_ts::Namespace::NAMESPACE, symbols)
                .is_some();
            if !is_value_export {
              entry.type_id = Some(any);
            }
          }
        }
      } else {
        for entry in exports.values_mut() {
          let is_type_only = entry
            .def
            .and_then(|def| state.def_data.get(&def))
            .is_some_and(|data| matches!(data.kind, DefKind::Interface(_) | DefKind::TypeAlias(_)));
          if is_type_only {
            entry.type_id = Some(any);
          }
        }
      }

      Ok(exports)
    })
  }

  /// Global bindings available to all files (from libs, `.d.ts`, and builtins).
  pub fn global_bindings(&self) -> Arc<BTreeMap<String, SymbolBinding>> {
    match self.with_interned_state(|state| Ok(Arc::clone(&state.global_bindings))) {
      Ok(bindings) => bindings,
      Err(fatal) => {
        self.record_fatal(fatal);
        Arc::new(BTreeMap::new())
      }
    }
  }
}
