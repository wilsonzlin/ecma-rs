use crate::execution_context::ModuleId;
use crate::module_loading::ModuleRequest;
use crate::module_record::SourceTextModuleRecord;

/// Minimal in-memory module graph used to exercise ECMA-262 module record algorithms.
///
/// This intentionally does **not** implement a full module loader. Tests are responsible for
/// constructing module records and linking their `[[RequestedModules]]` entries to concrete
/// [`ModuleId`]s.
#[derive(Debug, Default)]
pub struct ModuleGraph {
  modules: Vec<SourceTextModuleRecord>,
  host_resolve: Vec<(ModuleRequest, ModuleId)>,
}

impl ModuleGraph {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add_module(&mut self, record: SourceTextModuleRecord) -> ModuleId {
    let id = ModuleId::from_raw(self.modules.len() as u64);
    self.modules.push(record);
    id
  }

  /// Adds a module to the graph and registers it under `specifier` for later linking.
  pub fn add_module_with_specifier(
    &mut self,
    specifier: impl AsRef<str>,
    record: SourceTextModuleRecord,
  ) -> ModuleId {
    let id = self.add_module(record);
    self.register_specifier(specifier, id);
    id
  }

  /// Registers a host resolution mapping used by [`ModuleGraph::link_all_by_specifier`].
  pub fn register_specifier(&mut self, specifier: impl AsRef<str>, module: ModuleId) {
    self
      .host_resolve
      .push((module_request_from_specifier(specifier.as_ref()), module));
  }

  pub fn module(&self, id: ModuleId) -> &SourceTextModuleRecord {
    &self.modules[module_index(id)]
  }

  pub fn module_mut(&mut self, id: ModuleId) -> &mut SourceTextModuleRecord {
    &mut self.modules[module_index(id)]
  }

  pub fn module_count(&self) -> usize {
    self.modules.len()
  }

  /// Populates each module's `[[LoadedModules]]` mapping using the host resolution map and the
  /// module's `[[RequestedModules]]` list.
  pub fn link_all_by_specifier(&mut self) {
    for referrer_idx in 0..self.modules.len() {
      let requests = self.modules[referrer_idx].requested_modules.clone();
      for request in requests {
        if let Some(imported) = self.resolve_host_module(&request) {
          self.modules[referrer_idx]
            .loaded_modules
            .push((request, imported));
        } else {
          // `ModuleGraph` is a small in-memory helper used primarily by unit tests. Avoid panicking
          // in library code; missing host resolution simply leaves the request unlinked.
          debug_assert!(
            false,
            "ModuleGraph::link_all_by_specifier: no module registered for specifier {:?}",
            request.specifier
          );
        }
      }
    }
  }

  /// Implements ECMA-262 `GetImportedModule(referrer, request)`.
  pub fn get_imported_module(&self, referrer: ModuleId, request: &ModuleRequest) -> Option<ModuleId> {
    self
      .modules[module_index(referrer)]
      .loaded_modules
      .iter()
      .find_map(|(req, id)| (req == request).then_some(*id))
  }

  fn resolve_host_module(&self, request: &ModuleRequest) -> Option<ModuleId> {
    self
      .host_resolve
      .iter()
      .find_map(|(req, id)| (req == request).then_some(*id))
  }
}

fn module_index(id: ModuleId) -> usize {
  // `ModuleId` is an opaque token at the VM boundary, but `ModuleGraph` uses it as a stable index
  // into its module vector for tests. Tests construct module ids exclusively via
  // `ModuleGraph::add_module*`, which uses the raw index representation.
  id.to_raw() as usize
}

fn module_request_from_specifier(specifier: &str) -> ModuleRequest {
  ModuleRequest::new(specifier, Vec::new())
}
