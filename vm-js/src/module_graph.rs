use crate::execution_context::ModuleId;
use crate::module_record::ModuleNamespaceCache;
use crate::module_record::ResolveExportResult;
use crate::{LoadedModuleRequest, ModuleRequest};
use crate::module_record::SourceTextModuleRecord;
use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{cmp_utf16, GcObject, Realm, Scope, Value, VmError};

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

  /// Fallible accessor for module records.
  ///
  /// Unlike [`ModuleGraph::module`], this returns `None` for invalid `ModuleId`s instead of
  /// panicking.
  pub fn get_module(&self, id: ModuleId) -> Option<&SourceTextModuleRecord> {
    self.modules.get(id.to_raw() as usize)
  }

  /// Fallible mutable accessor for module records.
  ///
  /// Unlike [`ModuleGraph::module_mut`], this returns `None` for invalid `ModuleId`s instead of
  /// panicking.
  pub fn get_module_mut(&mut self, id: ModuleId) -> Option<&mut SourceTextModuleRecord> {
    self.modules.get_mut(id.to_raw() as usize)
  }

  pub fn module_count(&self) -> usize {
    self.modules.len()
  }

  /// Implements `GetModuleNamespace` (ECMA-262 `#sec-getmodulenamespace`) for a module in this
  /// graph.
  ///
  /// If the module already has a cached namespace object, it is returned. Otherwise this creates
  /// and caches a new namespace object using [`module_namespace_create`].
  ///
  /// Important: this operation must **never throw** due to missing/ambiguous exports; those names
  /// are excluded from the namespace.
  pub fn get_module_namespace(
    &mut self,
    module: ModuleId,
    scope: &mut Scope<'_>,
    realm: &Realm,
  ) -> Result<GcObject, VmError> {
    let idx = module_index(module);

    if let Some(cache) = self.modules[idx].namespace.as_ref() {
      let Some(Value::Object(obj)) = scope.heap().get_root(cache.object) else {
        return Err(VmError::InvalidHandle);
      };
      return Ok(obj);
    }

    // exportedNames = module.GetExportedNames()
    let exported_names = self.modules[idx].get_exported_names(self, module);

    // unambiguousNames = [ name | name in exportedNames, module.ResolveExport(name) is ResolvedBinding ]
    let mut unambiguous_names = Vec::<String>::new();
    for name in exported_names {
      if matches!(
        self.modules[idx].resolve_export(self, module, &name),
        ResolveExportResult::Resolved(_)
      ) {
        unambiguous_names.push(name);
      }
    }

    // namespace = ModuleNamespaceCreate(module, unambiguousNames)
    let (namespace_obj, exports_sorted) =
      module_namespace_create(scope, realm, &unambiguous_names)?;

    // Cache the namespace object via a persistent root so it remains live across GC.
    let root = scope.heap_mut().add_root(Value::Object(namespace_obj))?;

    self.modules[idx].namespace = Some(ModuleNamespaceCache {
      object: root,
      exports: exports_sorted,
    });

    Ok(namespace_obj)
  }

  /// Convenience accessor for the module namespace's cached `[[Exports]]` list.
  pub fn module_namespace_exports(&self, module: ModuleId) -> Option<&[String]> {
    self.module(module).namespace_exports()
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
            .push(LoadedModuleRequest::new(request, imported));
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
      .find(|loaded| loaded.request.spec_equal(request))
      .map(|loaded| loaded.module)
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

/// Implements `ModuleNamespaceCreate` (ECMA-262 `#sec-modulenamespacecreate`) – MVP version.
///
/// This creates an ordinary object with the correct `[[Prototype]]` and `%Symbol.toStringTag%`
/// property. A real module namespace is an *exotic object* with virtual string-keyed export
/// properties backed by live bindings; that behaviour will be added once module environments exist.
fn module_namespace_create(
  scope: &mut Scope<'_>,
  realm: &Realm,
  exports: &[String],
) -> Result<(GcObject, Vec<String>), VmError> {
  // 1. Let exports be a List whose elements are the String values representing the exports of module.
  // 2. Let sortedExports be a List containing the same values as exports in ascending order.
  let mut sorted_exports = exports.to_vec();
  sorted_exports.sort_by(|a, b| cmp_utf16(a, b));

  // Allocate the namespace object.
  //
  // Root it before any further allocations (e.g. the `toStringTag` value string) in case those
  // allocations trigger a GC.
  let mut inner = scope.reborrow();
  let obj = inner.alloc_object_with_prototype(None)?;
  inner.push_root(Value::Object(obj))?;

  // prototype must be `null`.
  inner.heap_mut().object_set_prototype(obj, None)?;

  // Define %Symbol.toStringTag% = "Module" (non-writable, non-enumerable, non-configurable).
  let tag_string = inner.alloc_string("Module")?;
  let desc = PropertyDescriptor {
    enumerable: false,
    configurable: false,
    kind: PropertyKind::Data {
      value: Value::String(tag_string),
      writable: false,
    },
  };
  inner.define_property(
    obj,
    PropertyKey::Symbol(realm.well_known_symbols().to_string_tag),
    desc,
  )?;

  // Define placeholder properties for exported bindings.
  //
  // A real module namespace is an exotic object whose string-keyed properties read **live
  // bindings** from module environments. Those environments do not exist yet; by installing
  // accessor properties we ensure `Heap::get` does not silently return `undefined` for exports.
  for export_name in &sorted_exports {
    let key = inner.alloc_string(export_name)?;
    let desc = PropertyDescriptor {
      enumerable: true,
      configurable: false,
      kind: PropertyKind::Accessor {
        // Any non-`undefined` getter will cause `Heap::get` to report `VmError::Unimplemented`.
        get: Value::Null,
        set: Value::Undefined,
      },
    };
    inner.define_property(obj, PropertyKey::String(key), desc)?;
  }

  Ok((obj, sorted_exports))
}
