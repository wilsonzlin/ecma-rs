//! ECMAScript module graph loading.
//!
//! This implements the ECMA-262 "module graph loading state machine" used by cyclic modules:
//! - `GraphLoadingState` record
//! - `LoadRequestedModules`
//! - `InnerModuleLoading`
//! - `ContinueModuleLoading`
//!
//! Spec reference (ECMA-262):
//! - `GraphLoadingState` record: `#sec-graphloadingstate-records`
//! - `LoadRequestedModules` / `InnerModuleLoading` / `ContinueModuleLoading`:
//!   `#sec-moduleloadingstate-machinery`
//!
//! This VM crate does not yet have a full `%Promise%` implementation; the spec's Promise capability
//! is represented by [`ModuleGraphLoadPromise`], a small internal completion sink that can be
//! resolved/rejected once.

use crate::execution_context::ModuleId;
use crate::VmError;
use std::any::Any;
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;
use std::sync::Arc;

/// Module linking/loading status.
///
/// This is a minimal subset of ECMA-262's `ModuleStatus` enum; additional states will be added as
/// module linking/evaluation are implemented.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModuleStatus {
  New,
  Unlinked,
}

/// A module request record.
///
/// Mirrors the `ModuleRequest` record used by cyclic module records, including optional import
/// attributes.
#[derive(Clone, PartialEq, Eq)]
pub struct ModuleRequest {
  pub specifier: Arc<str>,
  pub import_attributes: BTreeMap<Arc<str>, Arc<str>>,
}

impl fmt::Debug for ModuleRequest {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("ModuleRequest")
      .field("specifier", &self.specifier)
      .field("import_attributes", &self.import_attributes)
      .finish()
  }
}

impl ModuleRequest {
  pub fn new(specifier: impl Into<Arc<str>>) -> Self {
    Self {
      specifier: specifier.into(),
      import_attributes: BTreeMap::new(),
    }
  }

  pub fn with_import_attribute(
    mut self,
    key: impl Into<Arc<str>>,
    value: impl Into<Arc<str>>,
  ) -> Self {
    self.import_attributes.insert(key.into(), value.into());
    self
  }
}

/// A `ModuleRequest` paired with its resolved/loaded module record.
#[derive(Clone, Debug)]
pub struct LoadedModuleRequest<T> {
  pub request: ModuleRequest,
  pub module: T,
}

/// A cyclic module record (minimal surface for graph loading).
#[derive(Clone, Debug)]
pub struct CyclicModuleRecord {
  pub requested_modules: Vec<ModuleRequest>,
  pub loaded_modules: Vec<LoadedModuleRequest<ModuleId>>,
  pub status: ModuleStatus,
}

impl CyclicModuleRecord {
  pub fn new(requested_modules: Vec<ModuleRequest>) -> Self {
    Self {
      requested_modules,
      loaded_modules: Vec::new(),
      status: ModuleStatus::New,
    }
  }

  /// Finds an entry in `loaded_modules` using ECMA-262's `ModuleRequestsEqual` semantics.
  pub fn loaded_module_for_request(&self, request: &ModuleRequest) -> Option<ModuleId> {
    self
      .loaded_modules
      .iter()
      .find(|loaded| module_requests_equal(&loaded.request, request))
      .map(|loaded| loaded.module)
  }

  /// Inserts or replaces an entry in `loaded_modules` using ECMA-262's `ModuleRequestsEqual`
  /// semantics.
  pub fn set_loaded_module(&mut self, request: ModuleRequest, module: ModuleId) {
    if let Some(existing) = self
      .loaded_modules
      .iter_mut()
      .find(|loaded| module_requests_equal(&loaded.request, &request))
    {
      existing.module = module;
      return;
    }
    self.loaded_modules.push(LoadedModuleRequest { request, module });
  }
}

/// A module record stored in a [`ModuleStore`].
#[derive(Clone, Debug)]
pub enum ModuleRecord {
  Cyclic(CyclicModuleRecord),
  /// Placeholder for non-cyclic module record types (e.g. synthetic modules).
  NonCyclic,
}

/// In-memory module record store used by the loader.
#[derive(Debug, Default)]
pub struct ModuleStore {
  modules: HashMap<ModuleId, ModuleRecord>,
  next_id: u64,
}

impl ModuleStore {
  pub fn insert(&mut self, module: ModuleRecord) -> ModuleId {
    let id = ModuleId::from_raw(self.next_id);
    self.next_id = self.next_id.wrapping_add(1);
    self.modules.insert(id, module);
    id
  }

  pub fn insert_cyclic(&mut self, module: CyclicModuleRecord) -> ModuleId {
    self.insert(ModuleRecord::Cyclic(module))
  }

  pub fn get(&self, id: ModuleId) -> &ModuleRecord {
    self
      .modules
      .get(&id)
      .unwrap_or_else(|| panic!("invalid ModuleId {id:?}"))
  }

  pub fn get_mut(&mut self, id: ModuleId) -> &mut ModuleRecord {
    self
      .modules
      .get_mut(&id)
      .unwrap_or_else(|| panic!("invalid ModuleId {id:?}"))
  }

  pub fn get_cyclic(&self, id: ModuleId) -> Option<&CyclicModuleRecord> {
    match self.get(id) {
      ModuleRecord::Cyclic(m) => Some(m),
      _ => None,
    }
  }

  pub fn get_cyclic_mut(&mut self, id: ModuleId) -> Option<&mut CyclicModuleRecord> {
    match self.get_mut(id) {
      ModuleRecord::Cyclic(m) => Some(m),
      _ => None,
    }
  }
}

/// Opaque host-defined value carried through `LoadRequestedModules(hostDefined)` into
/// `HostLoadImportedModule`.
#[derive(Clone, Default)]
pub struct HostDefined(Option<Arc<dyn Any + Send + Sync>>);

impl HostDefined {
  pub fn new<T: Any + Send + Sync>(data: T) -> Self {
    Self(Some(Arc::new(data)))
  }

  pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
    self.0.as_ref()?.downcast_ref::<T>()
  }
}

impl fmt::Debug for HostDefined {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match &self.0 {
      Some(v) => f
        .debug_struct("HostDefined")
        .field("type_id", &v.type_id())
        .finish(),
      None => f.debug_struct("HostDefined").field("value", &"undefined").finish(),
    }
  }
}

/// Host hook used by module graph loading to asynchronously resolve/load module requests.
///
/// This corresponds to ECMA-262's `HostLoadImportedModule` host hook.
pub trait ModuleLoaderHost {
  fn host_load_imported_module(
    &mut self,
    modules: &mut ModuleStore,
    referrer: ModuleId,
    request: ModuleRequest,
    host_defined: HostDefined,
    payload: ModuleLoadPayload,
  );
}

/// Internal "promise" handle used by the module loader until `%Promise%` lands in this crate.
#[derive(Clone)]
pub struct ModuleGraphLoadPromise(Rc<RefCell<ModuleGraphLoadPromiseState>>);

impl fmt::Debug for ModuleGraphLoadPromise {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("ModuleGraphLoadPromise")
      .field(&*self.0.borrow())
      .finish()
  }
}

#[derive(Clone, Debug)]
pub enum ModuleGraphLoadPromiseState {
  Pending,
  Fulfilled,
  Rejected(VmError),
}

impl PartialEq for ModuleGraphLoadPromiseState {
  fn eq(&self, other: &Self) -> bool {
    match (self, other) {
      (ModuleGraphLoadPromiseState::Pending, ModuleGraphLoadPromiseState::Pending) => true,
      (ModuleGraphLoadPromiseState::Fulfilled, ModuleGraphLoadPromiseState::Fulfilled) => true,
      (ModuleGraphLoadPromiseState::Rejected(_), ModuleGraphLoadPromiseState::Rejected(_)) => true,
      _ => false,
    }
  }
}

impl Eq for ModuleGraphLoadPromiseState {}

impl ModuleGraphLoadPromise {
  fn pending() -> Self {
    Self(Rc::new(RefCell::new(ModuleGraphLoadPromiseState::Pending)))
  }

  pub fn state(&self) -> ModuleGraphLoadPromiseState {
    self.0.borrow().clone()
  }

  fn resolve(&self) {
    let mut state = self.0.borrow_mut();
    if !matches!(*state, ModuleGraphLoadPromiseState::Pending) {
      return;
    }
    *state = ModuleGraphLoadPromiseState::Fulfilled;
  }

  fn reject(&self, err: VmError) {
    let mut state = self.0.borrow_mut();
    if !matches!(*state, ModuleGraphLoadPromiseState::Pending) {
      return;
    }
    *state = ModuleGraphLoadPromiseState::Rejected(err);
  }
}

#[derive(Debug)]
struct GraphLoadingStateInner {
  promise: ModuleGraphLoadPromise,
  is_loading: bool,
  pending_modules_count: usize,
  visited: Vec<ModuleId>,
  host_defined: HostDefined,
}

/// The ECMA-262 `GraphLoadingState` record.
///
/// This is a cloneable handle so the payload passed to `HostLoadImportedModule` can keep the state
/// machine alive across asynchronous completion.
#[derive(Clone, Debug)]
pub struct GraphLoadingState(Rc<RefCell<GraphLoadingStateInner>>);

impl GraphLoadingState {
  fn new(host_defined: HostDefined) -> Self {
    let promise = ModuleGraphLoadPromise::pending();
    Self(Rc::new(RefCell::new(GraphLoadingStateInner {
      promise,
      is_loading: true,
      pending_modules_count: 1,
      visited: Vec::new(),
      host_defined,
    })))
  }

  fn promise(&self) -> ModuleGraphLoadPromise {
    self.0.borrow().promise.clone()
  }

  fn is_loading(&self) -> bool {
    self.0.borrow().is_loading
  }

  fn set_is_loading(&self, value: bool) {
    self.0.borrow_mut().is_loading = value;
  }

  fn host_defined(&self) -> HostDefined {
    self.0.borrow().host_defined.clone()
  }

  fn visited_contains(&self, module: ModuleId) -> bool {
    self.0.borrow().visited.contains(&module)
  }

  fn push_visited(&self, module: ModuleId) {
    self.0.borrow_mut().visited.push(module);
  }

  fn visited_snapshot(&self) -> Vec<ModuleId> {
    self.0.borrow().visited.clone()
  }

  fn inc_pending(&self, delta: usize) {
    self.0.borrow_mut().pending_modules_count += delta;
  }

  fn dec_pending(&self) -> usize {
    let mut state = self.0.borrow_mut();
    debug_assert!(state.pending_modules_count > 0, "pendingModulesCount underflow");
    state.pending_modules_count = state.pending_modules_count.saturating_sub(1);
    state.pending_modules_count
  }

  fn resolve_promise(&self) {
    self.promise().resolve();
  }

  fn reject_promise(&self, err: VmError) {
    self.promise().reject(err);
  }
}

/// Opaque payload passed to `HostLoadImportedModule`.
///
/// Hosts must treat this as an opaque token and later pass it back to
/// [`finish_loading_imported_module`].
#[derive(Clone, Debug)]
pub struct ModuleLoadPayload {
  state: GraphLoadingState,
}

impl ModuleLoadPayload {
  fn new(state: GraphLoadingState) -> Self {
    Self { state }
  }
}

/// Completion record returned by the module-loading host hook.
pub type ModuleCompletion = Result<ModuleId, VmError>;

/// Implements ECMA-262 `LoadRequestedModules(hostDefined?)` for cyclic modules.
pub fn load_requested_modules(
  modules: &mut ModuleStore,
  host: &mut dyn ModuleLoaderHost,
  module: ModuleId,
  host_defined: HostDefined,
) -> ModuleGraphLoadPromise {
  let state = GraphLoadingState::new(host_defined);
  let promise = state.promise();
  inner_module_loading(modules, host, &state, module);
  promise
}

/// Implements ECMA-262 `InnerModuleLoading(state, module)`.
pub fn inner_module_loading(
  modules: &mut ModuleStore,
  host: &mut dyn ModuleLoaderHost,
  state: &GraphLoadingState,
  module: ModuleId,
) {
  let (should_traverse, requested_modules) = match modules.get(module) {
    ModuleRecord::Cyclic(m) => {
      let should_traverse =
        m.status == ModuleStatus::New && !state.visited_contains(module);
      let requested = if should_traverse {
        m.requested_modules.clone()
      } else {
        Vec::new()
      };
      (should_traverse, requested)
    }
    ModuleRecord::NonCyclic => (false, Vec::new()),
  };

  if should_traverse {
    state.push_visited(module);
    state.inc_pending(requested_modules.len());

    for request in requested_modules {
      if !all_import_attributes_supported(&request) {
        continue_module_loading(
          modules,
          host,
          ModuleLoadPayload::new(state.clone()),
          Err(VmError::Unimplemented("AllImportAttributesSupported")),
        );
      } else {
        let already_loaded = modules
          .get_cyclic(module)
          .and_then(|m| m.loaded_module_for_request(&request));

        if let Some(loaded_module) = already_loaded {
          inner_module_loading(modules, host, state, loaded_module);
        } else {
          host.host_load_imported_module(
            modules,
            module,
            request,
            state.host_defined(),
            ModuleLoadPayload::new(state.clone()),
          );
        }
      }

      if !state.is_loading() {
        return;
      }
    }
  }

  let pending_left = state.dec_pending();
  if pending_left != 0 {
    return;
  }

  state.set_is_loading(false);
  for visited in state.visited_snapshot() {
    if let Some(module) = modules.get_cyclic_mut(visited) {
      if module.status == ModuleStatus::New {
        module.status = ModuleStatus::Unlinked;
      }
    }
  }
  state.resolve_promise();
}

/// Implements ECMA-262 `ContinueModuleLoading(state, moduleCompletion)`.
pub fn continue_module_loading(
  modules: &mut ModuleStore,
  host: &mut dyn ModuleLoaderHost,
  payload: ModuleLoadPayload,
  module_completion: ModuleCompletion,
) {
  let state = payload.state;
  if !state.is_loading() {
    return;
  }

  match module_completion {
    Ok(module) => inner_module_loading(modules, host, &state, module),
    Err(err) => {
      state.set_is_loading(false);
      state.reject_promise(err);
    }
  }
}

/// Helper implementing ECMA-262 `FinishLoadingImportedModule(...)`.
///
/// Hosts must call this exactly once for each `HostLoadImportedModule` invocation, either
/// synchronously (re-entrantly) or asynchronously later.
pub fn finish_loading_imported_module(
  modules: &mut ModuleStore,
  host: &mut dyn ModuleLoaderHost,
  referrer: ModuleId,
  request: ModuleRequest,
  payload: ModuleLoadPayload,
  result: ModuleCompletion,
) {
  if let Ok(loaded) = result {
    if let Some(module) = modules.get_cyclic_mut(referrer) {
      module.set_loaded_module(request, loaded);
    }
    continue_module_loading(modules, host, payload, Ok(loaded));
  } else {
    continue_module_loading(modules, host, payload, result);
  }
}

fn module_requests_equal(a: &ModuleRequest, b: &ModuleRequest) -> bool {
  a.specifier == b.specifier && a.import_attributes == b.import_attributes
}

fn all_import_attributes_supported(request: &ModuleRequest) -> bool {
  request.import_attributes.is_empty()
}
