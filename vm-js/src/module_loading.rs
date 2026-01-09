//! ECMAScript module loading host hooks and record types.
//!
//! This module defines a **spec-shaped**, evaluator-independent API surface for integrating the VM
//! with a host environment's module loader (e.g. HTML's event loop + network fetch).
//!
//! ## Spec references
//!
//! - [`HostLoadImportedModule`](https://tc39.es/ecma262/#sec-hostloadimportedmodule)
//! - [`FinishLoadingImportedModule`](https://tc39.es/ecma262/#sec-finishloadingimportedmodule)
//! - [`ModuleRequestsEqual`](https://tc39.es/ecma262/#sec-modulerequestsequal)
//!
//! The goal of this module is to provide the *host hook surface* and spec-shaped record types,
//! **not** to implement full module parsing/linking/evaluation.
//!
//! See also:
//! - [`crate::VmHostHooks::host_load_imported_module`]
//! - [`VmModuleLoadingContext::finish_loading_imported_module`]

use crate::{ModuleId, RealmId, ScriptId, VmError};
use std::any::Any;
use std::fmt;
use std::sync::Arc;

/// An `ImportAttribute` Record (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#importattribute-record>
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ImportAttribute {
  pub key: Arc<str>,
  pub value: Arc<str>,
}

impl ImportAttribute {
  #[inline]
  pub fn new(key: impl Into<Arc<str>>, value: impl Into<Arc<str>>) -> Self {
    Self {
      key: key.into(),
      value: value.into(),
    }
  }
}

/// A `ModuleRequest` Record (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#modulerequest-record>
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct ModuleRequest {
  pub specifier: Arc<str>,
  pub attributes: Vec<ImportAttribute>,
}

impl ModuleRequest {
  #[inline]
  pub fn new(specifier: impl Into<Arc<str>>, attributes: Vec<ImportAttribute>) -> Self {
    Self {
      specifier: specifier.into(),
      attributes,
    }
  }
}

/// The subset of fields shared by `ModuleRequest` and `LoadedModuleRequest`.
///
/// This exists so [`module_requests_equal`] can be implemented in the same shape as the spec
/// (`ModuleRequestsEqual` accepts either record).
pub trait ModuleRequestLike {
  fn specifier(&self) -> &str;
  fn attributes(&self) -> &[ImportAttribute];
}

impl ModuleRequestLike for ModuleRequest {
  #[inline]
  fn specifier(&self) -> &str {
    &self.specifier
  }

  #[inline]
  fn attributes(&self) -> &[ImportAttribute] {
    &self.attributes
  }
}

/// A `LoadedModuleRequest` Record (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#loadedmodulerequest-record>
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LoadedModuleRequest<M> {
  pub specifier: Arc<str>,
  pub attributes: Vec<ImportAttribute>,
  pub module: M,
}

impl<M> LoadedModuleRequest<M> {
  #[inline]
  pub fn new(request: ModuleRequest, module: M) -> Self {
    Self {
      specifier: request.specifier,
      attributes: request.attributes,
      module,
    }
  }
}

impl<M> ModuleRequestLike for LoadedModuleRequest<M> {
  #[inline]
  fn specifier(&self) -> &str {
    &self.specifier
  }

  #[inline]
  fn attributes(&self) -> &[ImportAttribute] {
    &self.attributes
  }
}

/// Implements `ModuleRequestsEqual(left, right)` from ECMA-262.
///
/// Spec: <https://tc39.es/ecma262/#sec-modulerequestsequal>
///
/// Import attributes are compared **order-insensitively**.
pub fn module_requests_equal<L: ModuleRequestLike + ?Sized, R: ModuleRequestLike + ?Sized>(
  left: &L,
  right: &R,
) -> bool {
  if left.specifier() != right.specifier() {
    return false;
  }

  let left_attrs = left.attributes();
  let right_attrs = right.attributes();
  if left_attrs.len() != right_attrs.len() {
    return false;
  }

  for l in left_attrs {
    if !right_attrs
      .iter()
      .any(|r| l.key == r.key && l.value == r.value)
    {
      return false;
    }
  }

  true
}

/// The *identity* of the `referrer` passed to `HostLoadImportedModule`/`FinishLoadingImportedModule`.
///
/// Per ECMA-262, the referrer is a union of:
/// - Script Record
/// - Cyclic Module Record
/// - Realm Record
///
/// This enum is intentionally **identity-only**: it can be stored across asynchronous boundaries
/// without holding `&` references into the engine.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ModuleReferrer {
  Script(ScriptId),
  Module(ModuleId),
  Realm(RealmId),
}

/// Host-defined data passed through `HostLoadImportedModule`.
///
/// In ECMA-262, `_hostDefined_` is typed as "anything" and is carried through spec algorithms.
///
/// This is an opaque record to the VM; the embedding chooses what to store.
#[derive(Clone)]
pub struct HostDefined(Arc<dyn Any + Send + Sync>);

impl HostDefined {
  /// Wrap host-defined data.
  pub fn new<T: Any + Send + Sync>(data: T) -> Self {
    Self(Arc::new(data))
  }

  /// Attempts to downcast the payload by reference.
  pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
    self.0.downcast_ref::<T>()
  }
}

impl fmt::Debug for HostDefined {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("HostDefined").field("type_id", &self.0.type_id()).finish()
  }
}

/// Opaque token passed through `HostLoadImportedModule` into `FinishLoadingImportedModule`.
///
/// In the ECMAScript spec, `_payload_` is either:
/// - a `GraphLoadingState` Record (module graph loading continuation), or
/// - a `PromiseCapability` Record (`import()` continuation).
///
/// The host MUST treat this value as opaque and pass it back unchanged.
///
/// ## Opaqueness (compile-time)
///
/// Hosts can store and clone this value, but cannot inspect or destructure it:
///
/// ```compile_fail
/// use vm_js::ModuleLoadPayload;
///
/// fn inspect(payload: ModuleLoadPayload) {
///   let ModuleLoadPayload(_) = payload;
/// }
/// ```
#[derive(Clone)]
pub struct ModuleLoadPayload(ModuleLoadPayloadInner);

#[derive(Clone)]
#[allow(dead_code)]
enum ModuleLoadPayloadInner {
  GraphLoadingState,
  PromiseCapability,
}

impl fmt::Debug for ModuleLoadPayload {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // Treat the inner discriminant as opaque: hosts should not be able to inspect it via `Debug`.
    let _ = &self.0;
    f.write_str("ModuleLoadPayload(..)")
  }
}

impl ModuleLoadPayload {
  #[inline]
  #[allow(dead_code)]
  pub(crate) fn graph_loading_state() -> Self {
    Self(ModuleLoadPayloadInner::GraphLoadingState)
  }

  #[inline]
  #[allow(dead_code)]
  pub(crate) fn promise_capability() -> Self {
    Self(ModuleLoadPayloadInner::PromiseCapability)
  }
}

/// Minimal engine callback surface needed to implement `FinishLoadingImportedModule`.
///
/// The host calls this once it has finished loading (or failed to load) an imported module.
///
/// Spec: <https://tc39.es/ecma262/#sec-finishloadingimportedmodule>
pub trait VmModuleLoadingContext {
  /// Perform `FinishLoadingImportedModule(referrer, moduleRequest, payload, result)`.
  ///
  /// - On success, `result` is `Ok(module)` where `module` is the loaded Module Record.
  /// - On failure, `result` is `Err(_)` and should typically represent a throw completion
  ///   (`VmError::Throw`), although other engine errors (OOM, termination) may be surfaced too.
  ///
  /// The host may call this synchronously from within
  /// [`crate::VmHostHooks::host_load_imported_module`], which *re-enters* module graph loading.
  fn finish_loading_imported_module(
    &mut self,
    referrer: ModuleReferrer,
    module_request: ModuleRequest,
    payload: ModuleLoadPayload,
    result: Result<ModuleId, VmError>,
  );
}

