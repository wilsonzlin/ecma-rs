//! ECMAScript module loading host hooks and record types.
//!
//! This module defines a **spec-shaped**, evaluator-independent API surface for integrating the VM
//! with a host environment's module loader (e.g. HTML's event loop + network fetch).
//!
//! ## Spec references
//!
//! - [`EvaluateImportCall`](https://tc39.es/ecma262/#sec-evaluate-import-call)
//! - [`ContinueDynamicImport`](https://tc39.es/ecma262/#sec-continuedynamicimport)
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

use crate::property::PropertyKey;
use crate::{GcString, ModuleId, RealmId, Scope, ScriptId, Value, Vm, VmError};
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

/// Opaque token representing the spec's `GraphLoadingState` record.
///
/// This is an engine-owned continuation state used by *static module loading* and passed through
/// the host's `HostLoadImportedModule` hook in the `_payload_` position.
///
/// The host MUST treat this value as opaque and pass it back unchanged in
/// `FinishLoadingImportedModule`.
#[derive(Clone)]
pub struct GraphLoadingState(Arc<dyn Any + Send + Sync>);

impl GraphLoadingState {
  /// Wrap engine-defined state.
  pub fn new<T: Any + Send + Sync>(data: T) -> Self {
    Self(Arc::new(data))
  }

  /// Attempts to downcast the payload by reference.
  pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
    self.0.downcast_ref::<T>()
  }
}

impl fmt::Debug for GraphLoadingState {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("GraphLoadingState")
      .field("type_id", &self.0.type_id())
      .finish()
  }
}

/// Opaque token representing the spec's `PromiseCapability` record.
///
/// This is used as the `_payload_` when starting a dynamic import (`import()`), and is later passed
/// back to `ContinueDynamicImport` via `FinishLoadingImportedModule`.
///
/// Note: `vm-js` does not yet implement user-facing JavaScript Promises. This record exists as an
/// engine-owned continuation token so the dynamic import path can be wired in a spec-shaped way.
#[derive(Clone)]
pub struct PromiseCapability(Arc<dyn Any + Send + Sync>);

impl PromiseCapability {
  /// Wrap engine-defined state.
  pub fn new<T: Any + Send + Sync>(data: T) -> Self {
    Self(Arc::new(data))
  }

  /// Attempts to downcast the payload by reference.
  pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
    self.0.downcast_ref::<T>()
  }
}

impl fmt::Debug for PromiseCapability {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("PromiseCapability")
      .field("type_id", &self.0.type_id())
      .finish()
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
  GraphLoadingState(GraphLoadingState),
  PromiseCapability(PromiseCapability),
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
  pub(crate) fn graph_loading_state(state: GraphLoadingState) -> Self {
    Self(ModuleLoadPayloadInner::GraphLoadingState(state))
  }

  #[inline]
  #[allow(dead_code)]
  pub(crate) fn promise_capability(capability: PromiseCapability) -> Self {
    Self(ModuleLoadPayloadInner::PromiseCapability(capability))
  }
}

/// The completion record passed to `FinishLoadingImportedModule` continuations.
///
/// In the spec this is either:
/// - a normal completion containing a Module Record, or
/// - a throw completion.
///
/// At this scaffolding layer modules are represented as opaque [`ModuleId`] tokens; errors are
/// represented by [`VmError`].
pub type ModuleCompletion = Result<ModuleId, VmError>;

/// Errors produced while validating dynamic import options / import attributes.
#[derive(Debug, Clone)]
pub enum ImportCallError {
  /// A spec-mandated TypeError rejection.
  TypeError(ImportCallTypeError),
  /// An abrupt error (e.g. OOM / invalid handle) encountered while inspecting objects.
  Vm(VmError),
}

/// The specific TypeError reason produced by `EvaluateImportCall` option/attribute validation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImportCallTypeError {
  OptionsNotObject,
  AttributesNotObject,
  AttributeValueNotString,
  UnsupportedImportAttribute { key: Arc<str> },
}

fn clone_heap_string_to_arc_str(heap: &crate::Heap, s: GcString) -> Result<Arc<str>, VmError> {
  Ok(Arc::<str>::from(heap.get_string(s)?.to_utf8_lossy()))
}

fn make_key_string(scope: &mut Scope<'_>, s: &str) -> Result<GcString, VmError> {
  // Root the key string for the duration of the algorithm so it can't be collected if a later
  // allocation triggers GC.
  let key = scope.alloc_string(s)?;
  scope.push_root(Value::String(key));
  Ok(key)
}

/// Extract and validate import attributes from the `options` argument of a dynamic `import()` call.
///
/// This implements the import-attributes portion of `EvaluateImportCall`:
/// <https://tc39.es/ecma262/#sec-evaluate-import-call>
pub fn import_attributes_from_options(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  options: Value,
  supported_keys: &[&str],
) -> Result<Vec<ImportAttribute>, ImportCallError> {
  if matches!(options, Value::Undefined) {
    return Ok(Vec::new());
  }

  let Value::Object(options_obj) = options else {
    return Err(ImportCallError::TypeError(ImportCallTypeError::OptionsNotObject));
  };

  let with_key = PropertyKey::from_string(make_key_string(scope, "with").map_err(ImportCallError::Vm)?);
  let attributes_obj = scope
    .ordinary_get(vm, options_obj, with_key, Value::Object(options_obj))
    .map_err(ImportCallError::Vm)?;

  if matches!(attributes_obj, Value::Undefined) {
    return Ok(Vec::new());
  }

  let Value::Object(attributes_obj) = attributes_obj else {
    return Err(ImportCallError::TypeError(
      ImportCallTypeError::AttributesNotObject,
    ));
  };

  let own_keys = scope
    .ordinary_own_property_keys(attributes_obj)
    .map_err(ImportCallError::Vm)?;

  let mut attributes = Vec::<ImportAttribute>::new();

  for key in own_keys {
    let PropertyKey::String(key_string) = key else {
      continue;
    };

    let Some(desc) = scope
      .heap()
      .object_get_own_property(attributes_obj, &key)
      .map_err(ImportCallError::Vm)?
    else {
      continue;
    };

    if !desc.enumerable {
      continue;
    }

    let value = scope
      .ordinary_get(vm, attributes_obj, key, Value::Object(attributes_obj))
      .map_err(ImportCallError::Vm)?;

    let Value::String(value_string) = value else {
      return Err(ImportCallError::TypeError(
        ImportCallTypeError::AttributeValueNotString,
      ));
    };

    let key = clone_heap_string_to_arc_str(scope.heap(), key_string).map_err(ImportCallError::Vm)?;
    let value =
      clone_heap_string_to_arc_str(scope.heap(), value_string).map_err(ImportCallError::Vm)?;

    attributes.push(ImportAttribute { key, value });
  }

  // `AllImportAttributesSupported`.
  for attribute in &attributes {
    if !supported_keys
      .iter()
      .any(|supported| *supported == attribute.key.as_ref())
    {
      return Err(ImportCallError::TypeError(
        ImportCallTypeError::UnsupportedImportAttribute {
          key: attribute.key.clone(),
        },
      ));
    }
  }

  // Sort by key.
  attributes.sort_by(|a, b| a.key.cmp(&b.key));
  Ok(attributes)
}

/// Spec helper: `AllImportAttributesSupported(attributes)`.
pub fn all_import_attributes_supported(
  supported_keys: &[&str],
  attributes: &[ImportAttribute],
) -> bool {
  attributes
    .iter()
    .all(|attr| supported_keys.iter().any(|k| *k == attr.key.as_ref()))
}

/// Spec-shaped dynamic import entry point (EvaluateImportCall).
///
/// This function currently returns [`VmError::Unimplemented`] because `vm-js` does not yet provide
/// a user-facing JavaScript Promise implementation or a full module evaluator.
#[allow(unused_variables)]
pub fn start_dynamic_import(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn crate::VmHostHooks,
  ctx: &mut dyn VmModuleLoadingContext,
  specifier: Value,
  options: Value,
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("dynamic import"))
}

/// Spec helper: `FinishLoadingImportedModule(referrer, moduleRequest, payload, result)`.
///
/// This function dispatches to `ContinueModuleLoading` or `ContinueDynamicImport` based on the
/// payload kind.
pub fn finish_loading_imported_module(
  _referrer: ModuleReferrer,
  _module_request: ModuleRequest,
  payload: ModuleLoadPayload,
  result: ModuleCompletion,
) -> Result<(), VmError> {
  match payload.0 {
    ModuleLoadPayloadInner::GraphLoadingState(state) => continue_module_loading(state, result),
    ModuleLoadPayloadInner::PromiseCapability(promise_capability) => {
      continue_dynamic_import(promise_capability, result)
    }
  }
}

/// Placeholder for the static-module loading continuation (`ContinueModuleLoading`).
pub fn continue_module_loading(_state: GraphLoadingState, _result: ModuleCompletion) -> Result<(), VmError> {
  Err(VmError::Unimplemented("ContinueModuleLoading"))
}

/// Placeholder for the dynamic import continuation (`ContinueDynamicImport`).
pub fn continue_dynamic_import(
  _promise_capability: PromiseCapability,
  _module_completion: ModuleCompletion,
) -> Result<(), VmError> {
  Err(VmError::Unimplemented("ContinueDynamicImport"))
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

#[cfg(test)]
mod tests {
  use super::*;
  use crate::property::PropertyDescriptor;
  use crate::property::PropertyKey as HeapPropertyKey;
  use crate::property::PropertyKind as HeapPropertyKind;
  use crate::Heap;
  use crate::HeapLimits;
  use crate::VmOptions;

  fn data_desc(value: Value, enumerable: bool) -> PropertyDescriptor {
    PropertyDescriptor {
      enumerable,
      configurable: true,
      kind: HeapPropertyKind::Data {
        value,
        writable: true,
      },
    }
  }

  #[test]
  fn import_attributes_from_options_validates_and_sorts() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());

    let options = scope.alloc_object().unwrap();
    let attributes = scope.alloc_object().unwrap();

    let k_with = scope.alloc_string("with").unwrap();
    let k_type = scope.alloc_string("type").unwrap();
    let v_json = scope.alloc_string("json").unwrap();
    let k_a = scope.alloc_string("a").unwrap();
    let v_b = scope.alloc_string("b").unwrap();
    let k_ignored = scope.alloc_string("ignored").unwrap();
    let v_x = scope.alloc_string("x").unwrap();

    scope
      .define_property(
        attributes,
        HeapPropertyKey::String(k_type),
        data_desc(Value::String(v_json), true),
      )
      .unwrap();
    scope
      .define_property(
        attributes,
        HeapPropertyKey::String(k_a),
        data_desc(Value::String(v_b), true),
      )
      .unwrap();
    scope
      .define_property(
        attributes,
        HeapPropertyKey::String(k_ignored),
        data_desc(Value::String(v_x), false),
      )
      .unwrap();

    scope
      .define_property(
        options,
        HeapPropertyKey::String(k_with),
        data_desc(Value::Object(attributes), true),
      )
      .unwrap();

    let supported = ["a", "type"];
    let attrs =
      import_attributes_from_options(&mut vm, &mut scope, Value::Object(options), &supported)
        .unwrap();

    let keys: Vec<&str> = attrs.iter().map(|a| a.key.as_ref()).collect();
    assert_eq!(keys, vec!["a", "type"]);
  }

  #[test]
  fn import_attributes_from_options_rejects_invalid_types() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());

    let supported = ["type"];
    let err =
      import_attributes_from_options(&mut vm, &mut scope, Value::Number(1.0), &supported).unwrap_err();
    assert!(matches!(
      err,
      ImportCallError::TypeError(ImportCallTypeError::OptionsNotObject)
    ));

    let options = scope.alloc_object().unwrap();
    let k_with = scope.alloc_string("with").unwrap();
    scope
      .define_property(
        options,
        HeapPropertyKey::String(k_with),
        data_desc(Value::Number(1.0), true),
      )
      .unwrap();

    let err =
      import_attributes_from_options(&mut vm, &mut scope, Value::Object(options), &supported).unwrap_err();
    assert!(matches!(
      err,
      ImportCallError::TypeError(ImportCallTypeError::AttributesNotObject)
    ));

    let options2 = scope.alloc_object().unwrap();
    let attrs_obj = scope.alloc_object().unwrap();
    let k_with2 = scope.alloc_string("with").unwrap();
    let k_type = scope.alloc_string("type").unwrap();
    scope
      .define_property(
        attrs_obj,
        HeapPropertyKey::String(k_type),
        data_desc(Value::Number(1.0), true),
      )
      .unwrap();
    scope
      .define_property(
        options2,
        HeapPropertyKey::String(k_with2),
        data_desc(Value::Object(attrs_obj), true),
      )
      .unwrap();

    let err =
      import_attributes_from_options(&mut vm, &mut scope, Value::Object(options2), &supported).unwrap_err();
    assert!(matches!(
      err,
      ImportCallError::TypeError(ImportCallTypeError::AttributeValueNotString)
    ));
  }

  #[test]
  fn finish_loading_imported_module_dispatches_by_payload_kind() {
    let referrer = ModuleReferrer::Realm(RealmId::from_raw(1));
    let request = ModuleRequest::new("./x.mjs", vec![]);
    let ok = Ok(ModuleId::from_raw(1));

    let err = finish_loading_imported_module(
      referrer,
      request.clone(),
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      ok,
    )
    .unwrap_err();
    assert!(matches!(err, VmError::Unimplemented("ContinueModuleLoading")));

    let err = finish_loading_imported_module(
      referrer,
      request,
      ModuleLoadPayload::promise_capability(PromiseCapability::new(())),
      Ok(ModuleId::from_raw(1)),
    )
    .unwrap_err();
    assert!(matches!(err, VmError::Unimplemented("ContinueDynamicImport")));
  }
}
