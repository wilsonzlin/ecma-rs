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
use crate::{
  GcObject, GcString, ImportAttribute, LoadedModuleRequest, ModuleId, ModuleRequest, RealmId,
  RootId, Scope, ScriptId, ScriptOrModule, Value, Vm, VmError,
};
use std::any::Any;
use std::fmt;
use std::sync::{Arc, Mutex};

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

/// Minimal access to an ECMA-262 `[[LoadedModules]]` list.
///
/// In the specification, Script Records, Cyclic Module Records, and Realm Records each have a
/// `[[LoadedModules]]` internal slot used by `FinishLoadingImportedModule` to memoize the result of
/// loading a `(specifier, attributes)` module request.
///
/// This trait exists so `FinishLoadingImportedModule` can be implemented in a reusable, spec-shaped
/// way without committing to concrete Script/Module/Realm record representations yet.
pub trait LoadedModulesOwner {
  fn loaded_modules(&self) -> &[LoadedModuleRequest<ModuleId>];
  fn loaded_modules_mut(&mut self) -> &mut Vec<LoadedModuleRequest<ModuleId>>;
}

impl LoadedModulesOwner for Vec<LoadedModuleRequest<ModuleId>> {
  #[inline]
  fn loaded_modules(&self) -> &[LoadedModuleRequest<ModuleId>] {
    self.as_slice()
  }

  #[inline]
  fn loaded_modules_mut(&mut self) -> &mut Vec<LoadedModuleRequest<ModuleId>> {
    self
  }
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
/// Note: `vm-js` models Promise objects and Promise jobs, but module evaluation is not yet
/// integrated. This record keeps the Promise object alive across asynchronous boundaries so host
/// module loading can later resolve/reject it.
#[derive(Clone)]
pub struct PromiseCapability(Arc<Mutex<PromiseCapabilityInner>>);

#[derive(Debug)]
struct PromiseCapabilityInner {
  promise: GcObject,
  /// Persistent root keeping `promise` alive until the capability is settled.
  root: Option<RootId>,
}

impl PromiseCapability {
  /// Create a new pending PromiseCapability.
  ///
  /// This allocates a Promise object and roots it in the heap's persistent root set so the returned
  /// capability can be held by the host across asynchronous module loading.
  pub fn new(vm: &mut Vm, scope: &mut Scope<'_>) -> Result<Self, VmError> {
    // When intrinsics are present, use the realm's `%Promise.prototype%` so the returned object is
    // `instanceof Promise` from JS. Tests sometimes call this helper without initializing a realm;
    // fall back to an unprototyped Promise object in that case.
    let promise = match vm.intrinsics() {
      Some(intr) => scope.alloc_promise_with_prototype(Some(intr.promise_prototype()))?,
      None => scope.alloc_promise()?,
    };

    // Root the promise while inserting it into the persistent root set (which can allocate and
    // trigger GC). Use a child scope so the temporary stack root does not escape.
    let mut root_scope = scope.reborrow();
    root_scope.push_root(Value::Object(promise))?;
    let root = root_scope.heap_mut().add_root(Value::Object(promise))?;
    Ok(Self(Arc::new(Mutex::new(PromiseCapabilityInner {
      promise,
      root: Some(root),
    }))))
  }

  /// Returns the underlying Promise object.
  pub fn promise(&self) -> GcObject {
    self.0.lock().expect("poisoned PromiseCapability").promise
  }

  /// Fulfill this capability's promise with `value` (idempotent).
  pub fn fulfill(&self, vm: &mut Vm, scope: &mut Scope<'_>, value: Value) -> Result<(), VmError> {
    let mut inner = self.0.lock().expect("poisoned PromiseCapability");
    if inner.root.is_none() {
      return Ok(());
    }
    let promise = inner.promise;
    crate::builtins::fulfill_promise(vm.microtask_queue_mut(), scope, promise, value)?;
    let root = inner
      .root
      .take()
      .expect("PromiseCapability root should be present when unsettled");
    scope.heap_mut().remove_root(root);
    Ok(())
  }

  /// Reject this capability's promise with `reason` (idempotent).
  pub fn reject(&self, vm: &mut Vm, scope: &mut Scope<'_>, reason: Value) -> Result<(), VmError> {
    let mut inner = self.0.lock().expect("poisoned PromiseCapability");
    if inner.root.is_none() {
      return Ok(());
    }
    let promise = inner.promise;
    crate::builtins::reject_promise(vm.microtask_queue_mut(), scope, promise, reason)?;
    let root = inner
      .root
      .take()
      .expect("PromiseCapability root should be present when unsettled");
    scope.heap_mut().remove_root(root);
    Ok(())
  }
}

impl fmt::Debug for PromiseCapability {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // Treat the promise capability as opaque to the host.
    let _ = &self.0;
    f.write_str("PromiseCapability(..)")
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
  UnsupportedImportAttribute { key: String },
}

fn clone_heap_string_to_string(heap: &crate::Heap, s: GcString) -> Result<String, VmError> {
  Ok(heap.get_string(s)?.to_utf8_lossy())
}

fn make_key_string(scope: &mut Scope<'_>, s: &str) -> Result<GcString, VmError> {
  // Root the key string for the duration of the algorithm so it can't be collected if a later
  // allocation triggers GC.
  let key = scope.alloc_string(s)?;
  scope.push_root(Value::String(key))?;
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

    let key = clone_heap_string_to_string(scope.heap(), key_string).map_err(ImportCallError::Vm)?;
    let value =
      clone_heap_string_to_string(scope.heap(), value_string).map_err(ImportCallError::Vm)?;

    attributes.push(ImportAttribute { key, value });
  }

  // `AllImportAttributesSupported`.
  for attribute in &attributes {
    if !supported_keys
      .iter()
      .any(|supported| *supported == attribute.key.as_str())
    {
      return Err(ImportCallError::TypeError(
        ImportCallTypeError::UnsupportedImportAttribute {
          key: attribute.key.clone(),
        },
      ));
    }
  }

  // Sort by key (and value for determinism) by UTF-16 code unit order.
  attributes.sort_by(|a, b| match crate::cmp_utf16(&a.key, &b.key) {
    std::cmp::Ordering::Equal => crate::cmp_utf16(&a.value, &b.value),
    non_eq => non_eq,
  });
  Ok(attributes)
}

/// Spec helper: `AllImportAttributesSupported(attributes)`.
pub fn all_import_attributes_supported(
  supported_keys: &[&str],
  attributes: &[ImportAttribute],
) -> bool {
  attributes
    .iter()
    .all(|attr| supported_keys.iter().any(|k| *k == attr.key.as_str()))
}

fn vm_error_to_rejection_reason(
  scope: &mut Scope<'_>,
  err: VmError,
) -> Result<(Value, Option<VmError>), VmError> {
  match err {
    VmError::Throw(v) => Ok((v, None)),
    // Represent non-throw VM errors as a string reason so dynamic import remains evaluator-
    // independent while Error object construction is still evolving.
    other => {
      let msg = other.to_string();
      let s = scope.alloc_string(&msg)?;
      Ok((Value::String(s), Some(other)))
    }
  }
}

fn import_call_type_error_message(err: &ImportCallTypeError) -> String {
  match err {
    ImportCallTypeError::OptionsNotObject => "TypeError: import() options must be an object".to_string(),
    ImportCallTypeError::AttributesNotObject => {
      "TypeError: import() options.with must be an object".to_string()
    }
    ImportCallTypeError::AttributeValueNotString => {
      "TypeError: import() attribute values must be strings".to_string()
    }
    ImportCallTypeError::UnsupportedImportAttribute { key } => {
      format!("TypeError: unsupported import attribute key: {key}")
    }
  }
}

/// Spec-shaped dynamic import entry point (EvaluateImportCall).
///
/// This implements the *host integration* and option validation parts of ECMA-262's
/// `EvaluateImportCall`:
/// <https://tc39.es/ecma262/#sec-evaluate-import-call>.
///
/// `vm-js` does not yet implement full module evaluation, but this function still:
/// - returns a Promise object,
/// - validates import attributes, and
/// - calls the host's `HostLoadImportedModule` hook with `payload = PromiseCapability`.
pub fn start_dynamic_import(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn crate::VmHostHooks,
  ctx: &mut dyn VmModuleLoadingContext,
  specifier: Value,
  options: Value,
) -> Result<Value, VmError> {
  let promise_capability = PromiseCapability::new(vm, scope)?;
  let promise_obj = promise_capability.promise();

  // 1. `specifierString = ToString(specifier)`
  let specifier_string = match scope.heap_mut().to_string(specifier) {
    Ok(s) => s,
    Err(err) => {
      let (reason, _) = vm_error_to_rejection_reason(scope, err)?;
      promise_capability.reject(vm, scope, reason)?;
      return Ok(Value::Object(promise_obj));
    }
  };
  let specifier = clone_heap_string_to_string(scope.heap(), specifier_string)?;

  // 2. Determine `referrer = GetActiveScriptOrModule(); if null, use current Realm Record`.
  let referrer = match vm.get_active_script_or_module() {
    Some(ScriptOrModule::Script(id)) => ModuleReferrer::Script(id),
    Some(ScriptOrModule::Module(id)) => ModuleReferrer::Module(id),
    None => match vm.current_realm() {
      Some(realm) => ModuleReferrer::Realm(realm),
      None => {
        let s = scope.alloc_string("unimplemented: dynamic import requires a current realm")?;
        promise_capability.reject(vm, scope, Value::String(s))?;
        return Ok(Value::Object(promise_obj));
      }
    },
  };

  // 3. Parse/validate import attributes.
  let supported_keys = host.host_get_supported_import_attributes();
  let attributes = match import_attributes_from_options(vm, scope, options, supported_keys) {
    Ok(attrs) => attrs,
    Err(ImportCallError::TypeError(type_err)) => {
      let msg = import_call_type_error_message(&type_err);
      let s = scope.alloc_string(&msg)?;
      promise_capability.reject(vm, scope, Value::String(s))?;
      return Ok(Value::Object(promise_obj));
    }
    Err(ImportCallError::Vm(err)) => {
      let (reason, _) = vm_error_to_rejection_reason(scope, err)?;
      promise_capability.reject(vm, scope, reason)?;
      return Ok(Value::Object(promise_obj));
    }
  };

  // 4. HostLoadImportedModule(referrer, moduleRequest, empty, payload = promiseCapability).
  let module_request = ModuleRequest::new(specifier, attributes);
  host.host_load_imported_module(
    ctx,
    referrer,
    module_request,
    HostDefined::new(()),
    ModuleLoadPayload::promise_capability(promise_capability),
  );

  Ok(Value::Object(promise_obj))
}

/// Spec helper: `FinishLoadingImportedModule(referrer, moduleRequest, payload, result)`.
///
/// This helper implements the core spec semantics:
/// - On a normal completion, update `referrer.[[LoadedModules]]`:
///   - If a `ModuleRequestsEqual` match already exists, error if it resolves to a different module.
///   - Otherwise append a new `LoadedModuleRequest`.
/// - Dispatch to `ContinueModuleLoading` or `ContinueDynamicImport` based on payload kind.
pub fn finish_loading_imported_module(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  referrer: &mut impl LoadedModulesOwner,
  module_request: ModuleRequest,
  payload: ModuleLoadPayload,
  result: ModuleCompletion,
) -> Result<(), VmError> {
  // FinishLoadingImportedModule (ECMA-262):
  // If this completion was normal, cache the resolved module into `[[LoadedModules]]` and enforce
  // the spec invariant that a duplicate request must resolve to the same module record.
  if let Ok(module) = &result {
    if let Some(existing) = referrer
      .loaded_modules()
      .iter()
      .find(|record| record.request.spec_equal(&module_request))
    {
      if existing.module != *module {
        return Err(VmError::InvariantViolation(
          "FinishLoadingImportedModule invariant violation: module request resolved to different modules",
        ));
      }
    } else {
      let list = referrer.loaded_modules_mut();
      list.try_reserve(1).map_err(|_| VmError::OutOfMemory)?;
      list.push(LoadedModuleRequest::new(module_request, *module));
    }
  }

  match payload.0 {
    ModuleLoadPayloadInner::GraphLoadingState(state) => continue_module_loading(vm, scope, state, result),
    ModuleLoadPayloadInner::PromiseCapability(promise_capability) => {
      continue_dynamic_import(vm, scope, promise_capability, result)
    }
  }
}

/// Placeholder for the static-module loading continuation (`ContinueModuleLoading`).
pub fn continue_module_loading(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _state: GraphLoadingState,
  _result: ModuleCompletion,
) -> Result<(), VmError> {
  Err(VmError::Unimplemented("ContinueModuleLoading"))
}

/// Dynamic import continuation (`ContinueDynamicImport`).
///
/// This currently implements only the rejection path because module evaluation is not yet
/// integrated into `vm-js`.
pub fn continue_dynamic_import(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  promise_capability: PromiseCapability,
  module_completion: ModuleCompletion,
) -> Result<(), VmError> {
  match module_completion {
    Err(err) => {
      let (reason, _) = vm_error_to_rejection_reason(scope, err)?;
      promise_capability.reject(vm, scope, reason)?;
      Ok(())
    }
    Ok(_module) => {
      let s = scope.alloc_string("unimplemented: ContinueDynamicImport (module evaluation)")?;
      promise_capability.reject(vm, scope, Value::String(s))?;
      Ok(())
    }
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

    let keys: Vec<&str> = attrs.iter().map(|a| a.key.as_str()).collect();
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
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());
    let request = ModuleRequest::new("./x.mjs", vec![]);
    let ok = Ok(ModuleId::from_raw(1));

    let mut loaded_modules = Vec::<LoadedModuleRequest<ModuleId>>::new();
    let err = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request.clone(),
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      ok,
    )
    .unwrap_err();
    assert!(matches!(err, VmError::Unimplemented("ContinueModuleLoading")));

    let promise_capability = PromiseCapability::new(&mut vm, &mut scope).unwrap();
    let promise = promise_capability.promise();

    finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request,
      ModuleLoadPayload::promise_capability(promise_capability),
      Ok(ModuleId::from_raw(1)),
    )
    .unwrap();

    assert_eq!(
      scope.heap().promise_state(promise).unwrap(),
      crate::PromiseState::Rejected
    );
  }

  #[test]
  fn finish_loading_imported_module_appends_loaded_modules_on_success() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());
    let mut loaded_modules = Vec::<LoadedModuleRequest<ModuleId>>::new();
    let request = ModuleRequest::new("./x.mjs", vec![ImportAttribute::new("type", "json")]);
    let module = ModuleId::from_raw(123);

    let err = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request.clone(),
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      Ok(module),
    )
    .unwrap_err();
    assert!(matches!(err, VmError::Unimplemented("ContinueModuleLoading")));

    assert_eq!(loaded_modules.len(), 1);
    assert_eq!(loaded_modules[0].request.specifier.as_str(), "./x.mjs");
    assert_eq!(loaded_modules[0].request.attributes, request.attributes);
    assert_eq!(loaded_modules[0].module, module);
  }

  #[test]
  fn finish_loading_imported_module_does_not_append_on_failure() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());
    let mut loaded_modules = Vec::<LoadedModuleRequest<ModuleId>>::new();
    let request = ModuleRequest::new("./x.mjs", vec![]);

    let err = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request,
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      Err(VmError::Unimplemented("load failure")),
    )
    .unwrap_err();
    assert!(matches!(err, VmError::Unimplemented("ContinueModuleLoading")));
    assert!(loaded_modules.is_empty());
  }

  #[test]
  fn finish_loading_imported_module_does_not_duplicate_on_same_module() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());
    let mut loaded_modules = Vec::<LoadedModuleRequest<ModuleId>>::new();
    let request = ModuleRequest::new("./x.mjs", vec![]);
    let module = ModuleId::from_raw(1);

    let _ = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request.clone(),
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      Ok(module),
    );
    let _ = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request.clone(),
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      Ok(module),
    );
    assert_eq!(loaded_modules.len(), 1);
    assert_eq!(loaded_modules[0].module, module);
  }

  #[test]
  fn finish_loading_imported_module_errors_on_duplicate_mismatch() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();
    let mut vm = Vm::new(VmOptions::default());
    let mut loaded_modules = Vec::<LoadedModuleRequest<ModuleId>>::new();
    let request = ModuleRequest::new("./x.mjs", vec![]);
    let module_a = ModuleId::from_raw(1);
    let module_b = ModuleId::from_raw(2);

    let _ = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request.clone(),
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      Ok(module_a),
    );

    let err = finish_loading_imported_module(
      &mut vm,
      &mut scope,
      &mut loaded_modules,
      request,
      ModuleLoadPayload::graph_loading_state(GraphLoadingState::new(())),
      Ok(module_b),
    )
    .unwrap_err();
    assert!(matches!(err, VmError::InvariantViolation(_)));
    assert_eq!(loaded_modules.len(), 1);
    assert_eq!(loaded_modules[0].module, module_a);
  }
}
