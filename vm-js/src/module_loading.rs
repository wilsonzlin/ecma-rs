//! ECMAScript module loading host hooks and dynamic import scaffolding.
//!
//! This module is intentionally **evaluator-independent** (similar to [`crate::jobs`]): it defines
//! small, spec-shaped types that allow an embedding to integrate module loading before a complete
//! ECMAScript evaluator/interpreter exists.
//!
//! ## Spec background
//!
//! - `EvaluateImportCall` / `ContinueDynamicImport` (dynamic `import()`):
//!   <https://tc39.es/ecma262/#sec-evaluate-import-call>
//! - `HostLoadImportedModule` / `FinishLoadingImportedModule` (host module loader hook):
//!   <https://tc39.es/ecma262/#sec-hostloadimportedmodule>
//! - Import attributes (`with: { ... }`):
//!   <https://tc39.es/ecma262/#sec-allimportattributessupported>

use crate::property::PropertyKey;
use crate::{GcString, JsString, RealmId, Scope, Value, Vm, VmError};
use std::any::Any;
use std::fmt;
use std::sync::Arc;

/// Opaque identifier for an ECMAScript Script Record or Module Record.
///
/// This mirrors the spec notion of "active ScriptOrModule" returned by
/// `GetActiveScriptOrModule()`. The host/evaluator may choose what this identifies (e.g. a module
/// graph node id or a settings object id); the VM treats it as an opaque token.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ScriptOrModuleId(u64);

impl ScriptOrModuleId {
  /// Creates a new `ScriptOrModuleId` from an opaque numeric value.
  #[inline]
  pub const fn from_raw(raw: u64) -> Self {
    Self(raw)
  }

  /// Returns the underlying opaque numeric representation.
  #[inline]
  pub const fn to_raw(self) -> u64 {
    self.0
  }
}

impl fmt::Debug for ScriptOrModuleId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("ScriptOrModuleId").field(&self.0).finish()
  }
}

/// The `referrer` argument passed to `HostLoadImportedModule`.
///
/// In ECMA-262 this is a Script Record, Cyclic Module Record, or Realm Record.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ModuleReferrer {
  ScriptOrModule(ScriptOrModuleId),
  Realm(RealmId),
}

/// A spec-shaped ImportAttribute record.
///
/// Both fields are ECMAScript String values. We store them as [`JsString`] so they are independent
/// of GC handles (and preserve UTF-16 code units, including lone surrogates).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ImportAttribute {
  pub key: JsString,
  pub value: JsString,
}

/// A spec-shaped ModuleRequest record.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModuleRequest {
  pub specifier: JsString,
  pub attributes: Vec<ImportAttribute>,
}

/// The payload passed through `HostLoadImportedModule` and later returned to
/// `FinishLoadingImportedModule`.
#[derive(Clone)]
pub enum ModuleLoadPayload {
  GraphLoadingState(GraphLoadingState),
  PromiseCapability(PromiseCapability),
}

impl fmt::Debug for ModuleLoadPayload {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      Self::GraphLoadingState(_) => f.debug_tuple("GraphLoadingState").finish(),
      Self::PromiseCapability(_) => f.debug_tuple("PromiseCapability").finish(),
    }
  }
}

/// Opaque token representing the "GraphLoadingState" record used by static module loading.
///
/// This is a host/evaluator-owned value; `vm-js` carries it through as required by ECMA-262.
#[derive(Clone)]
pub struct GraphLoadingState(Arc<dyn Any + Send + Sync>);

impl GraphLoadingState {
  pub fn new<T: Any + Send + Sync>(data: T) -> Self {
    Self(Arc::new(data))
  }

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

/// Opaque wrapper representing a loaded Module Record.
///
/// This module record is created by the host's module graph loader. `vm-js` does not yet interpret
/// the module directly, but it must preserve the token to allow future linking/evaluation.
#[derive(Clone)]
pub struct ModuleRecord(Arc<dyn Any + Send + Sync>);

impl ModuleRecord {
  pub fn new<T: Any + Send + Sync>(data: T) -> Self {
    Self(Arc::new(data))
  }

  pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
    self.0.downcast_ref::<T>()
  }
}

impl fmt::Debug for ModuleRecord {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("ModuleRecord")
      .field("type_id", &self.0.type_id())
      .finish()
  }
}

/// The completion record passed to `FinishLoadingImportedModule`.
///
/// In the spec this is either:
/// - a normal completion containing a Module Record, or
/// - a throw completion containing an ECMAScript value.
pub type ModuleCompletion = Result<ModuleRecord, Value>;

/// A spec-shaped PromiseCapability record.
///
/// This is used as the `payload` when starting a dynamic import (`import()`), and is later passed
/// back to `ContinueDynamicImport` via `FinishLoadingImportedModule`.
///
/// Note: this is currently only a container for the three values; Promise semantics are not yet
/// implemented by `vm-js`.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct PromiseCapability {
  pub promise: Value,
  pub resolve: Value,
  pub reject: Value,
}

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
  UnsupportedImportAttribute { key: JsString },
}

/// Host hooks required for module loading.
///
/// Embeddings (or a future evaluator) implement this trait to perform I/O and module graph
/// construction.
pub trait VmModuleHostHooks {
  /// Host-defined hook corresponding to `HostLoadImportedModule`.
  ///
  /// The host must eventually call [`finish_loading_imported_module`] with the same `referrer`,
  /// `module_request`, and `payload` (either synchronously or asynchronously).
  fn host_load_imported_module(
    &mut self,
    referrer: ModuleReferrer,
    module_request: ModuleRequest,
    host_defined: (),
    payload: ModuleLoadPayload,
  );

  /// Host-defined hook corresponding to `HostGetSupportedImportAttributes`.
  ///
  /// The spec requires that repeated calls return the same list with the same order.
  fn host_get_supported_import_attributes(&mut self) -> Vec<JsString> {
    Vec::new()
  }
}

fn clone_js_string(heap: &crate::Heap, s: GcString) -> Result<JsString, VmError> {
  Ok(heap.get_string(s)?.clone())
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
  supported_keys: &[JsString],
) -> Result<Vec<ImportAttribute>, ImportCallError> {
  if matches!(options, Value::Undefined) {
    return Ok(Vec::new());
  }

  let Value::Object(options_obj) = options else {
    return Err(ImportCallError::TypeError(ImportCallTypeError::OptionsNotObject));
  };

  let with_key = PropertyKey::String(make_key_string(scope, "with").map_err(ImportCallError::Vm)?);
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

    let key = clone_js_string(scope.heap(), key_string).map_err(ImportCallError::Vm)?;
    let value = clone_js_string(scope.heap(), value_string).map_err(ImportCallError::Vm)?;

    attributes.push(ImportAttribute { key, value });
  }

  // `AllImportAttributesSupported`.
  for attribute in &attributes {
    if !supported_keys.iter().any(|supported| supported == &attribute.key) {
      return Err(ImportCallError::TypeError(
        ImportCallTypeError::UnsupportedImportAttribute {
        key: attribute.key.clone(),
      },
      ));
    }
  }

  // Sort by UTF-16 code units.
  attributes.sort_by(|a, b| a.key.cmp(&b.key));
  Ok(attributes)
}

/// Spec helper: `AllImportAttributesSupported(attributes)`.
pub fn all_import_attributes_supported(
  supported_keys: &[JsString],
  attributes: &[ImportAttribute],
) -> bool {
  attributes
    .iter()
    .all(|attr| supported_keys.iter().any(|k| k == &attr.key))
}

/// Spec-shaped dynamic import entry point (EvaluateImportCall).
///
/// This function currently returns [`VmError::Unimplemented`] because `vm-js` does not yet provide
/// a Promise implementation or a full module evaluator.
pub fn start_dynamic_import(
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmModuleHostHooks,
  _active_script_or_module: Option<ScriptOrModuleId>,
  _realm: RealmId,
  _specifier: JsString,
  _options: Value,
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
  match payload {
    ModuleLoadPayload::GraphLoadingState(state) => continue_module_loading(state, result),
    ModuleLoadPayload::PromiseCapability(promise_capability) => continue_dynamic_import(promise_capability, result),
  }
}

/// Placeholder for the static-module loading continuation (`ContinueModuleLoading`).
pub fn continue_module_loading(
  _state: GraphLoadingState,
  _result: ModuleCompletion,
) -> Result<(), VmError> {
  Err(VmError::Unimplemented("ContinueModuleLoading"))
}

/// Placeholder for the dynamic import continuation (`ContinueDynamicImport`).
pub fn continue_dynamic_import(
  _promise_capability: PromiseCapability,
  _module_completion: ModuleCompletion,
) -> Result<(), VmError> {
  Err(VmError::Unimplemented("ContinueDynamicImport"))
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::property::PropertyDescriptor;
  use crate::property::PropertyKey as HeapPropertyKey;
  use crate::property::PropertyKind as HeapPropertyKind;
  use crate::Heap;
  use crate::HeapLimits;

  fn js(s: &str) -> JsString {
    JsString::from_u16_vec(s.encode_utf16().collect())
  }

  fn utf8_lossy_from_key(heap: &Heap, key: HeapPropertyKey) -> String {
    match key {
      HeapPropertyKey::String(s) => heap.get_string(s).unwrap().to_utf8_lossy(),
      HeapPropertyKey::Symbol(_) => "<symbol>".to_string(),
    }
  }

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
  fn own_property_keys_orders_array_indices_then_strings_then_symbols() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();

    let obj = scope.alloc_object().unwrap();

    let k_b = scope.alloc_string("b").unwrap();
    let k_1 = scope.alloc_string("1").unwrap();
    let k_a = scope.alloc_string("a").unwrap();
    let k_0 = scope.alloc_string("0").unwrap();
    let sym = scope.alloc_symbol(Some("s")).unwrap();

    scope
      .define_property(obj, HeapPropertyKey::String(k_b), data_desc(Value::Undefined, true))
      .unwrap();
    scope
      .define_property(obj, HeapPropertyKey::String(k_1), data_desc(Value::Undefined, true))
      .unwrap();
    scope
      .define_property(obj, HeapPropertyKey::String(k_a), data_desc(Value::Undefined, true))
      .unwrap();
    scope
      .define_property(obj, HeapPropertyKey::String(k_0), data_desc(Value::Undefined, true))
      .unwrap();
    scope
      .define_property(
        obj,
        HeapPropertyKey::Symbol(sym),
        data_desc(Value::Undefined, true),
      )
      .unwrap();

    let keys = scope.ordinary_own_property_keys(obj).unwrap();
    let rendered: Vec<String> = keys
      .into_iter()
      .map(|k| utf8_lossy_from_key(scope.heap(), k))
      .collect();

    assert_eq!(rendered, vec!["0", "1", "b", "a", "<symbol>"]);
  }

  #[test]
  fn import_attributes_from_options_validates_and_sorts() {
    let mut vm = crate::Vm::new(crate::VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();

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

    let supported = vec![js("a"), js("type")];
    let attrs =
      import_attributes_from_options(&mut vm, &mut scope, Value::Object(options), &supported).unwrap();

    let keys: Vec<String> = attrs.iter().map(|a| a.key.to_utf8_lossy()).collect();
    assert_eq!(keys, vec!["a", "type"]);
  }

  #[test]
  fn import_attributes_from_options_rejects_invalid_types() {
    let mut vm = crate::Vm::new(crate::VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let mut scope = heap.scope();

    let supported = vec![js("type")];
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
}
