//! ECMAScript Promise abstract operations used by module loading algorithms.
//!
//! `vm-js` implements the `%Promise%` built-in primarily via [`crate::builtins`]. Some spec
//! algorithms (notably module loading and dynamic import continuations) need direct access to
//! Promise abstract operations such as:
//! - `NewPromiseCapability(%Promise%)`
//! - `PromiseResolve(%Promise%, value)`
//! - `PerformPromiseThen(promise, onFulfilled, onRejected)`
//!
//! This module exposes small, spec-shaped helpers that are convenient to call from engine code
//! without going through property lookups on the global `Promise` constructor.

use crate::{PromiseCapability, Scope, Value, Vm, VmError, VmHostHooks};

/// `NewPromiseCapability(%Promise%)`.
pub fn new_promise_capability(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
) -> Result<PromiseCapability, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "NewPromiseCapability requires intrinsics (create a Realm first)",
  ))?;
  crate::builtins::new_promise_capability(vm, scope, host, Value::Object(intr.promise()))
}

/// `PromiseResolve(%Promise%, value)`.
///
/// Returns a Promise object.
pub fn promise_resolve(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  value: Value,
) -> Result<Value, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "PromiseResolve requires intrinsics (create a Realm first)",
  ))?;

  // Fast path: if `value` is already a %Promise% instance, return it.
  if let Value::Object(obj) = value {
    if scope.heap().is_promise_object(obj) && scope.heap().object_prototype(obj)? == Some(intr.promise_prototype()) {
      return Ok(Value::Object(obj));
    }
  }

  let cap = new_promise_capability(vm, scope, host)?;
  let _ = vm.call_with_host(scope, host, cap.resolve, Value::Undefined, &[value])?;
  Ok(cap.promise)
}

/// `PerformPromiseThen(promise, onFulfilled, onRejected)`.
///
/// Returns the derived Promise (the value returned by `promise.then(...)`).
pub fn perform_promise_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  promise: Value,
  on_fulfilled: Option<Value>,
  on_rejected: Option<Value>,
) -> Result<Value, VmError> {
  crate::builtins::perform_promise_then(
    vm,
    scope,
    host,
    promise,
    on_fulfilled.unwrap_or(Value::Undefined),
    on_rejected.unwrap_or(Value::Undefined),
  )
}
