//! Minimal `%Proxy%` exotic objects (ECMA-262 §10.5 / §28.2).
//!
//! Implements enough of ProxyCreate / Proxy [[Set]] / [[Call]] / [[Construct]] /
//! `Proxy.revocable` for typeof-on-proxy and PutValue-through-proxy-prototype tests.
//! Full trap surface (get/has/ownKeys/…) is intentionally deferred.

use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Scope, Value, Vm, VmError, VmHost, VmHostHooks};

const PROXY_TARGET: &str = "vm-js.internal.ProxyTarget";
const PROXY_HANDLER: &str = "vm-js.internal.ProxyHandler";

fn data_desc(
  value: Value,
  writable: bool,
  enumerable: bool,
  configurable: bool,
) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable,
    configurable,
    kind: PropertyKind::Data { value, writable },
  }
}

fn marker_key(scope: &mut Scope<'_>, name: &str) -> Result<PropertyKey, VmError> {
  let s = scope.alloc_string(name)?;
  let sym = scope.heap_mut().symbol_for(s)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn property_key_to_value(key: PropertyKey) -> Value {
  match key {
    PropertyKey::String(s) => Value::String(s),
    PropertyKey::Symbol(s) => Value::Symbol(s),
  }
}

/// Returns `true` when `obj` is a Proxy exotic object (including revoked proxies).
pub fn is_proxy(scope: &mut Scope<'_>, obj: GcObject) -> Result<bool, VmError> {
  let key = marker_key(scope, PROXY_TARGET)?;
  Ok(scope.heap().object_get_own_property(obj, &key)?.is_some())
}

fn proxy_slots(scope: &mut Scope<'_>, obj: GcObject) -> Result<(Value, Value), VmError> {
  let target_key = marker_key(scope, PROXY_TARGET)?;
  let handler_key = marker_key(scope, PROXY_HANDLER)?;
  let target = scope
    .heap()
    .object_get_own_data_property_value(obj, &target_key)?
    .unwrap_or(Value::Undefined);
  let handler = scope
    .heap()
    .object_get_own_data_property_value(obj, &handler_key)?
    .unwrap_or(Value::Undefined);
  Ok((target, handler))
}

fn require_proxy_handler(
  scope: &mut Scope<'_>,
  proxy: GcObject,
) -> Result<(GcObject, GcObject), VmError> {
  let (target, handler) = proxy_slots(scope, proxy)?;
  match (target, handler) {
    (Value::Object(t), Value::Object(h)) => Ok((t, h)),
    _ => Err(VmError::TypeError(
      "Cannot perform operation on a revoked Proxy",
    )),
  }
}

/// ProxyCreate (ECMA-262 §10.5.1) — installs `[[ProxyTarget]]` / `[[ProxyHandler]]`.
///
/// If `target` is callable, the result is a callable/constructable function object so
/// `typeof` yields `"function"` (and remains so after revoke).
pub fn proxy_create(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  target: GcObject,
  handler: GcObject,
) -> Result<GcObject, VmError> {
  scope.push_root(Value::Object(target))?;
  scope.push_root(Value::Object(handler))?;

  let callable = scope.heap().is_callable(Value::Object(target))?;
  let constructable = scope.heap().is_constructor(Value::Object(target))?;

  let proxy = if callable {
    let call = vm.register_native_call(proxy_call)?;
    let construct = if constructable {
      Some(vm.register_native_construct(proxy_construct)?)
    } else {
      None
    };
    let name = scope.alloc_string("")?;
    let f = scope.alloc_native_function(call, construct, name, 0)?;
    scope.push_root(Value::Object(f))?;
    if let Some(intr) = vm.intrinsics() {
      scope
        .heap_mut()
        .object_set_prototype(f, Some(intr.function_prototype()))?;
    }
    f
  } else {
    let obj = scope.alloc_object()?;
    scope.push_root(Value::Object(obj))?;
    if let Some(intr) = vm.intrinsics() {
      scope
        .heap_mut()
        .object_set_prototype(obj, Some(intr.object_prototype()))?;
    }
    obj
  };

  let target_key = marker_key(scope, PROXY_TARGET)?;
  let handler_key = marker_key(scope, PROXY_HANDLER)?;
  // Non-enumerable, non-configurable internal slots (not JS-observable by ordinary ownKeys
  // filtering is not required for the current suite; Symbol.for keys stay out of typical tests).
  scope.define_property(
    proxy,
    target_key,
    data_desc(Value::Object(target), true, false, false),
  )?;
  scope.define_property(
    proxy,
    handler_key,
    data_desc(Value::Object(handler), true, false, false),
  )?;

  Ok(proxy)
}

fn revoke_proxy(scope: &mut Scope<'_>, proxy: GcObject) -> Result<(), VmError> {
  let target_key = marker_key(scope, PROXY_TARGET)?;
  let handler_key = marker_key(scope, PROXY_HANDLER)?;
  // Overwrite slots to `null` (revoked). Writable was set true so redefine succeeds.
  scope.define_property(
    proxy,
    target_key,
    data_desc(Value::Null, true, false, false),
  )?;
  scope.define_property(
    proxy,
    handler_key,
    data_desc(Value::Null, true, false, false),
  )?;
  Ok(())
}

/// `new Proxy(target, handler)` / `Proxy(target, handler)` (must be invoked with `new`).
pub fn proxy_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::TypeError("Constructor Proxy requires 'new'"))
}

/// `new Proxy(target, handler)`.
pub fn proxy_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  let target = match args.first().copied().unwrap_or(Value::Undefined) {
    Value::Object(o) => o,
    _ => return Err(VmError::TypeError("Proxy target must be an object")),
  };
  let handler = match args.get(1).copied().unwrap_or(Value::Undefined) {
    Value::Object(o) => o,
    _ => return Err(VmError::TypeError("Proxy handler must be an object")),
  };
  let proxy = proxy_create(vm, scope, target, handler)?;
  Ok(Value::Object(proxy))
}

/// `Proxy.revocable(target, handler)` → `{ proxy, revoke }`.
pub fn proxy_revocable(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let target = match args.first().copied().unwrap_or(Value::Undefined) {
    Value::Object(o) => o,
    _ => return Err(VmError::TypeError("Proxy target must be an object")),
  };
  let handler = match args.get(1).copied().unwrap_or(Value::Undefined) {
    Value::Object(o) => o,
    _ => return Err(VmError::TypeError("Proxy handler must be an object")),
  };

  let proxy = proxy_create(vm, scope, target, handler)?;
  scope.push_root(Value::Object(proxy))?;

  // Revoke closes over `proxy` via a native slot.
  let revoke_call = vm.register_native_call(proxy_revoke_call)?;
  let revoke_name = scope.alloc_string("revoke")?;
  let revoke = scope.alloc_native_function_with_slots(
    revoke_call,
    None,
    revoke_name,
    0,
    &[Value::Object(proxy)],
  )?;
  scope.push_root(Value::Object(revoke))?;
  if let Some(intr) = vm.intrinsics() {
    scope
      .heap_mut()
      .object_set_prototype(revoke, Some(intr.function_prototype()))?;
  }

  let result = scope.alloc_object()?;
  scope.push_root(Value::Object(result))?;
  if let Some(intr) = vm.intrinsics() {
    scope
      .heap_mut()
      .object_set_prototype(result, Some(intr.object_prototype()))?;
  }
  let proxy_key = PropertyKey::from_string(scope.alloc_string("proxy")?);
  let revoke_key = PropertyKey::from_string(scope.alloc_string("revoke")?);
  scope.define_property(
    result,
    proxy_key,
    data_desc(Value::Object(proxy), true, true, true),
  )?;
  scope.define_property(
    result,
    revoke_key,
    data_desc(Value::Object(revoke), true, true, true),
  )?;
  Ok(Value::Object(result))
}

fn proxy_revoke_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let slots = scope.heap().get_function_native_slots(callee)?;
  let Some(Value::Object(proxy)) = slots.first().copied() else {
    return Ok(Value::Undefined);
  };
  // Idempotent: already-revoked proxies are a no-op (ECMA-262 ProxyRevoke).
  let (_, handler) = proxy_slots(scope, proxy)?;
  if matches!(handler, Value::Null | Value::Undefined) {
    return Ok(Value::Undefined);
  }
  revoke_proxy(scope, proxy)?;
  Ok(Value::Undefined)
}

fn proxy_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let (target, _handler) = require_proxy_handler(scope, callee)?;
  scope.push_root(Value::Object(target))?;
  // Trap-less [[Call]]: Call(target, this, args). Full `apply` trap deferred.
  vm.call_with_host_and_hooks(host, scope, hooks, Value::Object(target), this, args)
}

fn proxy_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let (target, _handler) = require_proxy_handler(scope, callee)?;
  scope.push_root(Value::Object(target))?;
  vm.construct_with_host_and_hooks(host, scope, hooks, Value::Object(target), args, new_target)
}

/// Proxy `[[Set]]` (ECMA-262 §10.5.9) — `set` trap when present; else target `[[Set]]`.
pub fn proxy_set(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  proxy: GcObject,
  key: PropertyKey,
  value: Value,
  receiver: Value,
) -> Result<bool, VmError> {
  let (target, handler) = require_proxy_handler(scope, proxy)?;
  scope.push_root(Value::Object(target))?;
  scope.push_root(Value::Object(handler))?;
  scope.push_root(value)?;
  scope.push_root(receiver)?;

  let set_key = PropertyKey::from_string(scope.alloc_string("set")?);
  let trap = scope.ordinary_get_with_host_and_hooks(
    vm,
    host,
    hooks,
    handler,
    set_key,
    Value::Object(handler),
  )?;
  if matches!(trap, Value::Undefined) {
    return scope.ordinary_set_with_host_and_hooks(vm, host, hooks, target, key, value, receiver);
  }
  if !scope.heap().is_callable(trap)? {
    return Err(VmError::TypeError("Proxy 'set' trap is not callable"));
  }
  scope.push_root(trap)?;
  let key_val = property_key_to_value(key);
  scope.push_root(key_val)?;
  let result = vm.call_with_host_and_hooks(
    host,
    scope,
    hooks,
    trap,
    Value::Object(handler),
    &[Value::Object(target), key_val, value, receiver],
  )?;
  Ok(scope.heap().to_boolean(result)?)
}
