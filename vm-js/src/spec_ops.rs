//! Spec operations (ECMA-262 abstract operations).
//!
//! This module contains small helpers that mirror ECMA-262 abstract operations closely. These are
//! intended to be used by built-ins so their algorithms remain spec-shaped.

use crate::{GcObject, PropertyDescriptorPatch, PropertyKey, Scope, Value, Vm, VmError};

/// `GetPrototypeFromConstructor(constructor, intrinsicDefaultProto)` (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#sec-getprototypefromconstructor>
pub fn get_prototype_from_constructor(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  constructor: Value,
  intrinsic_default_proto: GcObject,
) -> Result<GcObject, VmError> {
  let Value::Object(constructor_obj) = constructor else {
    // The spec asserts `IsConstructor(constructor)`; treat non-objects as "use default".
    return Ok(intrinsic_default_proto);
  };

  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(constructor_obj))?;
  scope.push_root(Value::Object(intrinsic_default_proto))?;

  let key_s = scope.alloc_string("prototype")?;
  scope.push_root(Value::String(key_s))?;
  let key = PropertyKey::from_string(key_s);

  let proto = vm.get(&mut scope, constructor_obj, key)?;
  match proto {
    Value::Object(o) => Ok(o),
    _ => Ok(intrinsic_default_proto),
  }
}

/// `OrdinaryCreateFromConstructor(constructor, intrinsicDefaultProto, internalSlotsList)`
/// (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#sec-ordinarycreatefromconstructor>
pub fn ordinary_create_from_constructor<F>(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  new_target: Value,
  intrinsic_default_proto: GcObject,
  _internal_slots_list: &[&'static str],
  allocate: F,
) -> Result<GcObject, VmError>
where
  F: FnOnce(&mut Scope<'_>) -> Result<GcObject, VmError>,
{
  let proto = get_prototype_from_constructor(vm, scope, new_target, intrinsic_default_proto)?;

  // Root `new_target`/`proto` across allocation in case it triggers GC.
  let mut scope = scope.reborrow();
  scope.push_root(new_target)?;
  scope.push_root(Value::Object(proto))?;

  let obj = allocate(&mut scope)?;
  scope.heap_mut().object_set_prototype(obj, Some(proto))?;
  Ok(obj)
}

/// `CreateDataProperty(O, P, V)` (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#sec-createdataproperty>
#[inline]
pub fn create_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  value: Value,
) -> Result<bool, VmError> {
  scope.create_data_property(obj, key, value)
}

/// `CreateDataPropertyOrThrow(O, P, V)` (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#sec-createdatapropertyorthrow>
#[inline]
pub fn create_data_property_or_throw(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  value: Value,
) -> Result<(), VmError> {
  scope.create_data_property_or_throw(obj, key, value)
}

/// `DefinePropertyOrThrow(O, P, desc)` (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#sec-definepropertyorthrow>
#[inline]
pub fn define_property_or_throw(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  desc: PropertyDescriptorPatch,
) -> Result<(), VmError> {
  scope.define_property_or_throw(obj, key, desc)
}

/// `DeletePropertyOrThrow(O, P)` (ECMA-262).
///
/// Spec: <https://tc39.es/ecma262/#sec-deletepropertyorthrow>
#[inline]
pub fn delete_property_or_throw(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
) -> Result<(), VmError> {
  scope.delete_property_or_throw(obj, key)
}

/// `GetMethod(V, P)` (ECMA-262) (partial).
///
/// Spec: <https://tc39.es/ecma262/#sec-getmethod>
#[inline]
pub fn get_method(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  value: Value,
  key: PropertyKey,
) -> Result<Option<Value>, VmError> {
  vm.get_method(scope, value, key)
}
