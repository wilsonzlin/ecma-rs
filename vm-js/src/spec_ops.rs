//! Spec operations (ECMA-262 abstract operations).
//!
//! This module contains small helpers that mirror ECMA-262 abstract operations closely. These are
//! intended to be used by built-ins so their algorithms remain spec-shaped.

use crate::error_object::throw_type_error;
use crate::{GcObject, GcString, PropertyDescriptorPatch, PropertyKey, Scope, Value, Vm, VmError};

/// Preferred type hint for [`to_primitive`] (ECMA-262 §7.1.1).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ToPrimitiveHint {
  Default,
  String,
  Number,
}

impl ToPrimitiveHint {
  fn as_str(self) -> &'static str {
    match self {
      ToPrimitiveHint::Default => "default",
      ToPrimitiveHint::String => "string",
      ToPrimitiveHint::Number => "number",
    }
  }
}

/// `ToPrimitive(input [, preferredType])` (ECMA-262 §7.1.1).
///
/// Invokes `@@toPrimitive` when present, otherwise [`ordinary_to_primitive`].
pub fn to_primitive(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  value: Value,
  hint: ToPrimitiveHint,
) -> Result<Value, VmError> {
  let Value::Object(obj) = value else {
    return Ok(value);
  };

  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj))?;

  let Some(intr) = vm.intrinsics() else {
    return Err(VmError::Unimplemented("ToPrimitive requires intrinsics"));
  };
  let to_prim_key = PropertyKey::from_symbol(intr.well_known_symbols().to_primitive);
  if let Some(exotic) = vm.get_method_from_object(&mut scope, obj, to_prim_key)? {
    scope.push_root(exotic)?;
    let hint_s = scope.alloc_string(hint.as_str())?;
    scope.push_root(Value::String(hint_s))?;
    let out = vm.call_without_host(
      &mut scope,
      exotic,
      Value::Object(obj),
      &[Value::String(hint_s)],
    )?;
    if !matches!(out, Value::Object(_)) {
      return Ok(out);
    }
    return Err(throw_type_error(
      &mut scope,
      intr,
      "Cannot convert object to primitive value",
    ));
  }

  ordinary_to_primitive(vm, &mut scope, obj, hint)
}

/// `OrdinaryToPrimitive(O, hint)` (ECMA-262 §7.1.1.1).
pub fn ordinary_to_primitive(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  obj: GcObject,
  hint: ToPrimitiveHint,
) -> Result<Value, VmError> {
  let hint = match hint {
    ToPrimitiveHint::Default => ToPrimitiveHint::Number,
    other => other,
  };
  let methods: &[&str] = match hint {
    ToPrimitiveHint::String => &["toString", "valueOf"],
    ToPrimitiveHint::Number | ToPrimitiveHint::Default => &["valueOf", "toString"],
  };

  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj))?;

  for name in methods {
    let key_s = scope.alloc_string(name)?;
    scope.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);
    let method = vm.get(&mut scope, obj, key)?;
    if matches!(method, Value::Undefined | Value::Null) {
      continue;
    }
    if !scope.heap().is_callable(method)? {
      continue;
    }
    scope.push_root(method)?;
    let result = vm.call_without_host(&mut scope, method, Value::Object(obj), &[])?;
    if !matches!(result, Value::Object(_)) {
      return Ok(result);
    }
  }

  let Some(intr) = vm.intrinsics() else {
    return Err(VmError::TypeError(
      "Cannot convert object to primitive value",
    ));
  };
  Err(throw_type_error(
    &mut scope,
    intr,
    "Cannot convert object to primitive value",
  ))
}

/// `ToString(argument)` (ECMA-262 §7.1.17), including object → primitive conversion.
pub fn to_string(vm: &mut Vm, scope: &mut Scope<'_>, value: Value) -> Result<GcString, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(value)?;
  let prim = to_primitive(vm, &mut scope, value, ToPrimitiveHint::String)?;
  scope.push_root(prim)?;
  match scope.heap_mut().to_string(prim) {
    Ok(s) => Ok(s),
    Err(VmError::TypeError(msg)) => {
      let Some(intr) = vm.intrinsics() else {
        return Err(VmError::TypeError(msg));
      };
      Err(throw_type_error(&mut scope, intr, msg))
    }
    Err(err) => Err(err),
  }
}

/// `ToPropertyKey(argument)` (ECMA-262 §7.1.19).
pub fn to_property_key(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  value: Value,
) -> Result<PropertyKey, VmError> {
  match value {
    Value::String(s) => Ok(PropertyKey::String(s)),
    Value::Symbol(s) => Ok(PropertyKey::Symbol(s)),
    other => {
      let mut scope = scope.reborrow();
      scope.push_root(other)?;
      let prim = to_primitive(vm, &mut scope, other, ToPrimitiveHint::String)?;
      scope.push_root(prim)?;
      match prim {
        Value::Symbol(s) => Ok(PropertyKey::Symbol(s)),
        _ => Ok(PropertyKey::String(scope.heap_mut().to_string(prim)?)),
      }
    }
  }
}

/// `ToNumber(argument)` (ECMA-262 §7.1.4), including object → primitive conversion.
pub fn to_number(vm: &mut Vm, scope: &mut Scope<'_>, value: Value) -> Result<f64, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(value)?;
  let prim = to_primitive(vm, &mut scope, value, ToPrimitiveHint::Number)?;
  scope.push_root(prim)?;
  match crate::ops::to_number(scope.heap_mut(), prim) {
    Ok(n) => Ok(n),
    Err(VmError::TypeError(msg)) => {
      let Some(intr) = vm.intrinsics() else {
        return Err(VmError::TypeError(msg));
      };
      Err(throw_type_error(&mut scope, intr, msg))
    }
    Err(err) => Err(err),
  }
}

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
