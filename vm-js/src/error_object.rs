use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Intrinsics, Scope, Value, VmError};

fn data_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: false,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

/// Create a minimal native `Error` object instance.
///
/// This is intentionally small and spec-shaped:
/// - Allocate an ordinary object.
/// - Set its `[[Prototype]]` to the provided intrinsic prototype.
/// - Define own non-enumerable `"name"` and `"message"` data properties.
pub fn new_error(
  scope: &mut Scope<'_>,
  prototype: GcObject,
  name: &str,
  message: &str,
) -> Result<Value, VmError> {
  let err = scope.alloc_object()?;
  // Root the object for the remainder of construction. Subsequent property definition may
  // allocate and trigger GC.
  scope.push_root(Value::Object(err))?;

  scope
    .heap_mut()
    .object_set_prototype(err, Some(prototype))?;

  let name_value = scope.alloc_string(name)?;
  scope.push_root(Value::String(name_value))?;

  let message_value = scope.alloc_string(message)?;
  scope.push_root(Value::String(message_value))?;

  let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
  scope.define_property(err, name_key, data_desc(Value::String(name_value)))?;

  let message_key = PropertyKey::from_string(scope.alloc_string("message")?);
  scope.define_property(err, message_key, data_desc(Value::String(message_value)))?;

  Ok(Value::Object(err))
}

/// Allocates a new ECMAScript `TypeError` object (instance).
///
/// This is an object factory (not a callable constructor) intended for spec-shaped algorithms such
/// as module loading that need to reject/throw with real Error instances.
pub fn new_type_error_object(
  scope: &mut Scope<'_>,
  intrinsics: &Intrinsics,
  message: &str,
) -> Result<Value, VmError> {
  new_error(
    scope,
    intrinsics.type_error_prototype(),
    "TypeError",
    message,
  )
}

/// Allocates a new ECMAScript `SyntaxError` object (instance).
///
/// This is an object factory (not a callable constructor) intended for spec-shaped algorithms such
/// as module loading that need to reject/throw with real Error instances.
pub fn new_syntax_error_object(
  scope: &mut Scope<'_>,
  intrinsics: &Intrinsics,
  message: &str,
) -> Result<Value, VmError> {
  new_error(
    scope,
    intrinsics.syntax_error_prototype(),
    "SyntaxError",
    message,
  )
}

pub fn new_type_error(
  scope: &mut Scope<'_>,
  intr: Intrinsics,
  message: &str,
) -> Result<Value, VmError> {
  new_type_error_object(scope, &intr, message)
}

pub fn throw_type_error(scope: &mut Scope<'_>, intr: Intrinsics, message: &str) -> VmError {
  match new_type_error(scope, intr, message) {
    Ok(value) => VmError::Throw(value),
    Err(err) => err,
  }
}

pub fn new_reference_error(
  scope: &mut Scope<'_>,
  intr: Intrinsics,
  message: &str,
) -> Result<Value, VmError> {
  new_error(
    scope,
    intr.reference_error_prototype(),
    "ReferenceError",
    message,
  )
}

pub fn new_range_error(
  scope: &mut Scope<'_>,
  intr: Intrinsics,
  message: &str,
) -> Result<Value, VmError> {
  new_error(scope, intr.range_error_prototype(), "RangeError", message)
}
