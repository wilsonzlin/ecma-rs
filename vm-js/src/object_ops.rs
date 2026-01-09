use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Heap, Scope, Value, Vm, VmError};

fn strict_type_error_or_ignore(strict: bool, message: &'static str) -> Result<(), VmError> {
  if strict {
    Err(VmError::Unimplemented(message))
  } else {
    Ok(())
  }
}

fn define_own_writable_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  value: Value,
) -> Result<(), VmError> {
  scope.define_property(
    obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value,
        writable: true,
      },
    },
  )
}

/// ECMAScript `OrdinaryGet` for ordinary objects.
///
/// This implements enough of `[[Get]]` to support:
/// - data properties
/// - accessor properties (getter call with the provided `receiver` as `this`)
/// - prototype chain traversal
pub fn ordinary_get(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  receiver: Value,
  key: PropertyKey,
) -> Result<Value, VmError> {
  let Value::Object(receiver_obj) = receiver else {
    return Err(VmError::Unimplemented(
      "TypeError: [[Get]] receiver is not an object",
    ));
  };

  let Some((_holder, desc)) = scope
    .heap()
    .get_property_with_holder(receiver_obj, &key)?
  else {
    return Ok(Value::Undefined);
  };

  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(value),
    PropertyKind::Accessor { get, .. } => {
      if matches!(get, Value::Undefined) {
        return Ok(Value::Undefined);
      }
      if !scope.heap().is_callable(get)? {
        return Err(VmError::Unimplemented(
          "TypeError: accessor getter is not callable",
        ));
      }

      vm.call(scope, get, receiver, &[])
    }
  }
}

/// ECMAScript `OrdinarySet` for ordinary objects (simplified).
///
/// This implements a spec-shaped subset of `[[Set]]`:
/// - update writable own data properties
/// - call accessor setters (own or inherited) with `receiver` as `this`
/// - when setting an inherited writable data property, create an own data property on the receiver
/// - when setting a missing property, create an own data property on the receiver
///
/// When the set operation fails and `strict` is `true`, this returns a stubbed TypeError via
/// `VmError::Unimplemented("TypeError: ...")`. When `strict` is `false`, failures are silent.
pub fn ordinary_set(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  receiver: Value,
  key: PropertyKey,
  value: Value,
  strict: bool,
) -> Result<(), VmError> {
  let receiver_obj = match receiver {
    Value::Object(obj) => obj,
    _ => {
      return strict_type_error_or_ignore(strict, "TypeError: [[Set]] receiver is not an object");
    }
  };

  // 1) Own property fast path.
  if let Some(desc) = scope.heap().object_get_own_property(receiver_obj, &key)? {
    return match desc.kind {
      PropertyKind::Data { writable, .. } => {
        if !writable {
          return strict_type_error_or_ignore(strict, "TypeError: property is not writable");
        }
        scope
          .heap_mut()
          .object_set_existing_data_property_value(receiver_obj, &key, value)?;
        Ok(())
      }
      PropertyKind::Accessor { set, .. } => {
        if matches!(set, Value::Undefined) {
          return strict_type_error_or_ignore(strict, "TypeError: property has no setter");
        }
        if !scope.heap().is_callable(set)? {
          return Err(VmError::Unimplemented(
            "TypeError: accessor setter is not callable",
          ));
        }

        let _ = vm.call(scope, set, receiver, &[value])?;
        Ok(())
      }
    };
  }

  // 2) Inherited property.
  if let Some(proto) = scope.heap().object_prototype(receiver_obj)? {
    if let Some((_holder, desc)) = scope.heap().get_property_with_holder(proto, &key)? {
      return match desc.kind {
        PropertyKind::Accessor { set, .. } => {
          if matches!(set, Value::Undefined) {
            return strict_type_error_or_ignore(strict, "TypeError: property has no setter");
          }
          if !scope.heap().is_callable(set)? {
            return Err(VmError::Unimplemented(
              "TypeError: accessor setter is not callable",
            ));
          }

          let _ = vm.call(scope, set, receiver, &[value])?;
          Ok(())
        }
        PropertyKind::Data { writable, .. } => {
          if !writable {
            return strict_type_error_or_ignore(strict, "TypeError: property is not writable");
          }
          define_own_writable_data_property(scope, receiver_obj, key, value)
        }
      };
    }
  }

  // 3) Missing property: create a new own data property.
  define_own_writable_data_property(scope, receiver_obj, key, value)
}

/// Minimal `[[DefineOwnProperty]]` wrapper around the heap's `define_property` machinery.
pub fn ordinary_define_own_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  desc: PropertyDescriptor,
) -> Result<(), VmError> {
  scope.define_property(obj, key, desc)
}

/// `[[OwnPropertyKeys]]` for ordinary objects (ES ordering rules).
///
/// Ordering:
/// 1. Array indices (String keys that are array indices), ascending.
/// 2. Other String keys, in insertion order.
/// 3. Symbol keys, in insertion order.
pub fn own_property_keys(heap: &Heap, obj: GcObject) -> Result<Vec<PropertyKey>, VmError> {
  let keys = heap.object_keys_in_insertion_order(obj)?;

  let mut index_keys: Vec<(u32, PropertyKey)> = Vec::new();
  let mut string_keys: Vec<PropertyKey> = Vec::new();
  let mut symbol_keys: Vec<PropertyKey> = Vec::new();

  for key in keys {
    match key {
      PropertyKey::String(_) => match heap.property_key_to_array_index(&key)? {
        Some(idx) => index_keys.push((idx, key)),
        None => string_keys.push(key),
      },
      PropertyKey::Symbol(_) => symbol_keys.push(key),
    }
  }

  index_keys.sort_by_key(|(idx, _)| *idx);

  let mut out = Vec::with_capacity(index_keys.len() + string_keys.len() + symbol_keys.len());
  out.extend(index_keys.into_iter().map(|(_, k)| k));
  out.extend(string_keys);
  out.extend(symbol_keys);
  Ok(out)
}

