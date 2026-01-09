use crate::heap::Scope;
use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, GcString, Value, VmError};

/// ECMA-262-like helper for setting a function's `name` property.
///
/// This defines (or overwrites) `F.name` as a:
/// - non-writable
/// - non-enumerable
/// - configurable
/// data property.
pub fn set_function_name(
  scope: &mut Scope<'_>,
  func: GcObject,
  name: PropertyKey,
  prefix: Option<&str>,
) -> Result<(), VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(func))?;

  let computed = compute_function_name(&mut scope, name, prefix)?;
  scope.push_root(Value::String(computed))?;

  let name_key = scope.alloc_string("name")?;
  scope.define_property(
    func,
    PropertyKey::String(name_key),
    PropertyDescriptor {
      enumerable: false,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::String(computed),
        writable: false,
      },
    },
  )?;

  scope.heap_mut().set_function_name_metadata(func, computed)?;
  Ok(())
}

/// ECMA-262-like helper for setting a function's `length` property.
///
/// This defines (or overwrites) `F.length` as a:
/// - non-writable
/// - non-enumerable
/// - configurable
/// data property.
pub fn set_function_length(
  scope: &mut Scope<'_>,
  func: GcObject,
  length: u32,
) -> Result<(), VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(func))?;

  let length_key = scope.alloc_string("length")?;
  scope.define_property(
    func,
    PropertyKey::String(length_key),
    PropertyDescriptor {
      enumerable: false,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(length as f64),
        writable: false,
      },
    },
  )?;

  scope.heap_mut().set_function_length_metadata(func, length)?;
  Ok(())
}

/// ECMA-262-like helper for creating a function's `.prototype` object and wiring
/// `.prototype.constructor`.
///
/// This defines:
/// - `F.prototype` as a writable, non-enumerable, non-configurable data property
/// - `F.prototype.constructor` as a writable, non-enumerable, configurable data property
pub fn make_constructor(scope: &mut Scope<'_>, func: GcObject) -> Result<GcObject, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(func))?;

  let prototype = scope.alloc_object()?;
  scope.push_root(Value::Object(prototype))?;

  let constructor_key = scope.alloc_string("constructor")?;
  scope.define_property(
    prototype,
    PropertyKey::String(constructor_key),
    PropertyDescriptor {
      enumerable: false,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Object(func),
        writable: true,
      },
    },
  )?;

  let prototype_key = scope.alloc_string("prototype")?;
  scope.define_property(
    func,
    PropertyKey::String(prototype_key),
    PropertyDescriptor {
      enumerable: false,
      configurable: false,
      kind: PropertyKind::Data {
        value: Value::Object(prototype),
        writable: true,
      },
    },
  )?;

  Ok(prototype)
}

fn compute_function_name(
  scope: &mut Scope<'_>,
  name: PropertyKey,
  prefix: Option<&str>,
) -> Result<GcString, VmError> {
  if prefix.is_none() {
    if let PropertyKey::String(name) = name {
      return Ok(name);
    }
  }

  // Compute total code unit length up-front so we can use fallible allocation and
  // avoid any infallible Vec growth that could abort the process.
  let prefix_units_len = prefix
    .map(|p| p.encode_utf16().count().saturating_add(1))
    .unwrap_or(0);

  let base_units_len = match name {
    PropertyKey::String(s) => scope.heap().get_string(s)?.len_code_units(),
    PropertyKey::Symbol(sym) => {
      let desc_len = match scope.heap().get_symbol_description(sym)? {
        Some(desc) => scope.heap().get_string(desc)?.len_code_units(),
        None => 0,
      };
      desc_len.saturating_add(2) // "[" + desc + "]"
    }
  };

  let total_units_len = prefix_units_len.saturating_add(base_units_len);

  let mut units: Vec<u16> = Vec::new();
  units
    .try_reserve_exact(total_units_len)
    .map_err(|_| VmError::OutOfMemory)?;

  if let Some(prefix) = prefix {
    units.extend(prefix.encode_utf16());
    units.push(' ' as u16);
  }

  match name {
    PropertyKey::String(s) => {
      units.extend_from_slice(scope.heap().get_string(s)?.as_code_units());
    }
    PropertyKey::Symbol(sym) => {
      units.push('[' as u16);
      if let Some(desc) = scope.heap().get_symbol_description(sym)? {
        units.extend_from_slice(scope.heap().get_string(desc)?.as_code_units());
      }
      units.push(']' as u16);
    }
  }

  debug_assert_eq!(
    units.len(),
    total_units_len,
    "compute_function_name miscomputed UTF-16 length"
  );

  scope.alloc_string_from_u16_vec(units)
}
