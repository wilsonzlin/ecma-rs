use crate::property::PropertyKey;
use crate::{GcObject, GcSymbol, Scope, Value, Vm, VmError, VmHost, VmHostHooks};

/// ECMAScript "IteratorRecord" (ECMA-262).
///
/// This is intentionally spec-shaped (iterator object + next method + done flag). For now we also
/// embed a private fast-path state for Array iteration so `for..of`/spread can work before full
/// `%Array.prototype%[@@iterator]` exists.
#[derive(Debug, Clone, Copy)]
pub struct IteratorRecord {
  pub iterator: Value,
  pub next_method: Value,
  pub done: bool,
  kind: IteratorKind,
}

#[derive(Debug, Clone, Copy)]
enum IteratorKind {
  Protocol,
  Array {
    array: GcObject,
    next_index: u32,
    length: u32,
  },
}

fn string_key(scope: &mut Scope<'_>, s: &str) -> Result<PropertyKey, VmError> {
  Ok(PropertyKey::from_string(scope.alloc_string(s)?))
}

fn symbol_for(scope: &mut Scope<'_>, description: &str) -> Result<GcSymbol, VmError> {
  let key = scope.alloc_string(description)?;
  scope.heap_mut().symbol_for(key)
}

fn is_array(scope: &mut Scope<'_>, value: Value) -> Result<Option<GcObject>, VmError> {
  let Value::Object(obj) = value else {
    return Ok(None);
  };
  if scope.heap().object_is_array(obj)? {
    return Ok(Some(obj));
  }
  Ok(None)
}

fn array_length(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  array: GcObject,
) -> Result<u32, VmError> {
  let length_key = string_key(scope, "length")?;
  let len_value =
    scope.ordinary_get_with_host_and_hooks(vm, host, hooks, array, length_key, Value::Object(array))?;
  match len_value {
    Value::Number(n) if n.is_finite() && n >= 0.0 => Ok(n as u32),
    _ => Err(VmError::Unimplemented("Array length is not a uint32 Number")),
  }
}

fn get_method(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  obj: Value,
  key: PropertyKey,
) -> Result<Option<Value>, VmError> {
  let Value::Object(obj) = obj else {
    return Err(VmError::Unimplemented("GetMethod on non-object"));
  };

  let func = scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, key, Value::Object(obj))?;
  if matches!(func, Value::Undefined | Value::Null) {
    return Ok(None);
  }
  if !scope.heap().is_callable(func)? {
    return Err(VmError::NotCallable);
  }
  Ok(Some(func))
}

/// `GetIterator` (ECMA-262).
///
/// For now, this supports:
/// - A fast path for Array exotic objects.
/// - A minimal iterator-protocol path via `@@iterator` for objects with native-callable iterator
///   methods.
pub fn get_iterator(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  iterable: Value,
) -> Result<IteratorRecord, VmError> {
  if let Some(array) = is_array(scope, iterable)? {
    let length = array_length(vm, host, hooks, scope, array)?;
    return Ok(IteratorRecord {
      iterator: Value::Object(array),
      next_method: Value::Undefined,
      done: false,
      kind: IteratorKind::Array {
        array,
        next_index: 0,
        length,
      },
    });
  }

  // Fall back to iterator protocol: `GetMethod(iterable, @@iterator)`.
  let iterator_sym = symbol_for(scope, "Symbol.iterator")?;
  let method = get_method(vm, host, hooks, scope, iterable, PropertyKey::from_symbol(iterator_sym))?
    .ok_or(VmError::Unimplemented("GetIterator: missing @@iterator method"))?;
  get_iterator_from_method(vm, host, hooks, scope, iterable, method)
}

/// `GetIteratorFromMethod` (ECMA-262).
pub fn get_iterator_from_method(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  iterable: Value,
  method: Value,
) -> Result<IteratorRecord, VmError> {
  let iterator = vm.call_with_host_and_hooks(host, scope, hooks, method, iterable, &[])?;
  let Value::Object(iterator_obj) = iterator else {
    return Err(VmError::Unimplemented(
      "GetIteratorFromMethod: iterator method did not return an object",
    ));
  };

  // Root the iterator object while allocating/reading the `next` method in case those operations
  // trigger GC.
  let mut next_scope = scope.reborrow();
  next_scope.push_root(iterator)?;

  let next_key = string_key(&mut next_scope, "next")?;
  let next = next_scope.ordinary_get_with_host_and_hooks(
    vm,
    host,
    hooks,
    iterator_obj,
    next_key,
    Value::Object(iterator_obj),
  )?;
  if !next_scope.heap().is_callable(next)? {
    return Err(VmError::NotCallable);
  }

  Ok(IteratorRecord {
    iterator,
    next_method: next,
    done: false,
    kind: IteratorKind::Protocol,
  })
}

/// `IteratorNext` (ECMA-262).
pub fn iterator_next(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  record: &IteratorRecord,
) -> Result<Value, VmError> {
  match record.kind {
    IteratorKind::Protocol => {
      vm.call_with_host_and_hooks(host, scope, hooks, record.next_method, record.iterator, &[])
    }
    IteratorKind::Array { .. } => Err(VmError::Unimplemented(
      "IteratorNext is not used for Array fast-path iterators",
    )),
  }
}

/// `IteratorComplete` (ECMA-262).
pub fn iterator_complete(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  iter_result: Value,
) -> Result<bool, VmError> {
  let Value::Object(obj) = iter_result else {
    return Err(VmError::Unimplemented(
      "IteratorComplete: iterator result is not an object",
    ));
  };
  let done_key = string_key(scope, "done")?;
  let done = scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, done_key, iter_result)?;
  scope.heap().to_boolean(done)
}

/// `IteratorValue` (ECMA-262).
pub fn iterator_value(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  iter_result: Value,
) -> Result<Value, VmError> {
  let Value::Object(obj) = iter_result else {
    return Err(VmError::Unimplemented(
      "IteratorValue: iterator result is not an object",
    ));
  };
  let value_key = string_key(scope, "value")?;
  scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, value_key, iter_result)
}

/// `IteratorStepValue` (ECMA-262).
///
/// Returns `Ok(None)` when iteration is complete.
pub fn iterator_step_value(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  record: &mut IteratorRecord,
) -> Result<Option<Value>, VmError> {
  if record.done {
    return Ok(None);
  }

  match &mut record.kind {
    IteratorKind::Array {
      array,
      next_index,
      length,
    } => {
      if *next_index >= *length {
        record.done = true;
        return Ok(None);
      }

      let idx = *next_index;
      *next_index = next_index.saturating_add(1);

      let key = string_key(scope, &idx.to_string())?;
      let value = scope.ordinary_get_with_host_and_hooks(vm, host, hooks, *array, key, Value::Object(*array))?;
      Ok(Some(value))
    }
    IteratorKind::Protocol => {
      let result = iterator_next(vm, host, hooks, scope, record)?;
      if iterator_complete(vm, host, hooks, scope, result)? {
        record.done = true;
        return Ok(None);
      }
      Ok(Some(iterator_value(vm, host, hooks, scope, result)?))
    }
  }
}

/// `IteratorClose` (ECMA-262) (best-effort).
///
/// This is used by `for..of` to close iterators on abrupt completion. For now we intentionally
/// swallow any error from the `return` call since the surrounding interpreter does not yet have a
/// full exception model.
pub fn iterator_close(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  record: &IteratorRecord,
) -> Result<(), VmError> {
  if matches!(record.kind, IteratorKind::Array { .. }) {
    return Ok(());
  }

  let return_key = string_key(scope, "return")?;
  let Some(return_method) = get_method(vm, host, hooks, scope, record.iterator, return_key)? else {
    return Ok(());
  };

  // Best-effort: ignore errors.
  let _ = vm.call_with_host_and_hooks(host, scope, hooks, return_method, record.iterator, &[]);
  Ok(())
}

// Note: old `vm-js.internal.ArrayMarker` tagging was removed now that arrays are proper exotic
// objects.
