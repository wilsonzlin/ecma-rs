use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
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
  /// Private Array exotic fast-path (CreateAsyncFromSyncIterator / legacy). Not constructed by
  /// [`get_iterator`] anymore — arrays go through `%Array.prototype%[@@iterator]`.
  #[allow(dead_code)]
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

#[allow(dead_code)]
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
  let len_value = scope.ordinary_get_with_host_and_hooks(
    vm,
    host,
    hooks,
    array,
    length_key,
    Value::Object(array),
  )?;
  match len_value {
    Value::Number(n) if n.is_finite() && n >= 0.0 => Ok(n as u32),
    _ => Err(VmError::Unimplemented(
      "Array length is not a uint32 Number",
    )),
  }
}

fn get_method(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  value: Value,
  key: PropertyKey,
) -> Result<Option<Value>, VmError> {
  // GetMethod → GetV → ToObject: null/undefined throw TypeError (§7.3.2 / §7.1.18).
  let obj = match value {
    Value::Object(obj) => obj,
    Value::Undefined | Value::Null => {
      return Err(throw_type_error(
        vm,
        scope,
        "GetMethod: cannot convert undefined or null to object",
      )?);
    }
    other => {
      let intr = vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
      let object_ctor = Value::Object(intr.object_constructor());
      let mut box_scope = scope.reborrow();
      box_scope.push_root(other)?;
      box_scope.push_root(object_ctor)?;
      let boxed = vm.call_with_host_and_hooks(
        host,
        &mut box_scope,
        hooks,
        object_ctor,
        Value::Undefined,
        &[other],
      )?;
      let Value::Object(obj) = boxed else {
        return Err(VmError::InvariantViolation(
          "Object(..) conversion returned non-object",
        ));
      };
      // Keep the box alive on the outer scope after `box_scope` drops.
      drop(box_scope);
      scope.push_root(Value::Object(obj))?;
      obj
    }
  };

  let func =
    scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, key, Value::Object(obj))?;
  if matches!(func, Value::Undefined | Value::Null) {
    return Ok(None);
  }
  if !scope.heap().is_callable(func)? {
    return Err(VmError::NotCallable);
  }
  Ok(Some(func))
}

/// Marker keys for Async-from-Sync Iterator internal slots (not exposed as JS names).
fn afsi_marker_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.AsyncFromSyncIterator")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn afsi_kind_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.AsyncFromSyncKind")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn afsi_sync_iterator_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.SyncIterator")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn afsi_sync_next_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.SyncNextMethod")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn afsi_array_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.SyncArray")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn afsi_index_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.SyncNextIndex")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn afsi_length_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.SyncLength")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

const AFSI_KIND_PROTOCOL: f64 = 0.0;
const AFSI_KIND_ARRAY: f64 = 1.0;

/// `CreateAsyncFromSyncIterator` (ECMA-262 §7.4.11 / §27.1.4).
///
/// Wraps a sync `IteratorRecord` in an async iterator whose `next` returns Promises of
/// `{ value, done }` (sufficient for `for await` over arrays and sync generators).
pub fn create_async_from_sync_iterator(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  sync: IteratorRecord,
) -> Result<IteratorRecord, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "CreateAsyncFromSyncIterator requires intrinsics",
  ))?;

  let mut s = scope.reborrow();
  s.push_roots(&[sync.iterator, sync.next_method])?;

  let wrapper = s.alloc_object_with_prototype(Some(intr.async_from_sync_iterator_prototype()))?;
  s.push_root(Value::Object(wrapper))?;

  let marker_key = afsi_marker_key(&mut s)?;
  let kind_key = afsi_kind_key(&mut s)?;
  let sync_iter_key = afsi_sync_iterator_key(&mut s)?;
  let sync_next_key = afsi_sync_next_key(&mut s)?;
  let array_key = afsi_array_key(&mut s)?;
  let index_key = afsi_index_key(&mut s)?;
  let length_key = afsi_length_key(&mut s)?;
  let next_key = string_key(&mut s, "next")?;

  s.define_property(
    wrapper,
    marker_key,
    data_desc(Value::Bool(true), false, false, false),
  )?;

  match sync.kind {
    IteratorKind::Protocol => {
      s.define_property(
        wrapper,
        kind_key,
        data_desc(Value::Number(AFSI_KIND_PROTOCOL), true, false, false),
      )?;
      s.define_property(
        wrapper,
        sync_iter_key,
        data_desc(sync.iterator, true, false, false),
      )?;
      s.define_property(
        wrapper,
        sync_next_key,
        data_desc(sync.next_method, true, false, false),
      )?;
    }
    IteratorKind::Array {
      array,
      next_index,
      length,
    } => {
      s.define_property(
        wrapper,
        kind_key,
        data_desc(Value::Number(AFSI_KIND_ARRAY), true, false, false),
      )?;
      s.define_property(
        wrapper,
        array_key,
        data_desc(Value::Object(array), true, false, false),
      )?;
      s.define_property(
        wrapper,
        index_key,
        data_desc(Value::Number(next_index as f64), true, false, false),
      )?;
      s.define_property(
        wrapper,
        length_key,
        data_desc(Value::Number(length as f64), true, false, false),
      )?;
    }
  }

  let next_method =
    s.ordinary_get_with_host_and_hooks(vm, host, hooks, wrapper, next_key, Value::Object(wrapper))?;
  if !s.heap().is_callable(next_method)? {
    return Err(VmError::NotCallable);
  }

  Ok(IteratorRecord {
    iterator: Value::Object(wrapper),
    next_method,
    done: false,
    kind: IteratorKind::Protocol,
  })
}

/// `%AsyncFromSyncIteratorPrototype%.next` (§27.1.4.2.1).
///
/// Minimal: steps the sync iterator and returns `PromiseResolve({ value, done })`. Does not yet
/// implement full `AsyncFromSyncIteratorContinuation` thenable-unwrapping of `value`.
pub(crate) fn async_from_sync_iterator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Err(VmError::TypeError(
      "AsyncFromSyncIterator.prototype.next called on non-object",
    ));
  };

  let mut s = scope.reborrow();
  s.push_root(Value::Object(this_obj))?;

  let marker = afsi_marker_key(&mut s)?;
  let has_marker = s
    .heap()
    .object_get_own_data_property_value(this_obj, &marker)?
    .is_some();
  if !has_marker {
    return Err(VmError::TypeError(
      "AsyncFromSyncIterator.prototype.next called on incompatible receiver",
    ));
  }

  match step_sync_from_wrapper(vm, host, hooks, &mut s, this_obj) {
    Ok(iter_result) => {
      s.push_root(iter_result)?;
      crate::promise_ops::promise_resolve(vm, &mut s, hooks, iter_result)
    }
    Err(err) => {
      let Some(reason) = err.thrown_value() else {
        return Err(err);
      };
      s.push_root(reason)?;
      let cap = crate::promise_ops::new_promise_capability(vm, &mut s, hooks)?;
      let reject = cap.reject;
      let promise = cap.promise;
      s.push_root(promise)?;
      let _ =
        vm.call_with_host_and_hooks(host, &mut s, hooks, reject, Value::Undefined, &[reason])?;
      Ok(promise)
    }
  }
}

fn step_sync_from_wrapper(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  wrapper: GcObject,
) -> Result<Value, VmError> {
  let kind_key = afsi_kind_key(scope)?;
  let array_key = afsi_array_key(scope)?;
  let index_key = afsi_index_key(scope)?;
  let length_key = afsi_length_key(scope)?;
  let sync_iter_key = afsi_sync_iterator_key(scope)?;
  let sync_next_key = afsi_sync_next_key(scope)?;

  let kind = match scope
    .heap()
    .object_get_own_data_property_value(wrapper, &kind_key)?
  {
    Some(Value::Number(n)) => n,
    _ => {
      return Err(VmError::InvariantViolation(
        "AsyncFromSyncIterator missing kind",
      ))
    }
  };

  if kind == AFSI_KIND_ARRAY {
    let array = match scope
      .heap()
      .object_get_own_data_property_value(wrapper, &array_key)?
    {
      Some(Value::Object(a)) => a,
      _ => {
        return Err(VmError::InvariantViolation(
          "AsyncFromSyncIterator missing array",
        ))
      }
    };
    let next_index = match scope
      .heap()
      .object_get_own_data_property_value(wrapper, &index_key)?
    {
      Some(Value::Number(n)) if n.is_finite() && n >= 0.0 => n as u32,
      _ => 0,
    };
    let length = match scope
      .heap()
      .object_get_own_data_property_value(wrapper, &length_key)?
    {
      Some(Value::Number(n)) if n.is_finite() && n >= 0.0 => n as u32,
      _ => 0,
    };

    if next_index >= length {
      return crate::generator::create_iter_result_object(vm, scope, Value::Undefined, true);
    }

    let idx = next_index;
    scope.define_property(
      wrapper,
      index_key,
      data_desc(Value::Number((idx + 1) as f64), true, false, false),
    )?;

    let key = string_key(scope, &idx.to_string())?;
    let value =
      scope.ordinary_get_with_host_and_hooks(vm, host, hooks, array, key, Value::Object(array))?;
    return crate::generator::create_iter_result_object(vm, scope, value, false);
  }

  // Protocol sync iterator.
  let sync_iterator = scope
    .heap()
    .object_get_own_data_property_value(wrapper, &sync_iter_key)?
    .unwrap_or(Value::Undefined);
  let sync_next = scope
    .heap()
    .object_get_own_data_property_value(wrapper, &sync_next_key)?
    .unwrap_or(Value::Undefined);
  scope.push_roots(&[sync_iterator, sync_next])?;

  let result = vm.call_with_host_and_hooks(host, scope, hooks, sync_next, sync_iterator, &[])?;
  // Sync `next` should already return an IteratorResult; pass it through.
  if !matches!(result, Value::Object(_)) {
    return Err(VmError::TypeError(
      "IteratorResult from sync iterator is not an object",
    ));
  }
  Ok(result)
}

/// `GetIterator` with hint async (ECMA-262 §7.4.2): prefer `@@asyncIterator`, else wrap sync.
pub fn get_async_iterator(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  iterable: Value,
) -> Result<IteratorRecord, VmError> {
  let async_iterator_sym = match vm.intrinsics() {
    Some(intr) => intr.well_known_symbols().async_iterator,
    None => symbol_for(scope, "Symbol.asyncIterator")?,
  };
  let method = get_method(
    vm,
    host,
    hooks,
    scope,
    iterable,
    PropertyKey::from_symbol(async_iterator_sym),
  )?;
  if let Some(method) = method {
    return get_iterator_from_method(vm, host, hooks, scope, iterable, method);
  }

  // Fallback: GetIterator (sync) + CreateAsyncFromSyncIterator.
  let sync = get_iterator(vm, host, hooks, scope, iterable)?;
  create_async_from_sync_iterator(vm, host, hooks, scope, sync)
}

fn throw_type_error(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> Result<VmError, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let value =
    crate::error_object::new_error(scope, intr.type_error_prototype(), "TypeError", message)?;
  Ok(VmError::Throw(value))
}

/// `GetIterator` (ECMA-262 §7.4.1, sync hint).
///
/// Always uses the iterator protocol (`GetMethod(obj, @@iterator)`). Arrays are iterable via
/// `%Array.prototype%[@@iterator]` (`values`); the former Array exotic fast-path is retained only
/// inside [`IteratorRecord`] for CreateAsyncFromSyncIterator wrapping of sync array iteration.
pub fn get_iterator(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  iterable: Value,
) -> Result<IteratorRecord, VmError> {
  // @@iterator must be the realm's well-known symbol (the same one `Symbol.iterator` exposes and
  // `%IteratorPrototype%[@@iterator]` is keyed by) — NOT a `Symbol.for` registry symbol.
  let iterator_sym = match vm.intrinsics() {
    Some(intr) => intr.well_known_symbols().iterator,
    None => symbol_for(scope, "Symbol.iterator")?,
  };
  let method = get_method(
    vm,
    host,
    hooks,
    scope,
    iterable,
    PropertyKey::from_symbol(iterator_sym),
  )?;
  let Some(method) = method else {
    return Err(throw_type_error(
      vm,
      scope,
      "GetIterator: object is not iterable",
    )?);
  };
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
    return Err(throw_type_error(
      vm,
      scope,
      "GetIteratorFromMethod: iterator method did not return an object",
    )?);
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
    return Err(throw_type_error(
      vm,
      scope,
      "IteratorComplete: iterator result is not an object",
    )?);
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
    return Err(throw_type_error(
      vm,
      scope,
      "IteratorValue: iterator result is not an object",
    )?);
  };
  let value_key = string_key(scope, "value")?;
  scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, value_key, iter_result)
}

/// `IteratorStepValue` (ECMA-262).
///
/// Returns `Ok(None)` when iteration is complete. On abrupt completion from `next` / `done` /
/// `value`, sets `record.done = true` (IteratorBindingInitialization requirement).
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
      let value = scope.ordinary_get_with_host_and_hooks(
        vm,
        host,
        hooks,
        *array,
        key,
        Value::Object(*array),
      )?;
      Ok(Some(value))
    }
    IteratorKind::Protocol => {
      let result = match iterator_next(vm, host, hooks, scope, record) {
        Ok(v) => v,
        Err(e) => {
          record.done = true;
          return Err(e);
        }
      };
      let complete = match iterator_complete(vm, host, hooks, scope, result) {
        Ok(d) => d,
        Err(e) => {
          record.done = true;
          return Err(e);
        }
      };
      if complete {
        record.done = true;
        return Ok(None);
      }
      match iterator_value(vm, host, hooks, scope, result) {
        Ok(v) => Ok(Some(v)),
        Err(e) => {
          record.done = true;
          Err(e)
        }
      }
    }
  }
}

/// `IteratorClose` (ECMA-262 §7.4.11) with a normal completion.
pub fn iterator_close(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  record: &IteratorRecord,
) -> Result<(), VmError> {
  iterator_close_with_completion(vm, host, hooks, scope, record, Ok(()))
}

/// `IteratorClose` (ECMA-262 §7.4.11).
///
/// If `completion` is abrupt, `return` errors are discarded and `completion` is re-thrown.
/// If `completion` is normal, abrupt results from `GetMethod`/`Call`/`TypeError` propagate.
pub fn iterator_close_with_completion(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  record: &IteratorRecord,
  completion: Result<(), VmError>,
) -> Result<(), VmError> {
  if matches!(record.kind, IteratorKind::Array { .. }) {
    return completion;
  }

  let return_key = match string_key(scope, "return") {
    Ok(k) => k,
    Err(e) => {
      if completion.is_err() {
        return completion;
      }
      return Err(e);
    }
  };

  let return_method = match get_method(vm, host, hooks, scope, record.iterator, return_key) {
    Ok(m) => m,
    Err(e) => {
      if completion.is_err() {
        return completion;
      }
      return Err(e);
    }
  };

  let Some(return_method) = return_method else {
    return completion;
  };

  let inner = vm.call_with_host_and_hooks(host, scope, hooks, return_method, record.iterator, &[]);
  if completion.is_err() {
    return completion;
  }
  let inner = inner?;
  if !matches!(inner, Value::Object(_)) {
    return Err(throw_type_error(
      vm,
      scope,
      "IteratorClose: iterator return did not return an object",
    )?);
  }
  completion
}

// ---------------------------------------------------------------------------
// Array iterator (%ArrayIteratorPrototype% / Array.prototype.values / @@iterator)
// ---------------------------------------------------------------------------

fn array_iter_marker_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.ArrayIterator")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn array_iter_array_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.ArrayIteratorArray")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn array_iter_index_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.ArrayIteratorIndex")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

/// `CreateArrayIterator` (ECMA-262 §23.1.5.1) — values kind only.
pub fn create_array_iterator(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  array: GcObject,
) -> Result<Value, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "CreateArrayIterator requires intrinsics",
  ))?;
  let mut s = scope.reborrow();
  s.push_root(Value::Object(array))?;

  let iter = s.alloc_object_with_prototype(Some(intr.array_iterator_prototype()))?;
  s.push_root(Value::Object(iter))?;

  let marker_key = array_iter_marker_key(&mut s)?;
  let array_key = array_iter_array_key(&mut s)?;
  let index_key = array_iter_index_key(&mut s)?;

  s.define_property(
    iter,
    marker_key,
    data_desc(Value::Bool(true), false, false, false),
  )?;
  s.define_property(
    iter,
    array_key,
    data_desc(Value::Object(array), true, false, false),
  )?;
  s.define_property(
    iter,
    index_key,
    data_desc(Value::Number(0.0), true, false, false),
  )?;

  Ok(Value::Object(iter))
}

/// `%Array.prototype%.values` / `%Array.prototype%[@@iterator]` (§23.1.3.33 / §23.1.3.35).
pub(crate) fn array_prototype_values(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  // RequireObjectCoercible: null/undefined → TypeError. Full ToObject for primitives is deferred.
  match this {
    Value::Undefined | Value::Null => Err(throw_type_error(
      vm,
      scope,
      "Array.prototype.values called on null or undefined",
    )?),
    Value::Object(obj) => create_array_iterator(vm, scope, obj),
    _ => Err(VmError::Unimplemented(
      "Array.prototype.values on primitive receiver",
    )),
  }
}

/// `%ArrayIteratorPrototype%.next` (§23.1.5.2.1).
pub(crate) fn array_iterator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Err(throw_type_error(
      vm,
      scope,
      "Array Iterator.prototype.next called on non-object",
    )?);
  };

  let mut s = scope.reborrow();
  s.push_root(Value::Object(this_obj))?;

  let marker = array_iter_marker_key(&mut s)?;
  let has_marker = s
    .heap()
    .object_get_own_data_property_value(this_obj, &marker)?
    .is_some();
  if !has_marker {
    return Err(throw_type_error(
      vm,
      &mut s,
      "Array Iterator.prototype.next called on incompatible receiver",
    )?);
  }

  let array_key = array_iter_array_key(&mut s)?;
  let index_key = array_iter_index_key(&mut s)?;

  let array = match s
    .heap()
    .object_get_own_data_property_value(this_obj, &array_key)?
  {
    Some(Value::Object(a)) => a,
    Some(Value::Undefined) | None => {
      return crate::generator::create_iter_result_object(vm, &mut s, Value::Undefined, true);
    }
    _ => {
      return Err(VmError::InvariantViolation(
        "ArrayIterator missing iterated array",
      ))
    }
  };

  let next_index = match s
    .heap()
    .object_get_own_data_property_value(this_obj, &index_key)?
  {
    Some(Value::Number(n)) if n.is_finite() && n >= 0.0 => n as u32,
    _ => 0,
  };

  let length = array_length(vm, host, hooks, &mut s, array)?;
  if next_index >= length {
    s.define_property(
      this_obj,
      array_key,
      data_desc(Value::Undefined, true, false, false),
    )?;
    return crate::generator::create_iter_result_object(vm, &mut s, Value::Undefined, true);
  }

  s.define_property(
    this_obj,
    index_key,
    data_desc(Value::Number((next_index + 1) as f64), true, false, false),
  )?;

  let key = string_key(&mut s, &next_index.to_string())?;
  let value =
    s.ordinary_get_with_host_and_hooks(vm, host, hooks, array, key, Value::Object(array))?;
  crate::generator::create_iter_result_object(vm, &mut s, value, false)
}

// Note: old `vm-js.internal.ArrayMarker` tagging was removed now that arrays are proper exotic
// objects.

// ---------------------------------------------------------------------------
// String iterator (%StringIteratorPrototype% / String.prototype[@@iterator])
// ---------------------------------------------------------------------------

fn string_iter_marker_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.StringIterator")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn string_iter_string_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.StringIteratorString")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

fn string_iter_index_key(scope: &mut Scope<'_>) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string("vm-js.internal.StringIteratorIndex")?;
  let sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(sym))
}

/// `CreateStringIterator` (ECMA-262 §22.1.5.1).
pub fn create_string_iterator(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  string: Value,
) -> Result<Value, VmError> {
  let Value::String(_) = string else {
    return Err(VmError::InvariantViolation(
      "CreateStringIterator requires a String value",
    ));
  };
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "CreateStringIterator requires intrinsics",
  ))?;
  let mut s = scope.reborrow();
  s.push_root(string)?;

  let iter = s.alloc_object_with_prototype(Some(intr.string_iterator_prototype()))?;
  s.push_root(Value::Object(iter))?;

  let marker_key = string_iter_marker_key(&mut s)?;
  let string_key = string_iter_string_key(&mut s)?;
  let index_key = string_iter_index_key(&mut s)?;

  s.define_property(
    iter,
    marker_key,
    data_desc(Value::Bool(true), false, false, false),
  )?;
  s.define_property(iter, string_key, data_desc(string, true, false, false))?;
  s.define_property(
    iter,
    index_key,
    data_desc(Value::Number(0.0), true, false, false),
  )?;

  Ok(Value::Object(iter))
}

/// `%String.prototype%[@@iterator]` (§22.1.3.29).
pub(crate) fn string_prototype_iterator(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  if matches!(this, Value::Undefined | Value::Null) {
    return Err(throw_type_error(
      vm,
      scope,
      "String.prototype[@@iterator] called on null or undefined",
    )?);
  }
  let s = crate::spec_ops::to_string(vm, scope, this)?;
  create_string_iterator(vm, scope, Value::String(s))
}

/// `%StringIteratorPrototype%.next` (§22.1.5.2.1) — yields Unicode code points.
pub(crate) fn string_iterator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Err(throw_type_error(
      vm,
      scope,
      "String Iterator.prototype.next called on non-object",
    )?);
  };

  let mut s = scope.reborrow();
  s.push_root(Value::Object(this_obj))?;

  let marker = string_iter_marker_key(&mut s)?;
  let has_marker = s
    .heap()
    .object_get_own_data_property_value(this_obj, &marker)?
    .is_some();
  if !has_marker {
    return Err(throw_type_error(
      vm,
      &mut s,
      "String Iterator.prototype.next called on incompatible receiver",
    )?);
  }

  let string_key = string_iter_string_key(&mut s)?;
  let index_key = string_iter_index_key(&mut s)?;

  let string = match s
    .heap()
    .object_get_own_data_property_value(this_obj, &string_key)?
  {
    Some(Value::String(str_gc)) => str_gc,
    Some(Value::Undefined) | None => {
      return crate::generator::create_iter_result_object(vm, &mut s, Value::Undefined, true);
    }
    _ => {
      return Err(VmError::InvariantViolation(
        "StringIterator missing iterated string",
      ))
    }
  };

  let next_index = match s
    .heap()
    .object_get_own_data_property_value(this_obj, &index_key)?
  {
    Some(Value::Number(n)) if n.is_finite() && n >= 0.0 => n as usize,
    _ => 0,
  };

  let units = s.heap().get_string(string)?.as_code_units().to_vec();
  if next_index >= units.len() {
    s.define_property(
      this_obj,
      string_key,
      data_desc(Value::Undefined, true, false, false),
    )?;
    return crate::generator::create_iter_result_object(vm, &mut s, Value::Undefined, true);
  }

  let cu = units[next_index];
  let (cp_units, advance) = if (0xD800..=0xDBFF).contains(&cu) && next_index + 1 < units.len() {
    let cu2 = units[next_index + 1];
    if (0xDC00..=0xDFFF).contains(&cu2) {
      (&units[next_index..next_index + 2], 2usize)
    } else {
      (&units[next_index..next_index + 1], 1usize)
    }
  } else {
    (&units[next_index..next_index + 1], 1usize)
  };

  s.define_property(
    this_obj,
    index_key,
    data_desc(
      Value::Number((next_index + advance) as f64),
      true,
      false,
      false,
    ),
  )?;

  let result_s = s.alloc_string_from_code_units(cp_units)?;
  crate::generator::create_iter_result_object(vm, &mut s, Value::String(result_s), false)
}
