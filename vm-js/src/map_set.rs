//! `%Map%` / `%Set%` / `%WeakMap%` / `%WeakSet%` collections
//! (ECMA-262 §24.1–§24.4).
//!
//! Map/Set: constructor (+ iterable), `get`/`set`/`has`/`delete`/`clear`/`size`,
//! iteration (`keys`/`values`/`entries`/`forEach`/`@@iterator`), `@@toStringTag`,
//! `Map.groupBy`, `getOrInsert` / `getOrInsertComputed`,
//! Set composition (`union`/`intersection`/`difference`/`symmetricDifference`/
//! `isSubsetOf`/`isSupersetOf`/`isDisjointFrom` via `GetSetRecord`).
//! WeakMap/WeakSet: constructor (+ iterable), `get`/`set`/`has`/`delete` (or
//! `add`/`has`/`delete`), `getOrInsert` / `getOrInsertComputed`,
//! `CanBeHeldWeakly` (Objects + unregistered Symbols).
//! Entries are stored strongly for now; true weak GC edges are deferred.
//!
//! `[[MapData]]` / `[[SetData]]` / `[[WeakMapData]]` / `[[WeakSetData]]` are
//! ordinary Arrays of entry records behind internal symbol slots so GC traces
//! keys/values without a new `ObjectKind`.

use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Scope, Value, Vm, VmError, VmHost, VmHostHooks};

const MAP_DATA: &str = "vm-js.internal.MapData";
const SET_DATA: &str = "vm-js.internal.SetData";
const MAP_ITER_MARKER: &str = "vm-js.internal.MapIterator";
const MAP_ITER_MAP: &str = "vm-js.internal.MapIteratorMap";
const MAP_ITER_INDEX: &str = "vm-js.internal.MapIteratorIndex";
const MAP_ITER_KIND: &str = "vm-js.internal.MapIteratorKind";
const SET_ITER_MARKER: &str = "vm-js.internal.SetIterator";
const SET_ITER_SET: &str = "vm-js.internal.SetIteratorSet";
const SET_ITER_INDEX: &str = "vm-js.internal.SetIteratorIndex";
const SET_ITER_KIND: &str = "vm-js.internal.SetIteratorKind";

/// Iterator kind: 0 = key, 1 = value, 2 = key+value.
const KIND_KEY: f64 = 0.0;
const KIND_VALUE: f64 = 1.0;
const KIND_ENTRY: f64 = 2.0;

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

fn string_key(scope: &mut Scope<'_>, s: &str) -> Result<PropertyKey, VmError> {
  Ok(PropertyKey::from_string(scope.alloc_string(s)?))
}

fn index_key(scope: &mut Scope<'_>, i: u32) -> Result<PropertyKey, VmError> {
  string_key(scope, &i.to_string())
}

fn same_value_zero(a: Value, b: Value, scope: &Scope<'_>) -> bool {
  a.same_value_zero(b, scope.heap())
}

fn same_value(a: Value, b: Value, scope: &Scope<'_>) -> bool {
  a.same_value(b, scope.heap())
}

/// `CanonicalizeKeyedCollectionKey` (ECMA-262 §24.5.1).
fn canonicalize_keyed_collection_key(key: Value) -> Value {
  if let Value::Number(n) = key {
    if n == 0.0 {
      return Value::Number(0.0);
    }
  }
  key
}

/// `%IntrinsicDefaultProto%` from GetFunctionRealm(newTarget), else the active realm.
fn default_proto_from_new_target(
  vm: &Vm,
  scope: &Scope<'_>,
  new_target: Value,
  pick: impl FnOnce(&crate::Intrinsics) -> GcObject,
) -> Result<GcObject, VmError> {
  let active = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let Value::Object(nt) = new_target else {
    return Ok(pick(&active));
  };
  let Some(intr) = vm.intrinsics_for_function(scope.heap(), nt)? else {
    return Ok(pick(&active));
  };
  Ok(pick(&intr))
}

/// `CanBeHeldWeakly(v)` (ECMA-262 §10.1.2.1 / collections).
fn can_be_held_weakly(scope: &Scope<'_>, v: Value) -> Result<bool, VmError> {
  match v {
    Value::Object(_) => Ok(true),
    Value::Symbol(sym) => Ok(scope.heap().symbol_key_for(sym)?.is_none()),
    _ => Ok(false),
  }
}

fn create_array(vm: &mut Vm, scope: &mut Scope<'_>, len: u32) -> Result<GcObject, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let array = scope.alloc_array(len as usize)?;
  scope
    .heap_mut()
    .object_set_prototype(array, Some(intr.array_prototype()))?;
  Ok(array)
}

fn array_len(scope: &Scope<'_>, array: GcObject) -> Result<u32, VmError> {
  Ok(scope.heap().array_length(array).unwrap_or(0))
}

fn array_get(scope: &mut Scope<'_>, array: GcObject, i: u32) -> Result<Value, VmError> {
  let key = index_key(scope, i)?;
  Ok(
    scope
      .heap()
      .object_get_own_data_property_value(array, &key)?
      .unwrap_or(Value::Undefined),
  )
}

fn array_set(scope: &mut Scope<'_>, array: GcObject, i: u32, value: Value) -> Result<(), VmError> {
  let mut s = scope.reborrow();
  s.push_root(Value::Object(array))?;
  s.push_root(value)?;
  let key = index_key(&mut s, i)?;
  s.define_property(array, key, data_desc(value, true, true, true))?;
  Ok(())
}

fn require_map(scope: &mut Scope<'_>, this: Value) -> Result<GcObject, VmError> {
  let Value::Object(obj) = this else {
    return Err(VmError::TypeError(
      "Map method called on incompatible receiver",
    ));
  };
  let key = marker_key(scope, MAP_DATA)?;
  if scope.heap().object_get_own_property(obj, &key)?.is_none() {
    return Err(VmError::TypeError(
      "Map method called on incompatible receiver",
    ));
  }
  Ok(obj)
}

fn require_set(scope: &mut Scope<'_>, this: Value) -> Result<GcObject, VmError> {
  let Value::Object(obj) = this else {
    return Err(VmError::TypeError(
      "Set method called on incompatible receiver",
    ));
  };
  let key = marker_key(scope, SET_DATA)?;
  if scope.heap().object_get_own_property(obj, &key)?.is_none() {
    return Err(VmError::TypeError(
      "Set method called on incompatible receiver",
    ));
  }
  Ok(obj)
}

fn map_data(scope: &mut Scope<'_>, map: GcObject) -> Result<GcObject, VmError> {
  let key = marker_key(scope, MAP_DATA)?;
  match scope.heap().object_get_own_data_property_value(map, &key)? {
    Some(Value::Object(data)) => Ok(data),
    _ => Err(VmError::InvariantViolation("Map missing [[MapData]]")),
  }
}

fn set_data(scope: &mut Scope<'_>, set: GcObject) -> Result<GcObject, VmError> {
  let key = marker_key(scope, SET_DATA)?;
  match scope.heap().object_get_own_data_property_value(set, &key)? {
    Some(Value::Object(data)) => Ok(data),
    _ => Err(VmError::InvariantViolation("Set missing [[SetData]]")),
  }
}

fn entry_key_value(scope: &mut Scope<'_>, entry: GcObject) -> Result<(Value, Value), VmError> {
  let k = array_get(scope, entry, 0)?;
  let v = array_get(scope, entry, 1)?;
  Ok((k, v))
}

fn install_map_data(scope: &mut Scope<'_>, map: GcObject, data: GcObject) -> Result<(), VmError> {
  let key = marker_key(scope, MAP_DATA)?;
  scope.define_property(map, key, data_desc(Value::Object(data), true, false, false))?;
  Ok(())
}

fn install_set_data(scope: &mut Scope<'_>, set: GcObject, data: GcObject) -> Result<(), VmError> {
  let key = marker_key(scope, SET_DATA)?;
  scope.define_property(set, key, data_desc(Value::Object(data), true, false, false))?;
  Ok(())
}

fn map_find_index(
  scope: &mut Scope<'_>,
  data: GcObject,
  key: Value,
) -> Result<Option<u32>, VmError> {
  let len = array_len(scope, data)?;
  for i in 0..len {
    match array_get(scope, data, i)? {
      Value::Object(entry) => {
        let (ek, _) = entry_key_value(scope, entry)?;
        if same_value_zero(ek, key, scope) {
          return Ok(Some(i));
        }
      }
      _ => {} // empty slot
    }
  }
  Ok(None)
}

fn set_find_index(
  scope: &mut Scope<'_>,
  data: GcObject,
  value: Value,
) -> Result<Option<u32>, VmError> {
  // SetData slots are entry arrays `[value]` (like Map); empty slots are `undefined`.
  let len = array_len(scope, data)?;
  for i in 0..len {
    match array_get(scope, data, i)? {
      Value::Object(entry) => {
        let ev = array_get(scope, entry, 0)?;
        if same_value_zero(ev, value, scope) {
          return Ok(Some(i));
        }
      }
      _ => {}
    }
  }
  Ok(None)
}

fn map_count(scope: &mut Scope<'_>, data: GcObject) -> Result<u32, VmError> {
  let len = array_len(scope, data)?;
  let mut n = 0u32;
  for i in 0..len {
    if matches!(array_get(scope, data, i)?, Value::Object(_)) {
      n = n.saturating_add(1);
    }
  }
  Ok(n)
}

fn set_count(scope: &mut Scope<'_>, data: GcObject) -> Result<u32, VmError> {
  let len = array_len(scope, data)?;
  let mut n = 0u32;
  for i in 0..len {
    if matches!(array_get(scope, data, i)?, Value::Object(_)) {
      n = n.saturating_add(1);
    }
  }
  Ok(n)
}

fn create_set_entry(vm: &mut Vm, scope: &mut Scope<'_>, value: Value) -> Result<GcObject, VmError> {
  let mut s = scope.reborrow();
  s.push_root(value)?;
  let entry = create_array(vm, &mut s, 1)?;
  s.push_root(Value::Object(entry))?;
  array_set(&mut s, entry, 0, value)?;
  Ok(entry)
}

fn create_entry(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  key: Value,
  value: Value,
) -> Result<GcObject, VmError> {
  let mut s = scope.reborrow();
  s.push_root(key)?;
  s.push_root(value)?;
  let entry = create_array(vm, &mut s, 2)?;
  s.push_root(Value::Object(entry))?;
  array_set(&mut s, entry, 0, key)?;
  array_set(&mut s, entry, 1, value)?;
  Ok(entry)
}

/// `Map` call — must be invoked with `new`.
pub fn map_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::TypeError("Constructor Map requires 'new'"))
}

/// `new Map([iterable])` (ECMA-262 §24.1.1.1).
pub fn map_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  // GetPrototypeFromConstructor: when `.prototype` is not an object, use
  // GetFunctionRealm(newTarget)'s %Map.prototype% (not the active realm).
  let default_proto =
    default_proto_from_new_target(vm, scope, new_target, |intr| intr.map_prototype())?;
  let map = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    default_proto,
    &["[[MapData]]"],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(map))?;

  let data = create_array(vm, scope, 0)?;
  scope.push_root(Value::Object(data))?;
  install_map_data(scope, map, data)?;

  let iterable = args.first().copied().unwrap_or(Value::Undefined);
  if matches!(iterable, Value::Undefined | Value::Null) {
    return Ok(Value::Object(map));
  }

  let adder = {
    let key = string_key(scope, "set")?;
    scope.ordinary_get_with_host_and_hooks(vm, host, hooks, map, key, Value::Object(map))?
  };
  if !scope.heap().is_callable(adder)? {
    return Err(VmError::TypeError("Map set is not callable"));
  }
  scope.push_root(adder)?;

  add_entries_from_iterable(vm, scope, host, hooks, Value::Object(map), iterable, adder)?;
  Ok(Value::Object(map))
}

/// `Set` call — must be invoked with `new`.
pub fn set_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::TypeError("Constructor Set requires 'new'"))
}

/// `new Set([iterable])` (ECMA-262 §24.2.1.1).
pub fn set_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let default_proto =
    default_proto_from_new_target(vm, scope, new_target, |intr| intr.set_prototype())?;
  let set = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    default_proto,
    &["[[SetData]]"],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(set))?;

  let data = create_array(vm, scope, 0)?;
  scope.push_root(Value::Object(data))?;
  install_set_data(scope, set, data)?;

  let iterable = args.first().copied().unwrap_or(Value::Undefined);
  if matches!(iterable, Value::Undefined | Value::Null) {
    return Ok(Value::Object(set));
  }

  let adder = {
    let key = string_key(scope, "add")?;
    scope.ordinary_get_with_host_and_hooks(vm, host, hooks, set, key, Value::Object(set))?
  };
  if !scope.heap().is_callable(adder)? {
    return Err(VmError::TypeError("Set add is not callable"));
  }
  scope.push_root(adder)?;

  add_values_from_iterable(vm, scope, host, hooks, Value::Object(set), iterable, adder)?;
  Ok(Value::Object(set))
}

fn add_entries_from_iterable(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  target: Value,
  iterable: Value,
  adder: Value,
) -> Result<(), VmError> {
  let mut iterator_record = crate::iterator::get_iterator(vm, host, hooks, scope, iterable)?;
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  loop {
    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut iterator_record) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
          return Err(err);
        }
      };
    let Some(next_item) = next else {
      return Ok(());
    };

    let Value::Object(item) = next_item else {
      let close_err = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      let typ = VmError::TypeError("Iterator value is not an entry object");
      return match close_err {
        Ok(()) => Err(typ),
        Err(e) => Err(e),
      };
    };
    scope.push_root(Value::Object(item))?;

    let key0 = string_key(scope, "0")?;
    let k = match scope.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      item,
      key0,
      Value::Object(item),
    ) {
      Ok(v) => v,
      Err(err) => {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
        return Err(err);
      }
    };
    scope.push_root(k)?;
    let key1 = string_key(scope, "1")?;
    let v = match scope.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      item,
      key1,
      Value::Object(item),
    ) {
      Ok(v) => v,
      Err(err) => {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
        return Err(err);
      }
    };

    if let Err(err) = vm.call_with_host_and_hooks(host, scope, hooks, adder, target, &[k, v]) {
      let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      return Err(err);
    }
  }
}

fn add_values_from_iterable(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  target: Value,
  iterable: Value,
  adder: Value,
) -> Result<(), VmError> {
  let mut iterator_record = crate::iterator::get_iterator(vm, host, hooks, scope, iterable)?;
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  loop {
    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut iterator_record) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
          return Err(err);
        }
      };
    let Some(next_value) = next else {
      return Ok(());
    };
    if let Err(err) = vm.call_with_host_and_hooks(host, scope, hooks, adder, target, &[next_value])
    {
      let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      return Err(err);
    }
  }
}

pub fn map_prototype_set(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let mut key = args.first().copied().unwrap_or(Value::Undefined);
  let value = args.get(1).copied().unwrap_or(Value::Undefined);
  // Canonicalize -0 to +0 (SameValueZero / Map.set step).
  if let Value::Number(n) = key {
    if n == 0.0 {
      key = Value::Number(0.0);
    }
  }
  scope.push_root(key)?;
  scope.push_root(value)?;

  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;

  if let Some(i) = map_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("Map entry missing")),
    };
    scope.push_root(Value::Object(entry))?;
    array_set(scope, entry, 1, value)?;
    return Ok(Value::Object(map));
  }

  let entry = create_entry(vm, scope, key, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(Value::Object(map))
}

pub fn map_prototype_get(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  let data = map_data(scope, map)?;
  if let Some(i) = map_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Ok(Value::Undefined),
    };
    let (_, v) = entry_key_value(scope, entry)?;
    return Ok(v);
  }
  Ok(Value::Undefined)
}

pub fn map_prototype_has(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  let data = map_data(scope, map)?;
  Ok(Value::Bool(map_find_index(scope, data, key)?.is_some()))
}

pub fn map_prototype_delete(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = map_find_index(scope, data, key)? {
    array_set(scope, data, i, Value::Undefined)?;
    return Ok(Value::Bool(true));
  }
  Ok(Value::Bool(false))
}

pub fn map_prototype_clear(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  let len = array_len(scope, data)?;
  for i in 0..len {
    array_set(scope, data, i, Value::Undefined)?;
  }
  Ok(Value::Undefined)
}

pub fn map_prototype_size_get(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  let data = map_data(scope, map)?;
  Ok(Value::Number(map_count(scope, data)? as f64))
}

fn create_empty_map(vm: &mut Vm, scope: &mut Scope<'_>) -> Result<GcObject, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let map = scope.alloc_object_with_prototype(Some(intr.map_prototype()))?;
  scope.push_root(Value::Object(map))?;
  let data = create_array(vm, scope, 0)?;
  scope.push_root(Value::Object(data))?;
  install_map_data(scope, map, data)?;
  Ok(map)
}

/// `AddValueToKeyedGroup` (ECMA-262 §7.3.34) against a Map used as the groups list.
fn map_add_value_to_keyed_group(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  map: GcObject,
  key: Value,
  value: Value,
) -> Result<(), VmError> {
  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = map_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("Map group entry missing")),
    };
    scope.push_root(Value::Object(entry))?;
    let elements = match array_get(scope, entry, 1)? {
      Value::Object(arr) => arr,
      _ => return Err(VmError::InvariantViolation("Map group elements missing")),
    };
    scope.push_root(Value::Object(elements))?;
    let len = array_len(scope, elements)?;
    array_set(scope, elements, len, value)?;
    return Ok(());
  }
  let elements = create_array(vm, scope, 1)?;
  scope.push_root(Value::Object(elements))?;
  array_set(scope, elements, 0, value)?;
  let entry = create_entry(vm, scope, key, Value::Object(elements))?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(())
}

/// `GroupBy(items, callback, ~collection~)` (ECMA-262 §7.3.35), returning a Map
/// whose values are the per-key element arrays.
fn group_by_collection(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  items: Value,
  callback: Value,
) -> Result<GcObject, VmError> {
  // RequireObjectCoercible(items)
  if matches!(items, Value::Undefined | Value::Null) {
    return Err(VmError::TypeError("Map.groupBy items is null or undefined"));
  }
  if !scope.heap().is_callable(callback)? {
    return Err(VmError::TypeError("Map.groupBy callback is not callable"));
  }
  scope.push_root(items)?;
  scope.push_root(callback)?;

  let map = create_empty_map(vm, scope)?;
  scope.push_root(Value::Object(map))?;

  let mut iterator_record = crate::iterator::get_iterator(vm, host, hooks, scope, items)?;
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  let mut k: u64 = 0;
  loop {
    // 2^53 - 1
    if k >= 9_007_199_254_740_991 {
      let typ = VmError::TypeError("Map.groupBy iterable too large");
      let close_err = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      return match close_err {
        Ok(()) => Err(typ),
        Err(e) => Err(e),
      };
    }

    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut iterator_record) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
          return Err(err);
        }
      };
    let Some(value) = next else {
      return Ok(map);
    };
    scope.push_root(value)?;

    let key = match vm.call_with_host_and_hooks(
      host,
      scope,
      hooks,
      callback,
      Value::Undefined,
      &[value, Value::Number(k as f64)],
    ) {
      Ok(v) => v,
      Err(err) => {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
        return Err(err);
      }
    };
    let key = canonicalize_keyed_collection_key(key);
    scope.push_root(key)?;
    scope.push_root(value)?;
    map_add_value_to_keyed_group(vm, scope, map, key, value)?;
    k = k.saturating_add(1);
  }
}

/// `Map.groupBy(items, callback)` (ECMA-262 §24.1.2.1).
pub fn map_group_by(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let items = args.first().copied().unwrap_or(Value::Undefined);
  let callback = args.get(1).copied().unwrap_or(Value::Undefined);
  let map = group_by_collection(vm, scope, host, hooks, items, callback)?;
  Ok(Value::Object(map))
}

/// `Map.prototype.getOrInsert(key, value)` (ECMA-262 §24.1.3.7).
pub fn map_prototype_get_or_insert(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = canonicalize_keyed_collection_key(args.first().copied().unwrap_or(Value::Undefined));
  let value = args.get(1).copied().unwrap_or(Value::Undefined);
  scope.push_root(key)?;
  scope.push_root(value)?;

  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = map_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("Map entry missing")),
    };
    let (_, existing) = entry_key_value(scope, entry)?;
    return Ok(existing);
  }

  let entry = create_entry(vm, scope, key, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(value)
}

/// `Map.prototype.getOrInsertComputed(key, callback)` (ECMA-262 §24.1.3.8).
pub fn map_prototype_get_or_insert_computed(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let callback = args.get(1).copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(callback)? {
    return Err(VmError::TypeError(
      "Map.prototype.getOrInsertComputed callback is not callable",
    ));
  }
  scope.push_root(callback)?;
  let key = canonicalize_keyed_collection_key(args.first().copied().unwrap_or(Value::Undefined));
  scope.push_root(key)?;

  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = map_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("Map entry missing")),
    };
    let (_, existing) = entry_key_value(scope, entry)?;
    return Ok(existing);
  }

  let value =
    vm.call_with_host_and_hooks(host, scope, hooks, callback, Value::Undefined, &[key])?;
  scope.push_root(value)?;
  // NOTE: The Map may have been modified during execution of callback.
  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = map_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("Map entry missing")),
    };
    scope.push_root(Value::Object(entry))?;
    array_set(scope, entry, 1, value)?;
    return Ok(value);
  }

  let entry = create_entry(vm, scope, key, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(value)
}

pub fn set_prototype_add(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let mut value = args.first().copied().unwrap_or(Value::Undefined);
  if let Value::Number(n) = value {
    if n == 0.0 {
      value = Value::Number(0.0);
    }
  }
  scope.push_root(value)?;
  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;

  if set_find_index(scope, data, value)?.is_some() {
    return Ok(Value::Object(set));
  }
  let entry = create_set_entry(vm, scope, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(Value::Object(set))
}

pub fn set_prototype_has(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let data = set_data(scope, set)?;
  Ok(Value::Bool(set_find_index(scope, data, value)?.is_some()))
}

pub fn set_prototype_delete(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = set_find_index(scope, data, value)? {
    array_set(scope, data, i, Value::Undefined)?;
    return Ok(Value::Bool(true));
  }
  Ok(Value::Bool(false))
}

pub fn set_prototype_clear(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  let len = array_len(scope, data)?;
  for i in 0..len {
    array_set(scope, data, i, Value::Undefined)?;
  }
  Ok(Value::Undefined)
}

pub fn set_prototype_size_get(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  let data = set_data(scope, set)?;
  Ok(Value::Number(set_count(scope, data)? as f64))
}

fn create_map_iterator(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  map: GcObject,
  kind: f64,
) -> Result<Value, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let mut s = scope.reborrow();
  s.push_root(Value::Object(map))?;
  let iter = s.alloc_object_with_prototype(Some(intr.map_iterator_prototype()))?;
  s.push_root(Value::Object(iter))?;
  let marker = marker_key(&mut s, MAP_ITER_MARKER)?;
  let map_key = marker_key(&mut s, MAP_ITER_MAP)?;
  let index_key = marker_key(&mut s, MAP_ITER_INDEX)?;
  let kind_key = marker_key(&mut s, MAP_ITER_KIND)?;

  s.define_property(
    iter,
    marker,
    data_desc(Value::Bool(true), false, false, false),
  )?;
  s.define_property(
    iter,
    map_key,
    data_desc(Value::Object(map), true, false, false),
  )?;
  s.define_property(
    iter,
    index_key,
    data_desc(Value::Number(0.0), true, false, false),
  )?;
  s.define_property(
    iter,
    kind_key,
    data_desc(Value::Number(kind), false, false, false),
  )?;
  Ok(Value::Object(iter))
}

fn create_set_iterator(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  set: GcObject,
  kind: f64,
) -> Result<Value, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let mut s = scope.reborrow();
  s.push_root(Value::Object(set))?;
  let iter = s.alloc_object_with_prototype(Some(intr.set_iterator_prototype()))?;
  s.push_root(Value::Object(iter))?;
  let marker = marker_key(&mut s, SET_ITER_MARKER)?;
  let set_key = marker_key(&mut s, SET_ITER_SET)?;
  let index_key = marker_key(&mut s, SET_ITER_INDEX)?;
  let kind_key = marker_key(&mut s, SET_ITER_KIND)?;

  s.define_property(
    iter,
    marker,
    data_desc(Value::Bool(true), false, false, false),
  )?;
  s.define_property(
    iter,
    set_key,
    data_desc(Value::Object(set), true, false, false),
  )?;
  s.define_property(
    iter,
    index_key,
    data_desc(Value::Number(0.0), true, false, false),
  )?;
  s.define_property(
    iter,
    kind_key,
    data_desc(Value::Number(kind), false, false, false),
  )?;
  Ok(Value::Object(iter))
}

pub fn map_prototype_keys(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  create_map_iterator(vm, scope, map, KIND_KEY)
}

pub fn map_prototype_values(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  create_map_iterator(vm, scope, map, KIND_VALUE)
}

pub fn map_prototype_entries(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  create_map_iterator(vm, scope, map, KIND_ENTRY)
}

pub fn set_prototype_values(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  create_set_iterator(vm, scope, set, KIND_VALUE)
}

pub fn set_prototype_entries(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  create_set_iterator(vm, scope, set, KIND_ENTRY)
}

pub fn map_prototype_for_each(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_map(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let callback = args.first().copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(callback)? {
    return Err(VmError::TypeError(
      "Map.prototype.forEach callback is not callable",
    ));
  }
  scope.push_root(callback)?;
  let this_arg = args.get(1).copied().unwrap_or(Value::Undefined);
  scope.push_root(this_arg)?;

  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  let mut i = 0u32;
  loop {
    let len = array_len(scope, data)?;
    if i >= len {
      break;
    }
    if let Value::Object(entry) = array_get(scope, data, i)? {
      let (k, v) = entry_key_value(scope, entry)?;
      scope.push_root(k)?;
      scope.push_root(v)?;
      // callback(value, key, map)
      vm.call_with_host_and_hooks(
        host,
        scope,
        hooks,
        callback,
        this_arg,
        &[v, k, Value::Object(map)],
      )?;
    }
    i = i.saturating_add(1);
  }
  Ok(Value::Undefined)
}

pub fn set_prototype_for_each(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let callback = args.first().copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(callback)? {
    return Err(VmError::TypeError(
      "Set.prototype.forEach callback is not callable",
    ));
  }
  scope.push_root(callback)?;
  let this_arg = args.get(1).copied().unwrap_or(Value::Undefined);
  scope.push_root(this_arg)?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  let mut i = 0u32;
  loop {
    let len = array_len(scope, data)?;
    if i >= len {
      break;
    }
    if let Value::Object(entry) = array_get(scope, data, i)? {
      let v = array_get(scope, entry, 0)?;
      scope.push_root(v)?;
      // callback(value, value, set)
      vm.call_with_host_and_hooks(
        host,
        scope,
        hooks,
        callback,
        this_arg,
        &[v, v, Value::Object(set)],
      )?;
    }
    i = i.saturating_add(1);
  }
  Ok(Value::Undefined)
}

// --- Set composition methods (ECMA-262 §24.2.4.5 / .9–.12 / .15–.16) ---

/// `CanonicalizeKeyedCollectionKey` (ECMA-262 §24.5.1): `-0` → `+0`.
fn to_integer_or_infinity(n: f64) -> f64 {
  if n.is_nan() {
    0.0
  } else if n.is_infinite() {
    n
  } else {
    let t = n.trunc();
    if t == 0.0 {
      0.0
    } else {
      t
    }
  }
}

struct SetRecord {
  set_object: Value,
  size: f64,
  has: Value,
  keys: Value,
}

fn throw_type(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> VmError {
  let Some(intr) = vm.intrinsics() else {
    return VmError::Unimplemented("intrinsics not initialized");
  };
  crate::error_object::throw_type_error(scope, intr, message)
}

fn throw_range(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> VmError {
  let Some(intr) = vm.intrinsics() else {
    return VmError::Unimplemented("intrinsics not initialized");
  };
  crate::error_object::throw_range_error(scope, intr, message)
}

/// `GetSetRecord` (ECMA-262 §24.2.1.2).
fn get_set_record(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  obj: Value,
) -> Result<SetRecord, VmError> {
  let Value::Object(obj_gc) = obj else {
    return Err(throw_type(
      vm,
      scope,
      "GetSetRecord: argument is not an object",
    ));
  };
  scope.push_root(obj)?;

  let size_key = string_key(scope, "size")?;
  let raw_size = scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj_gc, size_key, obj)?;
  scope.push_root(raw_size)?;
  let number_size = crate::spec_ops::to_number(vm, scope, raw_size)?;
  if number_size.is_nan() {
    return Err(throw_type(vm, scope, "GetSetRecord: size is NaN"));
  }
  let int_size = to_integer_or_infinity(number_size);
  if int_size < 0.0 {
    return Err(throw_range(vm, scope, "GetSetRecord: size is negative"));
  }

  let has_key = string_key(scope, "has")?;
  let has = scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj_gc, has_key, obj)?;
  scope.push_root(has)?;
  if !scope.heap().is_callable(has)? {
    return Err(throw_type(vm, scope, "GetSetRecord: has is not callable"));
  }

  let keys_key = string_key(scope, "keys")?;
  let keys = scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj_gc, keys_key, obj)?;
  scope.push_root(keys)?;
  if !scope.heap().is_callable(keys)? {
    return Err(throw_type(vm, scope, "GetSetRecord: keys is not callable"));
  }

  Ok(SetRecord {
    set_object: obj,
    size: int_size,
    has,
    keys,
  })
}

fn set_entry_value(scope: &mut Scope<'_>, entry: GcObject) -> Result<Value, VmError> {
  array_get(scope, entry, 0)
}

fn copy_set_data(vm: &mut Vm, scope: &mut Scope<'_>, data: GcObject) -> Result<GcObject, VmError> {
  let len = array_len(scope, data)?;
  let copy = create_array(vm, scope, len)?;
  scope.push_root(Value::Object(copy))?;
  for i in 0..len {
    let slot = array_get(scope, data, i)?;
    array_set(scope, copy, i, slot)?;
  }
  Ok(copy)
}

fn create_set_from_data(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  data: GcObject,
) -> Result<Value, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let set = scope.alloc_object_with_prototype(Some(intr.set_prototype()))?;
  scope.push_root(Value::Object(set))?;
  scope.push_root(Value::Object(data))?;
  install_set_data(scope, set, data)?;
  Ok(Value::Object(set))
}

fn set_data_append(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  data: GcObject,
  value: Value,
) -> Result<(), VmError> {
  let value = canonicalize_keyed_collection_key(value);
  scope.push_root(value)?;
  if set_find_index(scope, data, value)?.is_some() {
    return Ok(());
  }
  let entry = create_set_entry(vm, scope, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(())
}

fn call_has(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  record: &SetRecord,
  value: Value,
) -> Result<bool, VmError> {
  let result =
    vm.call_with_host_and_hooks(host, scope, hooks, record.has, record.set_object, &[value])?;
  scope.heap().to_boolean(result)
}

/// `Set.prototype.union` (ECMA-262 §24.2.4.16).
pub fn set_prototype_union(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let mut keys_iterator = crate::iterator::get_iterator_from_method(
    vm,
    host,
    hooks,
    scope,
    other_record.set_object,
    other_record.keys,
  )?;
  scope.push_roots(&[keys_iterator.iterator, keys_iterator.next_method])?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  let result_data = copy_set_data(vm, scope, data)?;
  scope.push_root(Value::Object(result_data))?;

  loop {
    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut keys_iterator) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator);
          return Err(err);
        }
      };
    let Some(next) = next else {
      break;
    };
    let next = canonicalize_keyed_collection_key(next);
    scope.push_root(next)?;
    if set_find_index(scope, result_data, next)?.is_none() {
      set_data_append(vm, scope, result_data, next)?;
    }
  }

  create_set_from_data(vm, scope, result_data)
}

/// `Set.prototype.intersection` (ECMA-262 §24.2.4.9).
pub fn set_prototype_intersection(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  let result_data = create_array(vm, scope, 0)?;
  scope.push_root(Value::Object(result_data))?;

  let this_size = set_count(scope, data)? as f64;
  if this_size <= other_record.size {
    let mut index = 0u32;
    loop {
      let this_len = array_len(scope, data)?;
      if index >= this_len {
        break;
      }
      let slot = array_get(scope, data, index)?;
      index = index.saturating_add(1);
      if let Value::Object(entry) = slot {
        let entry_val = set_entry_value(scope, entry)?;
        scope.push_root(entry_val)?;
        if call_has(vm, scope, host, hooks, &other_record, entry_val)?
          && set_find_index(scope, result_data, entry_val)?.is_none()
        {
          set_data_append(vm, scope, result_data, entry_val)?;
        }
      }
    }
  } else {
    let mut keys_iterator = crate::iterator::get_iterator_from_method(
      vm,
      host,
      hooks,
      scope,
      other_record.set_object,
      other_record.keys,
    )?;
    scope.push_roots(&[keys_iterator.iterator, keys_iterator.next_method])?;
    loop {
      let next =
        match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut keys_iterator) {
          Ok(v) => v,
          Err(err) => {
            let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator);
            return Err(err);
          }
        };
      let Some(next) = next else {
        break;
      };
      let next = canonicalize_keyed_collection_key(next);
      scope.push_root(next)?;
      if set_find_index(scope, data, next)?.is_some()
        && set_find_index(scope, result_data, next)?.is_none()
      {
        set_data_append(vm, scope, result_data, next)?;
      }
    }
  }

  create_set_from_data(vm, scope, result_data)
}

/// `Set.prototype.difference` (ECMA-262 §24.2.4.5).
pub fn set_prototype_difference(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  let result_data = copy_set_data(vm, scope, data)?;
  scope.push_root(Value::Object(result_data))?;

  let this_size = set_count(scope, data)? as f64;
  if this_size <= other_record.size {
    let this_len = array_len(scope, data)?;
    let mut index = 0u32;
    while index < this_len {
      if let Value::Object(entry) = array_get(scope, result_data, index)? {
        let entry_val = set_entry_value(scope, entry)?;
        scope.push_root(entry_val)?;
        if call_has(vm, scope, host, hooks, &other_record, entry_val)? {
          array_set(scope, result_data, index, Value::Undefined)?;
        }
      }
      index = index.saturating_add(1);
    }
  } else {
    let mut keys_iterator = crate::iterator::get_iterator_from_method(
      vm,
      host,
      hooks,
      scope,
      other_record.set_object,
      other_record.keys,
    )?;
    scope.push_roots(&[keys_iterator.iterator, keys_iterator.next_method])?;
    loop {
      let next =
        match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut keys_iterator) {
          Ok(v) => v,
          Err(err) => {
            let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator);
            return Err(err);
          }
        };
      let Some(next) = next else {
        break;
      };
      let next = canonicalize_keyed_collection_key(next);
      scope.push_root(next)?;
      if let Some(value_index) = set_find_index(scope, result_data, next)? {
        array_set(scope, result_data, value_index, Value::Undefined)?;
      }
    }
  }

  create_set_from_data(vm, scope, result_data)
}

/// `Set.prototype.symmetricDifference` (ECMA-262 §24.2.4.15).
pub fn set_prototype_symmetric_difference(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let mut keys_iterator = crate::iterator::get_iterator_from_method(
    vm,
    host,
    hooks,
    scope,
    other_record.set_object,
    other_record.keys,
  )?;
  scope.push_roots(&[keys_iterator.iterator, keys_iterator.next_method])?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  let result_data = copy_set_data(vm, scope, data)?;
  scope.push_root(Value::Object(result_data))?;

  loop {
    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut keys_iterator) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator);
          return Err(err);
        }
      };
    let Some(next) = next else {
      break;
    };
    let next = canonicalize_keyed_collection_key(next);
    scope.push_root(next)?;
    let result_index = set_find_index(scope, result_data, next)?;
    let already_in_result = result_index.is_some();
    let in_this = set_find_index(scope, data, next)?.is_some();
    if in_this {
      if already_in_result {
        if let Some(i) = result_index {
          array_set(scope, result_data, i, Value::Undefined)?;
        }
      }
    } else if !already_in_result {
      set_data_append(vm, scope, result_data, next)?;
    }
  }

  create_set_from_data(vm, scope, result_data)
}

/// `Set.prototype.isDisjointFrom` (ECMA-262 §24.2.4.10).
pub fn set_prototype_is_disjoint_from(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;

  let this_size = set_count(scope, data)? as f64;
  if this_size <= other_record.size {
    let mut index = 0u32;
    loop {
      let this_len = array_len(scope, data)?;
      if index >= this_len {
        break;
      }
      let slot = array_get(scope, data, index)?;
      index = index.saturating_add(1);
      if let Value::Object(entry) = slot {
        let entry_val = set_entry_value(scope, entry)?;
        scope.push_root(entry_val)?;
        if call_has(vm, scope, host, hooks, &other_record, entry_val)? {
          return Ok(Value::Bool(false));
        }
      }
    }
  } else {
    let mut keys_iterator = crate::iterator::get_iterator_from_method(
      vm,
      host,
      hooks,
      scope,
      other_record.set_object,
      other_record.keys,
    )?;
    scope.push_roots(&[keys_iterator.iterator, keys_iterator.next_method])?;
    loop {
      let next =
        match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut keys_iterator) {
          Ok(v) => v,
          Err(err) => {
            let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator);
            return Err(err);
          }
        };
      let Some(next) = next else {
        break;
      };
      scope.push_root(next)?;
      if set_find_index(scope, data, next)?.is_some() {
        crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator)?;
        return Ok(Value::Bool(false));
      }
    }
  }

  Ok(Value::Bool(true))
}

/// `Set.prototype.isSubsetOf` (ECMA-262 §24.2.4.11).
pub fn set_prototype_is_subset_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  if (set_count(scope, data)? as f64) > other_record.size {
    return Ok(Value::Bool(false));
  }

  let mut index = 0u32;
  loop {
    let this_len = array_len(scope, data)?;
    if index >= this_len {
      break;
    }
    let slot = array_get(scope, data, index)?;
    index = index.saturating_add(1);
    if let Value::Object(entry) = slot {
      let entry_val = set_entry_value(scope, entry)?;
      scope.push_root(entry_val)?;
      if !call_has(vm, scope, host, hooks, &other_record, entry_val)? {
        return Ok(Value::Bool(false));
      }
    }
  }

  Ok(Value::Bool(true))
}

/// `Set.prototype.isSupersetOf` (ECMA-262 §24.2.4.12).
pub fn set_prototype_is_superset_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_set(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let other = args.first().copied().unwrap_or(Value::Undefined);
  let other_record = get_set_record(vm, scope, host, hooks, other)?;
  scope.push_root(other_record.set_object)?;
  scope.push_root(other_record.has)?;
  scope.push_root(other_record.keys)?;

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  if (set_count(scope, data)? as f64) < other_record.size {
    return Ok(Value::Bool(false));
  }

  let mut keys_iterator = crate::iterator::get_iterator_from_method(
    vm,
    host,
    hooks,
    scope,
    other_record.set_object,
    other_record.keys,
  )?;
  scope.push_roots(&[keys_iterator.iterator, keys_iterator.next_method])?;
  loop {
    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut keys_iterator) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator);
          return Err(err);
        }
      };
    let Some(next) = next else {
      break;
    };
    scope.push_root(next)?;
    if set_find_index(scope, data, next)?.is_none() {
      crate::iterator::iterator_close(vm, host, hooks, scope, &keys_iterator)?;
      return Ok(Value::Bool(false));
    }
  }

  Ok(Value::Bool(true))
}

pub fn map_iterator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Err(VmError::TypeError(
      "Map Iterator.prototype.next called on non-object",
    ));
  };
  scope.push_root(Value::Object(this_obj))?;
  let marker = marker_key(scope, MAP_ITER_MARKER)?;
  if scope
    .heap()
    .object_get_own_data_property_value(this_obj, &marker)?
    .is_none()
  {
    return Err(VmError::TypeError(
      "Map Iterator.prototype.next called on incompatible receiver",
    ));
  }

  let map_key = marker_key(scope, MAP_ITER_MAP)?;
  let index_key = marker_key(scope, MAP_ITER_INDEX)?;
  let kind_key = marker_key(scope, MAP_ITER_KIND)?;

  let map = match scope
    .heap()
    .object_get_own_data_property_value(this_obj, &map_key)?
  {
    Some(Value::Object(m)) => m,
    Some(Value::Undefined) | None => {
      return crate::generator::create_iter_result_object(vm, scope, Value::Undefined, true);
    }
    _ => {
      return Err(VmError::InvariantViolation("MapIterator missing map"));
    }
  };
  scope.push_root(Value::Object(map))?;
  let kind = match scope
    .heap()
    .object_get_own_data_property_value(this_obj, &kind_key)?
  {
    Some(Value::Number(n)) => n,
    _ => KIND_ENTRY,
  };
  let mut index = match scope
    .heap()
    .object_get_own_data_property_value(this_obj, &index_key)?
  {
    Some(Value::Number(n)) if n.is_finite() && n >= 0.0 => n as u32,
    _ => 0,
  };

  let data = map_data(scope, map)?;
  scope.push_root(Value::Object(data))?;

  loop {
    let len = array_len(scope, data)?;
    if index >= len {
      scope.define_property(
        this_obj,
        map_key,
        data_desc(Value::Undefined, true, false, false),
      )?;
      return crate::generator::create_iter_result_object(vm, scope, Value::Undefined, true);
    }
    let slot = array_get(scope, data, index)?;
    index = index.saturating_add(1);
    scope.define_property(
      this_obj,
      index_key,
      data_desc(Value::Number(index as f64), true, false, false),
    )?;
    let Value::Object(entry) = slot else {
      continue;
    };
    let (k, v) = entry_key_value(scope, entry)?;
    let result_value = if (kind - KIND_KEY).abs() < f64::EPSILON {
      k
    } else if (kind - KIND_VALUE).abs() < f64::EPSILON {
      v
    } else {
      let pair = create_array(vm, scope, 2)?;
      scope.push_root(Value::Object(pair))?;
      array_set(scope, pair, 0, k)?;
      array_set(scope, pair, 1, v)?;
      Value::Object(pair)
    };
    return crate::generator::create_iter_result_object(vm, scope, result_value, false);
  }
}

pub fn set_iterator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Err(VmError::TypeError(
      "Set Iterator.prototype.next called on non-object",
    ));
  };
  scope.push_root(Value::Object(this_obj))?;
  let marker = marker_key(scope, SET_ITER_MARKER)?;
  if scope
    .heap()
    .object_get_own_data_property_value(this_obj, &marker)?
    .is_none()
  {
    return Err(VmError::TypeError(
      "Set Iterator.prototype.next called on incompatible receiver",
    ));
  }

  let set_key = marker_key(scope, SET_ITER_SET)?;
  let index_key = marker_key(scope, SET_ITER_INDEX)?;
  let kind_key = marker_key(scope, SET_ITER_KIND)?;

  let set = match scope
    .heap()
    .object_get_own_data_property_value(this_obj, &set_key)?
  {
    Some(Value::Object(s)) => s,
    Some(Value::Undefined) | None => {
      return crate::generator::create_iter_result_object(vm, scope, Value::Undefined, true);
    }
    _ => {
      return Err(VmError::InvariantViolation("SetIterator missing set"));
    }
  };
  scope.push_root(Value::Object(set))?;
  let kind = match scope
    .heap()
    .object_get_own_data_property_value(this_obj, &kind_key)?
  {
    Some(Value::Number(n)) => n,
    _ => KIND_VALUE,
  };
  let mut index = match scope
    .heap()
    .object_get_own_data_property_value(this_obj, &index_key)?
  {
    Some(Value::Number(n)) if n.is_finite() && n >= 0.0 => n as u32,
    _ => 0,
  };

  let data = set_data(scope, set)?;
  scope.push_root(Value::Object(data))?;

  loop {
    let len = array_len(scope, data)?;
    if index >= len {
      scope.define_property(
        this_obj,
        set_key,
        data_desc(Value::Undefined, true, false, false),
      )?;
      return crate::generator::create_iter_result_object(vm, scope, Value::Undefined, true);
    }
    let slot = array_get(scope, data, index)?;
    index = index.saturating_add(1);
    scope.define_property(
      this_obj,
      index_key,
      data_desc(Value::Number(index as f64), true, false, false),
    )?;
    let Value::Object(entry) = slot else {
      continue;
    };
    let v = array_get(scope, entry, 0)?;
    let result_value = if (kind - KIND_ENTRY).abs() < f64::EPSILON {
      let pair = create_array(vm, scope, 2)?;
      scope.push_root(Value::Object(pair))?;
      array_set(scope, pair, 0, v)?;
      array_set(scope, pair, 1, v)?;
      Value::Object(pair)
    } else {
      v
    };
    return crate::generator::create_iter_result_object(vm, scope, result_value, false);
  }
}

/// `get Map [ @@species ]` / `get Set [ @@species ]` — returns the receiver.
pub fn species_get(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(this)
}

/// `%WeakMap%` / `%WeakSet%` — object/unregistered-symbol keys, get/set/has/delete.
///
/// Entries are stored strongly (ordinary arrays) for now; true weak GC edges are deferred.
/// `CanBeHeldWeakly` matches the spec (Objects + unregistered Symbols).
const WEAKMAP_DATA: &str = "vm-js.internal.WeakMapData";
const WEAKSET_DATA: &str = "vm-js.internal.WeakSetData";

fn require_weakmap(scope: &mut Scope<'_>, this: Value) -> Result<GcObject, VmError> {
  let Value::Object(obj) = this else {
    return Err(VmError::TypeError(
      "WeakMap method called on incompatible receiver",
    ));
  };
  let key = marker_key(scope, WEAKMAP_DATA)?;
  if scope.heap().object_get_own_property(obj, &key)?.is_none() {
    return Err(VmError::TypeError(
      "WeakMap method called on incompatible receiver",
    ));
  }
  Ok(obj)
}

fn require_weakset(scope: &mut Scope<'_>, this: Value) -> Result<GcObject, VmError> {
  let Value::Object(obj) = this else {
    return Err(VmError::TypeError(
      "WeakSet method called on incompatible receiver",
    ));
  };
  let key = marker_key(scope, WEAKSET_DATA)?;
  if scope.heap().object_get_own_property(obj, &key)?.is_none() {
    return Err(VmError::TypeError(
      "WeakSet method called on incompatible receiver",
    ));
  }
  Ok(obj)
}

fn weakmap_data(scope: &mut Scope<'_>, map: GcObject) -> Result<GcObject, VmError> {
  let key = marker_key(scope, WEAKMAP_DATA)?;
  match scope.heap().object_get_own_data_property_value(map, &key)? {
    Some(Value::Object(data)) => Ok(data),
    _ => Err(VmError::InvariantViolation(
      "WeakMap missing [[WeakMapData]]",
    )),
  }
}

fn weakset_data(scope: &mut Scope<'_>, set: GcObject) -> Result<GcObject, VmError> {
  let key = marker_key(scope, WEAKSET_DATA)?;
  match scope.heap().object_get_own_data_property_value(set, &key)? {
    Some(Value::Object(data)) => Ok(data),
    _ => Err(VmError::InvariantViolation(
      "WeakSet missing [[WeakSetData]]",
    )),
  }
}

fn install_weakmap_data(
  scope: &mut Scope<'_>,
  map: GcObject,
  data: GcObject,
) -> Result<(), VmError> {
  let key = marker_key(scope, WEAKMAP_DATA)?;
  scope.define_property(map, key, data_desc(Value::Object(data), true, false, false))?;
  Ok(())
}

fn install_weakset_data(
  scope: &mut Scope<'_>,
  set: GcObject,
  data: GcObject,
) -> Result<(), VmError> {
  let key = marker_key(scope, WEAKSET_DATA)?;
  scope.define_property(set, key, data_desc(Value::Object(data), true, false, false))?;
  Ok(())
}

fn weakmap_find_index(
  scope: &mut Scope<'_>,
  data: GcObject,
  key: Value,
) -> Result<Option<u32>, VmError> {
  let len = array_len(scope, data)?;
  for i in 0..len {
    match array_get(scope, data, i)? {
      Value::Object(entry) => {
        let (ek, _) = entry_key_value(scope, entry)?;
        if same_value(ek, key, scope) {
          return Ok(Some(i));
        }
      }
      _ => {}
    }
  }
  Ok(None)
}

fn weakset_find_index(
  scope: &mut Scope<'_>,
  data: GcObject,
  value: Value,
) -> Result<Option<u32>, VmError> {
  let len = array_len(scope, data)?;
  for i in 0..len {
    match array_get(scope, data, i)? {
      Value::Object(entry) => {
        let ev = array_get(scope, entry, 0)?;
        if same_value(ev, value, scope) {
          return Ok(Some(i));
        }
      }
      _ => {}
    }
  }
  Ok(None)
}

pub fn weakmap_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::TypeError("Constructor WeakMap requires 'new'"))
}

pub fn weakmap_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let default_proto =
    default_proto_from_new_target(vm, scope, new_target, |intr| intr.weakmap_prototype())?;
  let map = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    default_proto,
    &["[[WeakMapData]]"],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(map))?;

  let data = create_array(vm, scope, 0)?;
  scope.push_root(Value::Object(data))?;
  install_weakmap_data(scope, map, data)?;

  let iterable = args.first().copied().unwrap_or(Value::Undefined);
  if matches!(iterable, Value::Undefined | Value::Null) {
    return Ok(Value::Object(map));
  }

  let adder = {
    let key = string_key(scope, "set")?;
    scope.ordinary_get_with_host_and_hooks(vm, host, hooks, map, key, Value::Object(map))?
  };
  if !scope.heap().is_callable(adder)? {
    return Err(VmError::TypeError("WeakMap set is not callable"));
  }
  scope.push_root(adder)?;
  add_entries_from_iterable(vm, scope, host, hooks, Value::Object(map), iterable, adder)?;
  Ok(Value::Object(map))
}

pub fn weakmap_prototype_set(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_weakmap(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  let value = args.get(1).copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, key)? {
    return Err(VmError::TypeError(
      "WeakMap key must be an Object or unregistered Symbol",
    ));
  }
  scope.push_root(key)?;
  scope.push_root(value)?;

  let data = weakmap_data(scope, map)?;
  scope.push_root(Value::Object(data))?;

  if let Some(i) = weakmap_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("WeakMap entry missing")),
    };
    scope.push_root(Value::Object(entry))?;
    array_set(scope, entry, 1, value)?;
    return Ok(Value::Object(map));
  }

  let entry = create_entry(vm, scope, key, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(Value::Object(map))
}

pub fn weakmap_prototype_get(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_weakmap(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, key)? {
    return Ok(Value::Undefined);
  }
  let data = weakmap_data(scope, map)?;
  if let Some(i) = weakmap_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Ok(Value::Undefined),
    };
    let (_, v) = entry_key_value(scope, entry)?;
    return Ok(v);
  }
  Ok(Value::Undefined)
}

pub fn weakmap_prototype_has(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_weakmap(scope, this)?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, key)? {
    return Ok(Value::Bool(false));
  }
  let data = weakmap_data(scope, map)?;
  Ok(Value::Bool(weakmap_find_index(scope, data, key)?.is_some()))
}

pub fn weakmap_prototype_delete(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_weakmap(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, key)? {
    return Ok(Value::Bool(false));
  }
  let data = weakmap_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = weakmap_find_index(scope, data, key)? {
    array_set(scope, data, i, Value::Undefined)?;
    return Ok(Value::Bool(true));
  }
  Ok(Value::Bool(false))
}

/// `WeakMap.prototype.getOrInsert(key, value)` (ECMA-262 §24.3.3.4).
pub fn weakmap_prototype_get_or_insert(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_weakmap(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  let value = args.get(1).copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, key)? {
    return Err(VmError::TypeError(
      "WeakMap key must be an Object or unregistered Symbol",
    ));
  }
  scope.push_root(key)?;
  scope.push_root(value)?;

  let data = weakmap_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = weakmap_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("WeakMap entry missing")),
    };
    let (_, existing) = entry_key_value(scope, entry)?;
    return Ok(existing);
  }

  let entry = create_entry(vm, scope, key, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(value)
}

/// `WeakMap.prototype.getOrInsertComputed(key, callback)` (ECMA-262 §24.3.3.5).
pub fn weakmap_prototype_get_or_insert_computed(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let map = require_weakmap(scope, this)?;
  scope.push_root(Value::Object(map))?;
  let key = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, key)? {
    return Err(VmError::TypeError(
      "WeakMap key must be an Object or unregistered Symbol",
    ));
  }
  scope.push_root(key)?;
  let callback = args.get(1).copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(callback)? {
    return Err(VmError::TypeError(
      "WeakMap.prototype.getOrInsertComputed callback is not callable",
    ));
  }
  scope.push_root(callback)?;

  let data = weakmap_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = weakmap_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("WeakMap entry missing")),
    };
    let (_, existing) = entry_key_value(scope, entry)?;
    return Ok(existing);
  }

  let value =
    vm.call_with_host_and_hooks(host, scope, hooks, callback, Value::Undefined, &[key])?;
  scope.push_root(value)?;
  // NOTE: The WeakMap may have been modified during execution of callback.
  let data = weakmap_data(scope, map)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = weakmap_find_index(scope, data, key)? {
    let entry = match array_get(scope, data, i)? {
      Value::Object(e) => e,
      _ => return Err(VmError::InvariantViolation("WeakMap entry missing")),
    };
    scope.push_root(Value::Object(entry))?;
    array_set(scope, entry, 1, value)?;
    return Ok(value);
  }

  let entry = create_entry(vm, scope, key, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(value)
}

pub fn weakset_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::TypeError("Constructor WeakSet requires 'new'"))
}

pub fn weakset_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let default_proto =
    default_proto_from_new_target(vm, scope, new_target, |intr| intr.weakset_prototype())?;
  let set = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    default_proto,
    &["[[WeakSetData]]"],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(set))?;

  let data = create_array(vm, scope, 0)?;
  scope.push_root(Value::Object(data))?;
  install_weakset_data(scope, set, data)?;

  let iterable = args.first().copied().unwrap_or(Value::Undefined);
  if matches!(iterable, Value::Undefined | Value::Null) {
    return Ok(Value::Object(set));
  }

  let adder = {
    let key = string_key(scope, "add")?;
    scope.ordinary_get_with_host_and_hooks(vm, host, hooks, set, key, Value::Object(set))?
  };
  if !scope.heap().is_callable(adder)? {
    return Err(VmError::TypeError("WeakSet add is not callable"));
  }
  scope.push_root(adder)?;
  add_values_from_iterable(vm, scope, host, hooks, Value::Object(set), iterable, adder)?;
  Ok(Value::Object(set))
}

pub fn weakset_prototype_add(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_weakset(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, value)? {
    return Err(VmError::TypeError(
      "WeakSet value must be an Object or unregistered Symbol",
    ));
  }
  scope.push_root(value)?;
  let data = weakset_data(scope, set)?;
  scope.push_root(Value::Object(data))?;

  if weakset_find_index(scope, data, value)?.is_some() {
    return Ok(Value::Object(set));
  }
  let entry = create_set_entry(vm, scope, value)?;
  scope.push_root(Value::Object(entry))?;
  let len = array_len(scope, data)?;
  array_set(scope, data, len, Value::Object(entry))?;
  Ok(Value::Object(set))
}

pub fn weakset_prototype_has(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_weakset(scope, this)?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, value)? {
    return Ok(Value::Bool(false));
  }
  let data = weakset_data(scope, set)?;
  Ok(Value::Bool(
    weakset_find_index(scope, data, value)?.is_some(),
  ))
}

pub fn weakset_prototype_delete(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let set = require_weakset(scope, this)?;
  scope.push_root(Value::Object(set))?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, value)? {
    return Ok(Value::Bool(false));
  }
  let data = weakset_data(scope, set)?;
  scope.push_root(Value::Object(data))?;
  if let Some(i) = weakset_find_index(scope, data, value)? {
    array_set(scope, data, i, Value::Undefined)?;
    return Ok(Value::Bool(true));
  }
  Ok(Value::Bool(false))
}
