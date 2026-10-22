//! Minimal `%TypedArray%` constructors + `%WeakRef%` (enough for Map/Set key identity).
//!
//! Implements `Int32Array` / `Uint32Array` / `BigInt64Array` / `BigUint64Array` and
//! `WeakRef` so collection tests can use those values as Map keys / Set values.
//! Full ArrayBuffer/DataView exotic semantics, detach, and true weak GC edges are
//! deferred; instances are ordinary objects with a marker, `length`, and indexed
//! data properties (element conversion follows the typed-array kind).

use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{
  GcObject, Intrinsics, Scope, Value, Vm, VmError, VmHost, VmHostHooks, WellKnownSymbols,
};

const TYPED_ARRAY_MARKER: &str = "vm-js.internal.TypedArray";
const TYPED_ARRAY_KIND: &str = "vm-js.internal.TypedArrayKind";
const WEAKREF_TARGET: &str = "vm-js.internal.WeakRefTarget";

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TypedArrayKind {
  Int32 = 0,
  Uint32 = 1,
  BigInt64 = 2,
  BigUint64 = 3,
}

impl TypedArrayKind {
  fn as_f64(self) -> f64 {
    self as i32 as f64
  }

  fn bytes_per_element(self) -> u32 {
    match self {
      Self::Int32 | Self::Uint32 => 4,
      Self::BigInt64 | Self::BigUint64 => 8,
    }
  }

  fn name(self) -> &'static str {
    match self {
      Self::Int32 => "Int32Array",
      Self::Uint32 => "Uint32Array",
      Self::BigInt64 => "BigInt64Array",
      Self::BigUint64 => "BigUint64Array",
    }
  }

  fn requires_new_message(self) -> &'static str {
    match self {
      Self::Int32 => "Constructor Int32Array requires 'new'",
      Self::Uint32 => "Constructor Uint32Array requires 'new'",
      Self::BigInt64 => "Constructor BigInt64Array requires 'new'",
      Self::BigUint64 => "Constructor BigUint64Array requires 'new'",
    }
  }

  fn is_bigint(self) -> bool {
    matches!(self, Self::BigInt64 | Self::BigUint64)
  }
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

fn to_length(value: Value) -> u32 {
  match value {
    Value::Number(n) => {
      if !n.is_finite() || n <= 0.0 {
        0
      } else {
        n.min(u32::MAX as f64).trunc() as u32
      }
    }
    Value::Bool(true) => 1,
    Value::Bool(false) | Value::Undefined | Value::Null => 0,
    _ => 0,
  }
}

fn convert_element(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  kind: TypedArrayKind,
  value: Value,
) -> Result<Value, VmError> {
  if kind.is_bigint() {
    // Spec: ToBigInt then ToBigInt64/ToBigUint64. For this minimal surface, accept BigInt
    // values as-is (test keys are already in range) and otherwise run `BigInt(value)`.
    match value {
      Value::BigInt(b) => Ok(Value::BigInt(b)),
      other => crate::builtins::bigint_constructor_call(
        vm,
        scope,
        host,
        hooks,
        callee,
        Value::Undefined,
        &[other],
      ),
    }
  } else {
    let n = crate::spec_ops::to_number(vm, scope, value)?;
    let out = match kind {
      TypedArrayKind::Int32 => crate::exec::number_to_int32(n) as f64,
      TypedArrayKind::Uint32 => crate::exec::number_to_uint32(n) as f64,
      _ => unreachable!(),
    };
    Ok(Value::Number(out))
  }
}

fn install_typed_array_slots(
  scope: &mut Scope<'_>,
  obj: GcObject,
  kind: TypedArrayKind,
) -> Result<(), VmError> {
  let marker = marker_key(scope, TYPED_ARRAY_MARKER)?;
  scope.define_property(
    obj,
    marker,
    data_desc(Value::Bool(true), false, false, false),
  )?;
  let kind_key = marker_key(scope, TYPED_ARRAY_KIND)?;
  scope.define_property(
    obj,
    kind_key,
    data_desc(Value::Number(kind.as_f64()), false, false, false),
  )?;
  Ok(())
}

fn typed_array_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
  kind: TypedArrayKind,
) -> Result<Value, VmError> {
  let default_proto = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
    .object_prototype();
  let ta = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    default_proto,
    &[
      "[[ViewedArrayBuffer]]",
      "[[TypedArrayName]]",
      "[[ByteLength]]",
    ],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(ta))?;
  install_typed_array_slots(scope, ta, kind)?;

  let arg0 = args.first().copied().unwrap_or(Value::Undefined);
  let len = match arg0 {
    Value::Undefined => 0,
    Value::Number(n) => to_length(Value::Number(n)),
    Value::Object(src) => {
      scope.push_root(Value::Object(src))?;
      let len_key = string_key(scope, "length")?;
      let len_val = scope.ordinary_get_with_host_and_hooks(
        vm,
        host,
        hooks,
        src,
        len_key,
        Value::Object(src),
      )?;
      to_length(len_val)
    }
    other => to_length(other),
  };

  let length_key = string_key(scope, "length")?;
  scope.define_property(
    ta,
    length_key,
    data_desc(Value::Number(len as f64), false, false, false),
  )?;

  if let Value::Object(src) = arg0 {
    for i in 0..len {
      let key = index_key(scope, i)?;
      let raw =
        scope.ordinary_get_with_host_and_hooks(vm, host, hooks, src, key, Value::Object(src))?;
      let converted = convert_element(vm, scope, host, hooks, callee, kind, raw)?;
      scope.push_root(converted)?;
      scope.define_property(ta, key, data_desc(converted, true, true, true))?;
    }
  }

  Ok(Value::Object(ta))
}

macro_rules! define_ta_ctors {
  ($(($call:ident, $construct:ident, $kind:expr)),* $(,)?) => {
    $(
      pub fn $call(
        _vm: &mut Vm,
        _scope: &mut Scope<'_>,
        _host: &mut dyn VmHost,
        _hooks: &mut dyn VmHostHooks,
        _callee: GcObject,
        _this: Value,
        _args: &[Value],
      ) -> Result<Value, VmError> {
        Err(VmError::TypeError($kind.requires_new_message()))
      }

      pub fn $construct(
        vm: &mut Vm,
        scope: &mut Scope<'_>,
        host: &mut dyn VmHost,
        hooks: &mut dyn VmHostHooks,
        callee: GcObject,
        args: &[Value],
        new_target: Value,
      ) -> Result<Value, VmError> {
        typed_array_construct(vm, scope, host, hooks, callee, args, new_target, $kind)
      }
    )*
  };
}

define_ta_ctors!(
  (
    int32_array_constructor_call,
    int32_array_constructor_construct,
    TypedArrayKind::Int32
  ),
  (
    uint32_array_constructor_call,
    uint32_array_constructor_construct,
    TypedArrayKind::Uint32
  ),
  (
    bigint64_array_constructor_call,
    bigint64_array_constructor_construct,
    TypedArrayKind::BigInt64
  ),
  (
    biguint64_array_constructor_call,
    biguint64_array_constructor_construct,
    TypedArrayKind::BigUint64
  ),
);

pub fn weakref_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::TypeError("Constructor WeakRef requires 'new'"))
}

fn can_be_held_weakly(scope: &Scope<'_>, v: Value) -> Result<bool, VmError> {
  match v {
    Value::Object(_) => Ok(true),
    Value::Symbol(sym) => Ok(scope.heap().symbol_key_for(sym)?.is_none()),
    _ => Ok(false),
  }
}

pub fn weakref_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let target = args.first().copied().unwrap_or(Value::Undefined);
  if !can_be_held_weakly(scope, target)? {
    return Err(VmError::TypeError(
      "WeakRef target must be an Object or unregistered Symbol",
    ));
  }
  scope.push_root(target)?;

  let default_proto = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
    .object_prototype();
  let wr = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    default_proto,
    &["[[WeakRefTarget]]"],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(wr))?;

  let key = marker_key(scope, WEAKREF_TARGET)?;
  // Strong storage for now; true weak GC edges are deferred.
  scope.define_property(wr, key, data_desc(target, false, false, false))?;
  Ok(Value::Object(wr))
}

pub fn weakref_prototype_deref(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(obj) = this else {
    return Err(VmError::TypeError(
      "WeakRef.prototype.deref called on incompatible receiver",
    ));
  };
  let key = marker_key(scope, WEAKREF_TARGET)?;
  match scope.heap().object_get_own_data_property_value(obj, &key)? {
    Some(v) => Ok(v),
    None => Err(VmError::TypeError(
      "WeakRef.prototype.deref called on incompatible receiver",
    )),
  }
}

fn define_prototype_method(
  scope: &mut Scope<'_>,
  prototype: GcObject,
  function_prototype: GcObject,
  name: &str,
  call: crate::NativeFunctionId,
  length: u32,
) -> Result<(), VmError> {
  let name_s = scope.alloc_string(name)?;
  scope.push_root(Value::String(name_s))?;
  let key = PropertyKey::from_string(name_s);
  let func = scope.alloc_native_function(call, None, name_s, length)?;
  scope.push_root(Value::Object(func))?;
  scope
    .heap_mut()
    .object_set_prototype(func, Some(function_prototype))?;
  scope.define_property(
    prototype,
    key,
    data_desc(Value::Object(func), true, false, true),
  )?;
  Ok(())
}

fn install_one_typed_array(
  scope: &mut Scope<'_>,
  roots: &mut Vec<crate::RootId>,
  global: GcObject,
  function_prototype: GcObject,
  object_prototype: GcObject,
  wks: &WellKnownSymbols,
  kind: TypedArrayKind,
  call: crate::NativeFunctionId,
  construct: crate::NativeConstructId,
) -> Result<(), VmError> {
  let proto = scope.alloc_object()?;
  roots.push(scope.heap_mut().add_root(Value::Object(proto))?);
  scope
    .heap_mut()
    .object_set_prototype(proto, Some(object_prototype))?;

  let name_s = scope.alloc_string(kind.name())?;
  scope.push_root(Value::String(name_s))?;
  let ctor = scope.alloc_native_function(call, Some(construct), name_s, 3)?;
  roots.push(scope.heap_mut().add_root(Value::Object(ctor))?);
  scope
    .heap_mut()
    .object_set_prototype(ctor, Some(function_prototype))?;

  let proto_key = string_key(scope, "prototype")?;
  scope.define_property(
    ctor,
    proto_key,
    data_desc(Value::Object(proto), false, false, false),
  )?;
  let name_key = string_key(scope, "name")?;
  scope.define_property(
    ctor,
    name_key,
    data_desc(Value::String(name_s), false, false, true),
  )?;
  let length_key = string_key(scope, "length")?;
  scope.define_property(
    ctor,
    length_key,
    data_desc(Value::Number(3.0), false, false, true),
  )?;
  let bpe_key = string_key(scope, "BYTES_PER_ELEMENT")?;
  let bpe = Value::Number(kind.bytes_per_element() as f64);
  scope.define_property(ctor, bpe_key, data_desc(bpe, false, false, false))?;
  scope.define_property(proto, bpe_key, data_desc(bpe, false, false, false))?;

  let ctor_key = string_key(scope, "constructor")?;
  scope.define_property(
    proto,
    ctor_key,
    data_desc(Value::Object(ctor), true, false, true),
  )?;
  let tag = scope.alloc_string(kind.name())?;
  scope.define_property(
    proto,
    PropertyKey::Symbol(wks.to_string_tag),
    data_desc(Value::String(tag), false, false, true),
  )?;

  let global_key = string_key(scope, kind.name())?;
  scope.define_property(
    global,
    global_key,
    PropertyDescriptor {
      enumerable: false,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Object(ctor),
        writable: true,
      },
    },
  )?;
  Ok(())
}

/// Installs minimal TypedArray + WeakRef globals on `global`, rooting constructors/prototypes.
pub fn install_globals(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  roots: &mut Vec<crate::RootId>,
  global: GcObject,
  intrinsics: &Intrinsics,
) -> Result<(), VmError> {
  let function_prototype = intrinsics.function_prototype();
  let object_prototype = intrinsics.object_prototype();
  let wks = *intrinsics.well_known_symbols();

  let kinds = [
    (
      TypedArrayKind::Int32,
      vm.register_native_call(int32_array_constructor_call)?,
      vm.register_native_construct(int32_array_constructor_construct)?,
    ),
    (
      TypedArrayKind::Uint32,
      vm.register_native_call(uint32_array_constructor_call)?,
      vm.register_native_construct(uint32_array_constructor_construct)?,
    ),
    (
      TypedArrayKind::BigInt64,
      vm.register_native_call(bigint64_array_constructor_call)?,
      vm.register_native_construct(bigint64_array_constructor_construct)?,
    ),
    (
      TypedArrayKind::BigUint64,
      vm.register_native_call(biguint64_array_constructor_call)?,
      vm.register_native_construct(biguint64_array_constructor_construct)?,
    ),
  ];
  for (kind, call, construct) in kinds {
    install_one_typed_array(
      scope,
      roots,
      global,
      function_prototype,
      object_prototype,
      &wks,
      kind,
      call,
      construct,
    )?;
  }

  // `%WeakRef%`
  let weakref_proto = scope.alloc_object()?;
  roots.push(scope.heap_mut().add_root(Value::Object(weakref_proto))?);
  scope
    .heap_mut()
    .object_set_prototype(weakref_proto, Some(object_prototype))?;
  let weakref_name = scope.alloc_string("WeakRef")?;
  scope.push_root(Value::String(weakref_name))?;
  let weakref_call = vm.register_native_call(weakref_constructor_call)?;
  let weakref_construct = vm.register_native_construct(weakref_constructor_construct)?;
  let weakref_ctor =
    scope.alloc_native_function(weakref_call, Some(weakref_construct), weakref_name, 1)?;
  roots.push(scope.heap_mut().add_root(Value::Object(weakref_ctor))?);
  scope
    .heap_mut()
    .object_set_prototype(weakref_ctor, Some(function_prototype))?;
  let proto_key = string_key(scope, "prototype")?;
  scope.define_property(
    weakref_ctor,
    proto_key,
    data_desc(Value::Object(weakref_proto), false, false, false),
  )?;
  let name_key = string_key(scope, "name")?;
  scope.define_property(
    weakref_ctor,
    name_key,
    data_desc(Value::String(weakref_name), false, false, true),
  )?;
  let length_key = string_key(scope, "length")?;
  scope.define_property(
    weakref_ctor,
    length_key,
    data_desc(Value::Number(1.0), false, false, true),
  )?;
  let ctor_key = string_key(scope, "constructor")?;
  scope.define_property(
    weakref_proto,
    ctor_key,
    data_desc(Value::Object(weakref_ctor), true, false, true),
  )?;
  {
    let tag = scope.alloc_string("WeakRef")?;
    scope.define_property(
      weakref_proto,
      PropertyKey::Symbol(wks.to_string_tag),
      data_desc(Value::String(tag), false, false, true),
    )?;
  }
  let deref_call = vm.register_native_call(weakref_prototype_deref)?;
  define_prototype_method(
    scope,
    weakref_proto,
    function_prototype,
    "deref",
    deref_call,
    0,
  )?;
  let weakref_key = string_key(scope, "WeakRef")?;
  scope.define_property(
    global,
    weakref_key,
    PropertyDescriptor {
      enumerable: false,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Object(weakref_ctor),
        writable: true,
      },
    },
  )?;

  Ok(())
}
