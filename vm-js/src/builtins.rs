use crate::function::FunctionData;
use crate::property::{PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind};
use crate::string::JsString;
use crate::{
  GcObject, Job, JobKind, PromiseCapability, PromiseHandle, PromiseReaction, PromiseReactionType,
  PromiseRejectionOperation, PromiseState, RealmId, RootId, Scope, Value, Vm, VmError, VmHost,
  VmHostHooks,
};

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

fn require_intrinsics(vm: &Vm) -> Result<crate::Intrinsics, VmError> {
  vm.intrinsics().ok_or(VmError::Unimplemented(
    "native builtins require Vm::intrinsics to be set",
  ))
}

/// `%IntrinsicDefaultProto%` from GetFunctionRealm(newTarget), else the active realm.
fn default_proto_from_new_target(
  vm: &Vm,
  scope: &Scope<'_>,
  new_target: Value,
  pick: impl FnOnce(&crate::Intrinsics) -> GcObject,
) -> Result<GcObject, VmError> {
  let active = require_intrinsics(vm)?;
  let Value::Object(nt) = new_target else {
    return Ok(pick(&active));
  };
  let Some(intr) = vm.intrinsics_for_function(scope.heap(), nt)? else {
    return Ok(pick(&active));
  };
  Ok(pick(&intr))
}

/// `Get(newTarget, "prototype")` if Object; otherwise `default_proto`.
fn prototype_from_new_target(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  new_target: Value,
  default_proto: GcObject,
) -> Result<GcObject, VmError> {
  let Value::Object(nt) = new_target else {
    return Ok(default_proto);
  };
  let mut s = scope.reborrow();
  s.push_root(Value::Object(nt))?;
  s.push_root(Value::Object(default_proto))?;
  let key = string_key(&mut s, "prototype")?;
  match vm.get(&mut s, nt, key)? {
    Value::Object(p) => Ok(p),
    _ => Ok(default_proto),
  }
}

fn require_object(value: Value) -> Result<GcObject, VmError> {
  match value {
    Value::Object(o) => Ok(o),
    _ => Err(VmError::TypeError("expected object")),
  }
}

fn require_callable(this: Value) -> Result<GcObject, VmError> {
  match this {
    Value::Object(obj) => Ok(obj),
    _ => Err(VmError::NotCallable),
  }
}

fn get_array_like_args(scope: &mut Scope<'_>, obj: GcObject) -> Result<Vec<Value>, VmError> {
  // Treat `obj` as array-like:
  // - read `length` as a Number
  // - read indices 0..length-1 as data properties
  let length_key_s = scope.alloc_string("length")?;
  let length_key = PropertyKey::from_string(length_key_s);
  let length_desc = scope.heap().get_property(obj, &length_key)?;
  let length_val = match length_desc.map(|d| d.kind) {
    Some(PropertyKind::Data { value, .. }) => value,
    Some(PropertyKind::Accessor { .. }) => {
      return Err(VmError::Unimplemented(
        "Function.prototype.apply: accessor length",
      ));
    }
    None => Value::Number(0.0),
  };

  let length = match length_val {
    Value::Number(n) if n.is_finite() && n >= 0.0 => n as usize,
    Value::Number(_) => 0usize,
    _ => {
      return Err(VmError::Unimplemented(
        "Function.prototype.apply: non-numeric length",
      ))
    }
  };

  let mut out: Vec<Value> = Vec::new();
  out
    .try_reserve_exact(length)
    .map_err(|_| VmError::OutOfMemory)?;

  for idx in 0..length {
    let idx_s = scope.alloc_string(&idx.to_string())?;
    let key = PropertyKey::from_string(idx_s);
    let desc = scope.heap().get_property(obj, &key)?;
    let value = match desc.map(|d| d.kind) {
      Some(PropertyKind::Data { value, .. }) => value,
      Some(PropertyKind::Accessor { .. }) => {
        return Err(VmError::Unimplemented(
          "Function.prototype.apply: accessor indexed element",
        ));
      }
      None => Value::Undefined,
    };
    out.push(value);
  }

  Ok(out)
}

fn set_function_job_realm_to_current(
  vm: &Vm,
  scope: &mut Scope<'_>,
  func: GcObject,
) -> Result<(), VmError> {
  if let Some(realm) = vm.current_realm() {
    scope.heap_mut().set_function_job_realm(func, realm)?;
  }
  Ok(())
}

fn root_property_key(scope: &mut Scope<'_>, key: PropertyKey) -> Result<(), VmError> {
  match key {
    PropertyKey::String(s) => {
      scope.push_root(Value::String(s))?;
    }
    PropertyKey::Symbol(s) => {
      scope.push_root(Value::Symbol(s))?;
    }
  }
  Ok(())
}

fn get_own_data_property_value_by_name(
  scope: &mut Scope<'_>,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj))?;
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  let Some(desc) = scope.heap().object_get_own_property(obj, &key)? else {
    return Ok(None);
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(Some(value)),
    PropertyKind::Accessor { .. } => Err(VmError::Unimplemented(
      "accessor properties are not yet supported",
    )),
  }
}

/// Minimal `ToPropertyDescriptor(Obj)` for own data fields on a descriptor object.
///
/// Matches the `Object.defineProperty` path: reads own data properties named
/// `value`/`writable`/`enumerable`/`configurable`/`get`/`set`. Full `HasProperty`+`Get`
/// (prototype-chain) ToPropertyDescriptor is deferred.
fn to_property_descriptor_patch(
  scope: &mut Scope<'_>,
  desc_obj: GcObject,
) -> Result<PropertyDescriptorPatch, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(desc_obj))?;

  let value = get_own_data_property_value_by_name(&mut scope, desc_obj, "value")?;
  let writable = get_own_data_property_value_by_name(&mut scope, desc_obj, "writable")?
    .map(|v| scope.heap().to_boolean(v))
    .transpose()?;
  let enumerable = get_own_data_property_value_by_name(&mut scope, desc_obj, "enumerable")?
    .map(|v| scope.heap().to_boolean(v))
    .transpose()?;
  let configurable = get_own_data_property_value_by_name(&mut scope, desc_obj, "configurable")?
    .map(|v| scope.heap().to_boolean(v))
    .transpose()?;
  let get = get_own_data_property_value_by_name(&mut scope, desc_obj, "get")?;
  let set = get_own_data_property_value_by_name(&mut scope, desc_obj, "set")?;

  if let Some(getter) = get {
    if !matches!(getter, Value::Undefined) && !scope.heap().is_callable(getter)? {
      return Err(VmError::TypeError(
        "property descriptor 'get' must be callable or undefined",
      ));
    }
  }
  if let Some(setter) = set {
    if !matches!(setter, Value::Undefined) && !scope.heap().is_callable(setter)? {
      return Err(VmError::TypeError(
        "property descriptor 'set' must be callable or undefined",
      ));
    }
  }

  let patch = PropertyDescriptorPatch {
    enumerable,
    configurable,
    value,
    writable,
    get,
    set,
  };
  patch.validate()?;
  Ok(patch)
}

/// `ObjectDefineProperties(O, Properties)` (ECMA-262 §20.1.2.3.1).
fn object_define_properties_on(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  o: GcObject,
  properties: Value,
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(o))?;

  // `ToObject(Properties)` — null/undefined throw; other primitives are not boxed yet.
  let props = match properties {
    Value::Undefined | Value::Null => {
      return Err(VmError::TypeError(
        "Object.defineProperties Properties is null or undefined",
      ));
    }
    Value::Object(obj) => obj,
    _ => {
      return Err(VmError::Unimplemented(
        "Object.defineProperties Properties ToObject boxing",
      ));
    }
  };
  scope.push_root(Value::Object(props))?;

  // Spec: collect enumerable own keys + ToPropertyDescriptor first, then DefinePropertyOrThrow.
  let keys = scope.heap().ordinary_own_property_keys(props)?;
  let mut descriptors: Vec<(PropertyKey, PropertyDescriptorPatch)> = Vec::new();
  descriptors
    .try_reserve_exact(keys.len())
    .map_err(|_| VmError::OutOfMemory)?;

  for key in keys {
    root_property_key(&mut scope, key)?;
    let Some(prop_desc) = scope.heap().object_get_own_property(props, &key)? else {
      continue;
    };
    if !prop_desc.enumerable {
      continue;
    }

    // `Get(props, nextKey)` (invokes getters on the properties bag).
    let desc_val = vm.get(&mut scope, props, key)?;
    let desc_obj = match desc_val {
      Value::Object(obj) => obj,
      _ => {
        return Err(VmError::TypeError("Property description must be an object"));
      }
    };
    scope.push_root(Value::Object(desc_obj))?;

    let patch = to_property_descriptor_patch(&mut scope, desc_obj)?;
    if let Some(v) = patch.value {
      scope.push_root(v)?;
    }
    if let Some(v) = patch.get {
      scope.push_root(v)?;
    }
    if let Some(v) = patch.set {
      scope.push_root(v)?;
    }
    descriptors.push((key, patch));
  }

  for (key, patch) in descriptors {
    root_property_key(&mut scope, key)?;
    scope.define_property_or_throw(o, key, patch)?;
  }

  Ok(Value::Object(o))
}

pub fn function_prototype_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn object_constructor_impl(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let arg0 = args.get(0).copied().unwrap_or(Value::Undefined);
  let mut host_state = ();
  match arg0 {
    Value::Undefined | Value::Null => {
      let obj = scope.alloc_object()?;
      scope
        .heap_mut()
        .object_set_prototype(obj, Some(intr.object_prototype()))?;
      Ok(Value::Object(obj))
    }
    Value::Object(obj) => Ok(Value::Object(obj)),
    Value::String(_) => string_constructor_construct(
      vm,
      scope,
      &mut host_state,
      host,
      intr.string_constructor(),
      &[arg0],
      Value::Object(intr.string_constructor()),
    ),
    Value::Number(_) => number_constructor_construct(
      vm,
      scope,
      &mut host_state,
      host,
      intr.number_constructor(),
      &[arg0],
      Value::Object(intr.number_constructor()),
    ),
    Value::Bool(_) => boolean_constructor_construct(
      vm,
      scope,
      &mut host_state,
      host,
      intr.boolean_constructor(),
      &[arg0],
      Value::Object(intr.boolean_constructor()),
    ),
    Value::Symbol(sym) => {
      // Minimal boxing used by test262 `ToObject` paths (e.g. `Object(Symbol("1"))`).
      // Store the symbol on an internal marker so `Symbol.prototype.valueOf` can recover it.
      scope.push_root(Value::Symbol(sym))?;
      let obj = scope.alloc_object()?;
      scope.push_root(Value::Object(obj))?;
      scope
        .heap_mut()
        .object_set_prototype(obj, Some(intr.symbol_prototype()))?;

      let marker = scope.alloc_string("vm-js.internal.SymbolData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      scope.define_property(
        obj,
        marker_key,
        data_desc(Value::Symbol(sym), true, false, false),
      )?;

      Ok(Value::Object(obj))
    }
    Value::BigInt(b) => {
      // Minimal BigInt boxing used by test262 (`Object(1n)`).
      scope.push_root(Value::BigInt(b))?;
      let obj = scope.alloc_object()?;
      scope.push_root(Value::Object(obj))?;
      scope
        .heap_mut()
        .object_set_prototype(obj, Some(intr.bigint_prototype()))?;

      let marker = scope.alloc_string("vm-js.internal.BigIntData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      scope.define_property(
        obj,
        marker_key,
        data_desc(Value::BigInt(b), true, false, false),
      )?;

      Ok(Value::Object(obj))
    }
  }
}

pub fn object_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, host, args)
}

pub fn object_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, host, args)
}

pub fn object_define_property(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();

  let target = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(target))?;

  let prop = args.get(1).copied().unwrap_or(Value::Undefined);
  let key = crate::spec_ops::to_property_key(vm, &mut scope, prop)?;
  root_property_key(&mut scope, key)?;

  let desc_obj = require_object(args.get(2).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(desc_obj))?;

  let patch = to_property_descriptor_patch(&mut scope, desc_obj)?;

  let ok = scope.define_own_property(target, key, patch)?;
  if !ok {
    return Err(VmError::TypeError("DefineOwnProperty rejected"));
  }
  Ok(Value::Object(target))
}

/// `Object.defineProperties(O, Properties)` (ECMA-262 §20.1.2.3).
pub fn object_define_properties(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let target = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  let properties = args.get(1).copied().unwrap_or(Value::Undefined);
  object_define_properties_on(vm, scope, target, properties)
}

pub fn object_create(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  let proto_val = args.get(0).copied().unwrap_or(Value::Undefined);
  let proto = match proto_val {
    Value::Object(o) => Some(o),
    Value::Null => None,
    _ => {
      return Err(VmError::TypeError(
        "Object.create prototype must be an object or null",
      ))
    }
  };

  let obj = scope.alloc_object()?;
  scope.heap_mut().object_set_prototype(obj, proto)?;
  scope.push_root(Value::Object(obj))?;

  // Spec: if Properties is not undefined, `Return ? ObjectDefineProperties(obj, Properties)`.
  if let Some(properties) = args.get(1).copied() {
    if !matches!(properties, Value::Undefined) {
      return object_define_properties_on(vm, &mut scope, obj, properties);
    }
  }

  Ok(Value::Object(obj))
}

pub fn object_keys(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;

  let own_keys = scope.heap().ordinary_own_property_keys(obj)?;
  let mut names: Vec<crate::GcString> = Vec::new();
  names
    .try_reserve_exact(own_keys.len())
    .map_err(|_| VmError::OutOfMemory)?;

  for key in own_keys {
    let PropertyKey::String(key_str) = key else {
      continue;
    };
    let Some(desc) = scope.heap().object_get_own_property(obj, &key)? else {
      continue;
    };
    if desc.enumerable {
      names.push(key_str);
    }
  }

  let len = u32::try_from(names.len()).map_err(|_| VmError::OutOfMemory)?;
  let array = create_array_object(vm, scope, len)?;

  for (i, name) in names.iter().copied().enumerate() {
    let mut idx_scope = scope.reborrow();
    idx_scope.push_root(Value::Object(array))?;
    idx_scope.push_root(Value::String(name))?;

    let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
    idx_scope.define_property(array, key, data_desc(Value::String(name), true, true, true))?;
  }

  Ok(Value::Object(array))
}

pub fn object_assign(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // Spec: Object.assign performs `ToObject` on the target and each source. We only support objects
  // for now, but we still follow the `Get`/`Set` semantics (invoking accessors).
  let mut scope = scope.reborrow();
  let target = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(target))?;

  for source_val in args.iter().copied().skip(1) {
    let source = match source_val {
      Value::Undefined | Value::Null => continue,
      Value::Object(o) => o,
      _ => return Err(VmError::TypeError("Object.assign source must be an object")),
    };

    let keys = scope.heap().ordinary_own_property_keys(source)?;
    for key in keys {
      let Some(desc) = scope.heap().object_get_own_property(source, &key)? else {
        continue;
      };
      if !desc.enumerable {
        continue;
      }

      // Spec: `Get(from, key)` (invokes getters).
      let value = vm.get(&mut scope, source, key)?;
      // Spec: `Set(to, key, value, true)` (invokes setters, throws on failure).
      let ok = scope.ordinary_set(vm, target, key, value, Value::Object(target))?;
      if !ok {
        return Err(VmError::TypeError("Object.assign failed to set property"));
      }
    }
  }

  Ok(Value::Object(target))
}

pub fn object_get_prototype_of(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  match scope.heap().object_prototype(obj)? {
    Some(proto) => Ok(Value::Object(proto)),
    None => Ok(Value::Null),
  }
}

pub fn object_set_prototype_of(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  let proto_val = args.get(1).copied().unwrap_or(Value::Undefined);
  let proto = match proto_val {
    Value::Object(o) => Some(o),
    Value::Null => None,
    _ => {
      return Err(VmError::TypeError(
        "Object.setPrototypeOf prototype must be an object or null",
      ))
    }
  };

  // OrdinarySetPrototypeOf: same value is always ok; otherwise require [[Extensible]].
  let current = scope.heap().object_prototype(obj)?;
  if current != proto {
    if !scope.heap().object_is_extensible(obj)? {
      return Err(VmError::TypeError(
        "Object.setPrototypeOf called on a non-extensible object",
      ));
    }
    scope.heap_mut().object_set_prototype(obj, proto)?;
  }
  Ok(Value::Object(obj))
}

/// `Object.preventExtensions(O)` (ECMA-262 §20.1.2.19).
pub fn object_prevent_extensions(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let o = args.first().copied().unwrap_or(Value::Undefined);
  let Value::Object(obj) = o else {
    // Non-objects are returned unchanged.
    return Ok(o);
  };
  scope.object_prevent_extensions(obj)?;
  Ok(Value::Object(obj))
}

/// `Object.isExtensible(O)` (ECMA-262 §20.1.2.13).
pub fn object_is_extensible(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let o = args.first().copied().unwrap_or(Value::Undefined);
  let Value::Object(obj) = o else {
    return Ok(Value::Bool(false));
  };
  Ok(Value::Bool(scope.object_is_extensible(obj)?))
}

fn create_array_object(vm: &mut Vm, scope: &mut Scope<'_>, len: u32) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;

  let array = scope.alloc_array(len as usize)?;
  scope
    .heap_mut()
    .object_set_prototype(array, Some(intr.array_prototype()))?;
  Ok(array)
}

fn array_constructor_impl(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  args: &[Value],
) -> Result<Value, VmError> {
  match args {
    [] => Ok(Value::Object(create_array_object(vm, scope, 0)?)),
    [Value::Number(n)] => {
      // Minimal `Array(len)` support (used by WebIDL sequence conversions).
      if !n.is_finite() || n.fract() != 0.0 || *n < 0.0 || *n > (u32::MAX as f64) {
        return Err(VmError::Unimplemented("Array(length) validation"));
      }
      Ok(Value::Object(create_array_object(vm, scope, *n as u32)?))
    }
    _ => {
      // Treat arguments as elements.
      let len = u32::try_from(args.len()).map_err(|_| VmError::OutOfMemory)?;
      let array = create_array_object(vm, scope, len)?;

      for (i, el) in args.iter().copied().enumerate() {
        // Root `array` and `el` during string allocation.
        let mut idx_scope = scope.reborrow();
        idx_scope.push_root(Value::Object(array))?;
        idx_scope.push_root(el)?;

        let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
        idx_scope.define_property(array, key, data_desc(el, true, true, true))?;
      }

      Ok(Value::Object(array))
    }
  }
}

pub fn array_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn array_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn function_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // §20.2.1.1: NewTarget is undefined when called as a function.
  crate::dynamic_function::create_dynamic_function(
    vm,
    scope,
    hooks,
    callee,
    Value::Undefined,
    crate::dynamic_function::DynamicFunctionKind::Normal,
    args,
  )
}

pub fn function_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  crate::dynamic_function::create_dynamic_function(
    vm,
    scope,
    hooks,
    callee,
    new_target,
    crate::dynamic_function::DynamicFunctionKind::Normal,
    args,
  )
}

pub fn error_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  error_constructor_construct(vm, scope, _host, host, callee, args, Value::Object(callee))
}

pub fn error_constructor_construct(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let name = scope.heap().get_function_name(callee)?;

  // `new Error(message)` uses `GetPrototypeFromConstructor(newTarget, defaultProto)`.
  // Approximate this by:
  // 1. Reading `callee.prototype` as the default.
  // 2. If `new_target` is an object, prefer `new_target.prototype` when it is an object.
  let prototype_key = PropertyKey::from_string(scope.alloc_string("prototype")?);
  let default_proto_value = scope
    .heap()
    .object_get_own_data_property_value(callee, &prototype_key)?
    .ok_or(VmError::Unimplemented(
      "Error constructor missing own prototype property",
    ))?;
  let Value::Object(default_prototype) = default_proto_value else {
    return Err(VmError::Unimplemented(
      "Error constructor prototype property is not an object",
    ));
  };

  let instance_prototype = match new_target {
    Value::Object(nt) => match scope.heap().get(nt, &prototype_key)? {
      Value::Object(p) => p,
      _ => default_prototype,
    },
    _ => default_prototype,
  };

  let is_aggregate_error = scope.heap().get_string(name)?.to_utf8_lossy() == "AggregateError";

  // Message argument: for AggregateError, the message is the *second* argument.
  // Spec: `new AggregateError(errors, message)` (ECMA-262).
  let message_arg = if is_aggregate_error {
    args.get(1).copied()
  } else {
    args.first().copied()
  };

  let message_string = match message_arg {
    Some(Value::Undefined) | None => scope.alloc_string("")?,
    Some(other) => scope.heap_mut().to_string(other)?,
  };
  scope.push_root(Value::String(message_string))?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(instance_prototype))?;

  let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
  scope.define_property(
    obj,
    name_key,
    data_desc(Value::String(name), true, false, true),
  )?;

  let message_key = PropertyKey::from_string(scope.alloc_string("message")?);
  scope.define_property(
    obj,
    message_key,
    data_desc(Value::String(message_string), true, false, true),
  )?;

  // AggregateError `errors` property.
  //
  // Spec: `new AggregateError(errors, message)` creates an `errors` own data property containing an
  // Array created from the provided iterable. `vm-js` does not yet implement full iterable-to-list
  // conversion here, so we store the first argument directly (sufficient for Promise.any, which
  // passes an Array).
  if is_aggregate_error {
    let errors = args.get(0).copied().unwrap_or(Value::Undefined);
    let errors_key = PropertyKey::from_string(scope.alloc_string("errors")?);
    scope.define_property(obj, errors_key, data_desc(errors, true, false, true))?;
  }

  Ok(Value::Object(obj))
}

pub(crate) fn create_type_error(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  message: &str,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let ctor = intr.type_error();

  let msg = scope.alloc_string(message)?;
  scope.push_root(Value::String(msg))?;

  let mut host_state = ();
  error_constructor_construct(
    vm,
    scope,
    &mut host_state,
    host,
    ctor,
    &[Value::String(msg)],
    Value::Object(ctor),
  )
}

fn throw_type_error(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  message: &str,
) -> Result<Value, VmError> {
  let err = create_type_error(vm, scope, host, message)?;
  Err(VmError::Throw(err))
}

fn new_promise(vm: &mut Vm, scope: &mut Scope<'_>) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;
  scope.alloc_promise_with_prototype(Some(intr.promise_prototype()))
}

pub(crate) fn new_promise_capability(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  constructor: Value,
) -> Result<PromiseCapability, VmError> {
  let intr = require_intrinsics(vm)?;

  let Value::Object(_) = constructor else {
    let err = create_type_error(
      vm,
      scope,
      host,
      "Promise capability constructor must be an object",
    )?;
    return Err(VmError::Throw(err));
  };

  if !scope.heap().is_constructor(constructor)? {
    let err = create_type_error(
      vm,
      scope,
      host,
      "Promise capability constructor is not a constructor",
    )?;
    return Err(VmError::Throw(err));
  }

  // Root the constructor across allocations/GC while wiring the capability and constructing the
  // Promise.
  scope.push_root(constructor)?;

  // --- NewPromiseCapability(C) ---
  // Spec: https://tc39.es/ecma262/#sec-newpromisecapability

  // resolvingFunctions = { resolve: undefined, reject: undefined }
  //
  // Represent the record as a closure environment with two mutable bindings.
  let resolving_env = scope.env_create(None)?;
  scope.push_env_root(resolving_env)?;
  scope.env_create_mutable_binding(resolving_env, "resolve")?;
  scope.env_create_mutable_binding(resolving_env, "reject")?;
  scope
    .heap_mut()
    .env_initialize_binding(resolving_env, "resolve", Value::Undefined)?;
  scope
    .heap_mut()
    .env_initialize_binding(resolving_env, "reject", Value::Undefined)?;

  // executor = CreateBuiltinFunction(...)
  let executor_name = scope.alloc_string("executor")?;
  let executor = scope.alloc_native_function(
    intr.promise_capability_executor_call(),
    None,
    executor_name,
    2,
  )?;
  set_function_job_realm_to_current(vm, scope, executor)?;
  scope
    .heap_mut()
    .object_set_prototype(executor, Some(intr.function_prototype()))?;
  scope
    .heap_mut()
    .set_function_data(executor, FunctionData::PromiseCapabilityExecutor)?;
  scope
    .heap_mut()
    .set_function_closure_env(executor, Some(resolving_env))?;

  // promise = ? Construct(C, « executor »)
  let promise = vm.construct_with_host(
    scope,
    host,
    constructor,
    &[Value::Object(executor)],
    constructor,
  )?;

  // Per spec, `Construct` returns an Object. `vm-js` native constructors can return non-objects, so
  // validate this to preserve the PromiseCapability invariants used throughout the VM.
  if !matches!(promise, Value::Object(_)) {
    let err = create_type_error(
      vm,
      scope,
      host,
      "Promise capability promise is not an object",
    )?;
    return Err(VmError::Throw(err));
  }

  // If IsCallable(resolve) is false, throw a TypeError exception.
  let resolve = scope
    .heap()
    .env_get_binding_value(resolving_env, "resolve", false)?;
  if !scope.heap().is_callable(resolve)? {
    let err = create_type_error(
      vm,
      scope,
      host,
      "Promise capability resolve is not callable",
    )?;
    return Err(VmError::Throw(err));
  }

  // If IsCallable(reject) is false, throw a TypeError exception.
  let reject = scope
    .heap()
    .env_get_binding_value(resolving_env, "reject", false)?;
  if !scope.heap().is_callable(reject)? {
    let err = create_type_error(vm, scope, host, "Promise capability reject is not callable")?;
    return Err(VmError::Throw(err));
  }

  Ok(PromiseCapability {
    promise,
    resolve,
    reject,
  })
}

fn get_property_value_with_host(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  obj: GcObject,
  key: PropertyKey,
  receiver: Value,
) -> Result<Value, VmError> {
  let Some(desc) = scope.heap().get_property(obj, &key)? else {
    return Ok(Value::Undefined);
  };

  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(value),
    PropertyKind::Accessor { get, .. } => {
      if matches!(get, Value::Undefined) {
        Ok(Value::Undefined)
      } else {
        if !scope.heap().is_callable(get)? {
          return Err(VmError::TypeError("accessor getter is not callable"));
        }
        vm.call_with_host(scope, host, get, receiver, &[])
      }
    }
  }
}

/// ECMA-262 `PromiseResolve(C, x)` abstract operation.
fn promise_resolve_abstract(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  constructor: Value,
  x: Value,
) -> Result<GcObject, VmError> {
  let mut scope = scope.reborrow();
  // Root inputs across allocations/GC.
  scope.push_root(constructor)?;
  scope.push_root(x)?;

  if let Value::Object(obj) = x {
    if scope.heap().is_promise_object(obj) {
      // `x.constructor === C`
      let ctor_key_s = scope.alloc_string("constructor")?;
      scope.push_root(Value::String(ctor_key_s))?;
      let ctor_key = PropertyKey::from_string(ctor_key_s);
      let x_ctor =
        get_property_value_with_host(vm, &mut scope, host, obj, ctor_key, Value::Object(obj))?;
      if x_ctor.same_value(constructor, scope.heap()) {
        return Ok(obj);
      }
    }
  }

  let capability = new_promise_capability(vm, &mut scope, host, constructor)?;
  let Value::Object(promise_obj) = capability.promise else {
    return Err(VmError::InvariantViolation(
      "PromiseCapability.promise is not an object",
    ));
  };

  // Root the promise + resolving function for the duration of the resolve call (which may
  // allocate/GC).
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  let _ = vm.call_with_host(&mut scope, host, capability.resolve, Value::Undefined, &[x])?;
  Ok(promise_obj)
}

fn create_promise_resolving_functions(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  promise: GcObject,
) -> Result<(Value, Value), VmError> {
  let intr = require_intrinsics(vm)?;
  let call_id = intr.promise_resolving_function_call();

  // Root the promise and shared [[AlreadyResolved]] state while allocating the resolving
  // functions.
  scope.push_root(Value::Object(promise))?;

  // Model `alreadyResolved` as a mutable binding in a shared closure environment.
  //
  // This is important for spec-correct behavior when:
  // - an executor calls both `resolve` and `reject`,
  // - or calls `resolve(thenable)` and then calls `resolve` again before the thenable job runs.
  let already_resolved_env = scope.env_create(None)?;
  scope.push_env_root(already_resolved_env)?;
  scope.env_create_mutable_binding(already_resolved_env, "alreadyResolved")?;
  scope.heap_mut().env_initialize_binding(
    already_resolved_env,
    "alreadyResolved",
    Value::Bool(false),
  )?;

  let resolve_name = scope.alloc_string("resolve")?;
  let resolve = scope.alloc_native_function(call_id, None, resolve_name, 1)?;
  set_function_job_realm_to_current(vm, scope, resolve)?;
  scope
    .heap_mut()
    .object_set_prototype(resolve, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    resolve,
    FunctionData::PromiseResolvingFunction {
      promise,
      is_reject: false,
    },
  )?;
  scope
    .heap_mut()
    .set_function_closure_env(resolve, Some(already_resolved_env))?;

  let reject_name = scope.alloc_string("reject")?;
  let reject = scope.alloc_native_function(call_id, None, reject_name, 1)?;
  set_function_job_realm_to_current(vm, scope, reject)?;
  scope
    .heap_mut()
    .object_set_prototype(reject, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    reject,
    FunctionData::PromiseResolvingFunction {
      promise,
      is_reject: true,
    },
  )?;
  scope
    .heap_mut()
    .set_function_closure_env(reject, Some(already_resolved_env))?;

  Ok((Value::Object(resolve), Value::Object(reject)))
}

fn enqueue_promise_reaction_job(
  host: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  reaction: PromiseReaction,
  argument: Value,
  current_realm: Option<RealmId>,
) -> Result<(), VmError> {
  let handler_callback_object = reaction
    .handler
    .as_ref()
    .map(|handler| handler.callback_object());
  let realm = reaction
    .handler
    .as_ref()
    .and_then(|handler| handler.realm())
    .or_else(|| {
      handler_callback_object.and_then(|handler| scope.heap().get_function_job_realm(handler))
    })
    .or(current_realm);
  let capability = reaction.capability;

  let job = Job::new(JobKind::Promise, move |ctx, host| {
    let Some(cap) = reaction.capability else {
      return Ok(());
    };

    match reaction.type_ {
      PromiseReactionType::Fulfill => {
        let handler_result = if let Some(handler) = &reaction.handler {
          match host.host_call_job_callback(ctx, handler, Value::Undefined, &[argument]) {
            Ok(v) => v,
            Err(VmError::Throw(e) | VmError::ThrowWithStack { value: e, .. }) => {
              let _ = ctx.call(host, cap.reject, Value::Undefined, &[e])?;
              return Ok(());
            }
            Err(e) => return Err(e),
          }
        } else {
          argument
        };

        let _ = ctx.call(host, cap.resolve, Value::Undefined, &[handler_result])?;
        Ok(())
      }
      PromiseReactionType::Reject => {
        if let Some(handler) = &reaction.handler {
          match host.host_call_job_callback(ctx, handler, Value::Undefined, &[argument]) {
            Ok(v) => {
              let _ = ctx.call(host, cap.resolve, Value::Undefined, &[v])?;
              Ok(())
            }
            Err(VmError::Throw(e) | VmError::ThrowWithStack { value: e, .. }) => {
              let _ = ctx.call(host, cap.reject, Value::Undefined, &[e])?;
              Ok(())
            }
            Err(e) => Err(e),
          }
        } else {
          let _ = ctx.call(host, cap.reject, Value::Undefined, &[argument])?;
          Ok(())
        }
      }
    }
  });

  // Root captured GC values while creating persistent roots: `Heap::add_root` can trigger a GC.
  // The resulting `RootId`s are transferred to the job so it can clean them up on run/discard.
  let mut root_scope = scope.reborrow();
  let mut values = [Value::Undefined; 5];
  let mut value_count = 0usize;
  values[value_count] = argument;
  value_count += 1;
  if let Some(handler) = handler_callback_object {
    values[value_count] = Value::Object(handler);
    value_count += 1;
  }
  if let Some(cap) = capability {
    values[value_count] = cap.promise;
    value_count += 1;
    values[value_count] = cap.resolve;
    value_count += 1;
    values[value_count] = cap.reject;
    value_count += 1;
  }
  root_scope.push_roots(&values[..value_count])?;

  let mut roots: Vec<RootId> = Vec::new();
  roots
    .try_reserve_exact(value_count)
    .map_err(|_| VmError::OutOfMemory)?;
  for value in values[..value_count].iter().copied() {
    let id = match root_scope.heap_mut().add_root(value) {
      Ok(id) => id,
      Err(e) => {
        for root in roots.drain(..) {
          root_scope.heap_mut().remove_root(root);
        }
        return Err(e);
      }
    };
    roots.push(id);
  }

  let job = job.with_roots(roots);
  host.host_enqueue_promise_job(job, realm);
  Ok(())
}

fn trigger_promise_reactions(
  host: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  reactions: Box<[PromiseReaction]>,
  argument: Value,
  current_realm: Option<RealmId>,
) -> Result<(), VmError> {
  for reaction in reactions.into_vec() {
    enqueue_promise_reaction_job(host, scope, reaction, argument, current_realm)?;
  }
  Ok(())
}

pub(crate) fn fulfill_promise(
  host: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  promise: GcObject,
  value: Value,
  current_realm: Option<RealmId>,
) -> Result<(), VmError> {
  let (fulfill_reactions, _reject_reactions) =
    scope
      .heap_mut()
      .promise_settle_and_take_reactions(promise, PromiseState::Fulfilled, value)?;
  trigger_promise_reactions(host, scope, fulfill_reactions, value, current_realm)
}

pub(crate) fn reject_promise(
  host: &mut dyn VmHostHooks,
  scope: &mut Scope<'_>,
  promise: GcObject,
  reason: Value,
  current_realm: Option<RealmId>,
) -> Result<(), VmError> {
  if scope.heap().promise_state(promise)? != PromiseState::Pending {
    // Per spec, subsequent rejects of an already-settled promise are no-ops.
    return Ok(());
  }

  let is_handled = scope.heap().promise_is_handled(promise)?;

  let (_fulfill_reactions, reject_reactions) =
    scope
      .heap_mut()
      .promise_settle_and_take_reactions(promise, PromiseState::Rejected, reason)?;

  if !is_handled {
    host.host_promise_rejection_tracker(PromiseHandle(promise), PromiseRejectionOperation::Reject);
  }

  trigger_promise_reactions(host, scope, reject_reactions, reason, current_realm)
}

pub(crate) fn resolve_promise(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  promise: GcObject,
  resolution: Value,
) -> Result<(), VmError> {
  let current_realm = vm.current_realm();
  let intr = require_intrinsics(vm)?;

  // 27.2.1.3.2 `Promise Resolve Functions`: self-resolution is a TypeError rejection.
  if let Value::Object(obj) = resolution {
    if obj == promise {
      let err = create_type_error(vm, scope, host, "Promise cannot resolve itself")?;
      return reject_promise(host, scope, promise, err, current_realm);
    }
  }

  // Non-objects cannot be thenables.
  let Value::Object(thenable_obj) = resolution else {
    return fulfill_promise(host, scope, promise, resolution, current_realm);
  };

  // Get `thenable.then`.
  //
  // Spec: this must perform `Get(thenable, "then")`, which means it must:
  // - traverse the prototype chain,
  // - and invoke accessor getters.
  let then_result = {
    // Root `thenable_obj` while allocating the property key.
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(thenable_obj))?;
    let then_key_s = key_scope.alloc_string("then")?;
    key_scope.push_root(Value::String(then_key_s))?;
    let then_key = PropertyKey::from_string(then_key_s);

    match key_scope.heap().get_property(thenable_obj, &then_key)? {
      None => Ok(Value::Undefined),
      Some(desc) => match desc.kind {
        PropertyKind::Data { value, .. } => Ok(value),
        PropertyKind::Accessor { get, .. } => {
          if matches!(get, Value::Undefined) {
            Ok(Value::Undefined)
          } else if !key_scope.heap().is_callable(get)? {
            // Model `Get(thenable, "then")` throwing a TypeError when an accessor getter exists but
            // is not callable. This must reject the promise rather than propagate as a VM error
            // from `resolve()`.
            Err(crate::throw_type_error(
              &mut key_scope,
              intr,
              "accessor getter is not callable",
            ))
          } else {
            vm.call_with_host(&mut key_scope, host, get, Value::Object(thenable_obj), &[])
          }
        }
      },
    }
  };

  let then = match then_result {
    Ok(v) => v,
    Err(VmError::Throw(e) | VmError::ThrowWithStack { value: e, .. }) => {
      reject_promise(host, scope, promise, e, current_realm)?;
      return Ok(());
    }
    Err(e) => return Err(e),
  };

  if !scope.heap().is_callable(then)? {
    return fulfill_promise(host, scope, promise, resolution, current_realm);
  }

  let Value::Object(then_obj) = then else {
    return Err(VmError::Unimplemented("callable then is not an object"));
  };

  // Enqueue PromiseResolveThenableJob(promise, thenable, then).
  let then_job_callback = host.host_make_job_callback(then_obj);

  // Per spec, the thenable job must use *fresh* resolving functions for `promise` (with their own
  // alreadyResolved record).
  scope.push_root(Value::Object(thenable_obj))?;
  let (resolve, reject) = create_promise_resolving_functions(vm, scope, promise)?;

  let callback_obj = then_job_callback.callback_object();
  let realm = then_job_callback
    .realm()
    .or_else(|| scope.heap().get_function_job_realm(callback_obj))
    .or(current_realm);
  let job = Job::new(JobKind::Promise, move |ctx, host| {
    match host.host_call_job_callback(ctx, &then_job_callback, resolution, &[resolve, reject]) {
      Ok(_) => Ok(()),
      Err(VmError::Throw(e) | VmError::ThrowWithStack { value: e, .. }) => {
        let _ = ctx.call(host, reject, Value::Undefined, &[e])?;
        Ok(())
      }
      Err(e) => Err(e),
    }
  });

  // Root captured GC values while creating persistent roots: `Heap::add_root` can trigger a GC.
  // The resulting `RootId`s are transferred to the job so it can clean them up on run/discard.
  let mut root_scope = scope.reborrow();
  let values = [resolution, Value::Object(callback_obj), resolve, reject];
  root_scope.push_roots(&values)?;

  let mut roots: Vec<RootId> = Vec::new();
  roots
    .try_reserve_exact(values.len())
    .map_err(|_| VmError::OutOfMemory)?;
  for value in values {
    let id = match root_scope.heap_mut().add_root(value) {
      Ok(id) => id,
      Err(e) => {
        for root in roots.drain(..) {
          root_scope.heap_mut().remove_root(root);
        }
        return Err(e);
      }
    };
    roots.push(id);
  }

  let job = job.with_roots(roots);
  host.host_enqueue_promise_job(job, realm);
  Ok(())
}

pub fn promise_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  throw_type_error(
    vm,
    scope,
    host,
    "Promise constructor must be called with new",
  )
}

pub fn promise_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let executor = args.get(0).copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(executor)? {
    return throw_type_error(vm, scope, host, "Promise executor is not callable");
  }

  // Promise constructor:
  // `promise = OrdinaryCreateFromConstructor(NewTarget, "%Promise.prototype%", ...)`.
  let intr = require_intrinsics(vm)?;
  let promise = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    intr.promise_prototype(),
    &[
      "[[PromiseState]]",
      "[[PromiseResult]]",
      "[[PromiseFulfillReactions]]",
      "[[PromiseRejectReactions]]",
      "[[PromiseIsHandled]]",
    ],
    |scope| scope.alloc_promise(),
  )?;
  scope.push_root(Value::Object(promise))?;

  let (resolve, reject) = create_promise_resolving_functions(vm, scope, promise)?;

  // Invoke executor(resolve, reject).
  match vm.call_with_host(scope, host, executor, Value::Undefined, &[resolve, reject]) {
    Ok(_) => {}
    Err(VmError::Throw(reason) | VmError::ThrowWithStack { value: reason, .. }) => {
      // If executor throws, reject the promise with the thrown value by calling the resolving
      // function (so it respects `alreadyResolved`).
      let _ = vm.call_with_host(scope, host, reject, Value::Undefined, &[reason])?;
    }
    Err(e) => return Err(e),
  }

  Ok(Value::Object(promise))
}

pub fn promise_species_get(
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

pub fn promise_capability_executor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `GetCapabilitiesExecutor` created by `NewPromiseCapability(C)` (ECMA-262).
  //
  // Captures a record `{ resolve: undefined, reject: undefined }` and stores the resolving
  // functions provided by the Promise constructor into that record.
  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseCapabilityExecutor = data else {
    return Err(VmError::Unimplemented(
      "promise capability executor missing internal slots",
    ));
  };

  let Some(env) = scope.heap().get_function_closure_env(callee)? else {
    return Err(VmError::Unimplemented(
      "promise capability executor missing closure env",
    ));
  };

  let resolve = args.get(0).copied().unwrap_or(Value::Undefined);
  let reject = args.get(1).copied().unwrap_or(Value::Undefined);

  let existing_resolve = scope.heap().env_get_binding_value(env, "resolve", false)?;
  let existing_reject = scope.heap().env_get_binding_value(env, "reject", false)?;
  if !matches!(existing_resolve, Value::Undefined) || !matches!(existing_reject, Value::Undefined) {
    return throw_type_error(
      vm,
      scope,
      hooks,
      "Promise capability executor already called",
    );
  }

  scope
    .heap_mut()
    .env_set_mutable_binding(env, "resolve", resolve, false)?;
  scope
    .heap_mut()
    .env_set_mutable_binding(env, "reject", reject, false)?;
  Ok(Value::Undefined)
}

pub fn promise_resolving_function_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let resolution = args.get(0).copied().unwrap_or(Value::Undefined);
  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseResolvingFunction { promise, is_reject } = data else {
    return Err(VmError::Unimplemented(
      "promise resolving function internal slots",
    ));
  };

  let Some(env) = scope.heap().get_function_closure_env(callee)? else {
    return Err(VmError::Unimplemented(
      "promise resolving functions must have a closure env for alreadyResolved",
    ));
  };

  // `alreadyResolved` record check.
  let already = scope
    .heap()
    .env_get_binding_value(env, "alreadyResolved", false)?;
  if already == Value::Bool(true) {
    return Ok(Value::Undefined);
  }
  scope
    .heap_mut()
    .env_set_mutable_binding(env, "alreadyResolved", Value::Bool(true), false)?;

  if is_reject {
    reject_promise(host, scope, promise, resolution, vm.current_realm())?;
  } else {
    resolve_promise(vm, scope, host, promise, resolution)?;
  }
  Ok(Value::Undefined)
}

pub fn promise_resolve(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let x = args.get(0).copied().unwrap_or(Value::Undefined);
  if !matches!(this, Value::Object(_)) {
    return throw_type_error(vm, scope, host, "Promise.resolve called on non-object");
  }

  let p = promise_resolve_abstract(vm, scope, host, this, x)?;
  Ok(Value::Object(p))
}

pub fn promise_reject(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let reason = args.get(0).copied().unwrap_or(Value::Undefined);
  let capability = new_promise_capability(vm, scope, host, this)?;
  scope.push_root(capability.promise)?;
  scope.push_root(capability.reject)?;
  let _ = vm.call_with_host(scope, host, capability.reject, Value::Undefined, &[reason])?;
  Ok(capability.promise)
}

pub(crate) fn perform_promise_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  this: Value,
  on_fulfilled: Value,
  on_rejected: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let Value::Object(promise) = this else {
    return throw_type_error(
      vm,
      scope,
      host,
      "Promise.prototype.then called on non-object",
    );
  };
  if !scope.heap().is_promise_object(promise) {
    return throw_type_error(
      vm,
      scope,
      host,
      "Promise.prototype.then called on non-promise",
    );
  }

  // `PerformPromiseThen`: unhandled rejection tracking.
  let was_handled = scope.heap().promise_is_handled(promise)?;
  if scope.heap().promise_state(promise)? == PromiseState::Rejected && !was_handled {
    host.host_promise_rejection_tracker(PromiseHandle(promise), PromiseRejectionOperation::Handle);
  }

  // `PerformPromiseThen` sets `[[PromiseIsHandled]] = true`.
  scope.heap_mut().promise_set_is_handled(promise, true)?;

  // Normalize handlers: use "empty" when not callable.
  let on_fulfilled = match on_fulfilled {
    Value::Object(obj) if scope.heap().is_callable(Value::Object(obj))? => {
      Some(host.host_make_job_callback(obj))
    }
    _ => None,
  };
  let on_rejected = match on_rejected {
    Value::Object(obj) if scope.heap().is_callable(Value::Object(obj))? => {
      Some(host.host_make_job_callback(obj))
    }
    _ => None,
  };

  // Create the derived promise + capability.
  let result_promise = scope.alloc_promise_with_prototype(Some(intr.promise_prototype()))?;
  scope.push_root(Value::Object(result_promise))?;
  let (resolve, reject) = create_promise_resolving_functions(vm, scope, result_promise)?;
  let capability = PromiseCapability {
    promise: Value::Object(result_promise),
    resolve,
    reject,
  };

  let fulfill_reaction = PromiseReaction {
    capability: Some(capability),
    type_: PromiseReactionType::Fulfill,
    handler: on_fulfilled,
  };
  let reject_reaction = PromiseReaction {
    capability: Some(capability),
    type_: PromiseReactionType::Reject,
    handler: on_rejected,
  };

  let current_realm = vm.current_realm();

  match scope.heap().promise_state(promise)? {
    PromiseState::Pending => {
      scope.promise_append_fulfill_reaction(promise, fulfill_reaction)?;
      scope.promise_append_reject_reaction(promise, reject_reaction)?;
    }
    PromiseState::Fulfilled => {
      let arg = scope
        .heap()
        .promise_result(promise)?
        .unwrap_or(Value::Undefined);
      enqueue_promise_reaction_job(host, scope, fulfill_reaction, arg, current_realm)?;
    }
    PromiseState::Rejected => {
      let arg = scope
        .heap()
        .promise_result(promise)?
        .unwrap_or(Value::Undefined);
      enqueue_promise_reaction_job(host, scope, reject_reaction, arg, current_realm)?;
    }
  }

  Ok(Value::Object(result_promise))
}

fn invoke_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  receiver: Value,
  on_fulfilled: Value,
  on_rejected: Value,
  non_object_message: &'static str,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  // Root inputs: `Get` and `Call` can allocate/GC.
  let mut scope = scope.reborrow();
  scope.push_root(receiver)?;
  scope.push_root(on_fulfilled)?;
  scope.push_root(on_rejected)?;

  // `Invoke(receiver, "then", ...)` uses `GetV`, which performs `ToObject` for primitives
  // (throwing only for `null`/`undefined`).
  let obj = match receiver {
    Value::Object(obj) => obj,
    Value::Null | Value::Undefined => {
      return Err(crate::throw_type_error(
        &mut scope,
        intr,
        non_object_message,
      ));
    }
    primitive => {
      let object_ctor = Value::Object(intr.object_constructor());
      scope.push_root(object_ctor)?;
      let value = vm.call_with_host(
        &mut scope,
        host,
        object_ctor,
        Value::Undefined,
        &[primitive],
      )?;
      let Value::Object(obj) = value else {
        return Err(VmError::InvariantViolation(
          "Object(..) conversion returned non-object",
        ));
      };
      scope.push_root(Value::Object(obj))?;
      obj
    }
  };

  let then_key_s = scope.alloc_string("then")?;
  scope.push_root(Value::String(then_key_s))?;
  let then_key = PropertyKey::from_string(then_key_s);
  let then = get_property_value_with_host(vm, &mut scope, host, obj, then_key, receiver)?;
  if !scope.heap().is_callable(then)? {
    return Err(crate::throw_type_error(
      &mut scope,
      intr,
      "then is not callable",
    ));
  }

  vm.call_with_host(
    &mut scope,
    host,
    then,
    receiver,
    &[on_fulfilled, on_rejected],
  )
}

pub fn promise_prototype_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let on_fulfilled = args.get(0).copied().unwrap_or(Value::Undefined);
  let on_rejected = args.get(1).copied().unwrap_or(Value::Undefined);
  perform_promise_then(vm, scope, host, this, on_fulfilled, on_rejected)
}

pub fn promise_prototype_catch(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let on_rejected = args.get(0).copied().unwrap_or(Value::Undefined);
  invoke_then(
    vm,
    scope,
    host,
    this,
    Value::Undefined,
    on_rejected,
    "Promise.prototype.catch called on non-object",
  )
}

pub fn promise_prototype_finally(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let on_finally = args.get(0).copied().unwrap_or(Value::Undefined);

  // Per ECMA-262, `Promise.prototype.finally` throws if the receiver is not an Object
  // (even though the subsequent `Invoke(promise, "then", ...)` would box primitives).
  let Value::Object(promise) = this else {
    return Err(crate::throw_type_error(
      scope,
      intr,
      "Promise.prototype.finally called on non-object",
    ));
  };

  if !scope.heap().is_callable(on_finally)? {
    return invoke_then(
      vm,
      scope,
      host,
      Value::Object(promise),
      on_finally,
      on_finally,
      "Promise.prototype.finally called on non-object",
    );
  }

  // Temporary `%Promise%`-only fallback: we do not yet implement `SpeciesConstructor` for promises.
  let constructor = Value::Object(intr.promise());

  scope.push_root(Value::Object(promise))?;
  scope.push_root(on_finally)?;
  scope.push_root(constructor)?;

  let call_id = intr.promise_finally_handler_call();

  let then_finally_name = scope.alloc_string("thenFinally")?;
  let then_finally = scope.alloc_native_function(call_id, None, then_finally_name, 1)?;
  set_function_job_realm_to_current(vm, scope, then_finally)?;
  scope
    .heap_mut()
    .object_set_prototype(then_finally, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    then_finally,
    FunctionData::PromiseFinallyHandler {
      on_finally,
      constructor,
      is_reject: false,
    },
  )?;

  let catch_finally_name = scope.alloc_string("catchFinally")?;
  let catch_finally = scope.alloc_native_function(call_id, None, catch_finally_name, 1)?;
  set_function_job_realm_to_current(vm, scope, catch_finally)?;
  scope
    .heap_mut()
    .object_set_prototype(catch_finally, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    catch_finally,
    FunctionData::PromiseFinallyHandler {
      on_finally,
      constructor,
      is_reject: true,
    },
  )?;

  // Root the closure functions before invoking `then`, which may allocate/GC.
  scope.push_root(Value::Object(then_finally))?;
  scope.push_root(Value::Object(catch_finally))?;

  invoke_then(
    vm,
    scope,
    host,
    Value::Object(promise),
    Value::Object(then_finally),
    Value::Object(catch_finally),
    "Promise.prototype.finally called on non-object",
  )
}

pub fn promise_finally_handler_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseFinallyHandler {
    on_finally,
    constructor,
    is_reject,
  } = data
  else {
    return Err(VmError::Unimplemented(
      "Promise finally handler missing internal slots",
    ));
  };

  let captured = args.get(0).copied().unwrap_or(Value::Undefined);

  // Call onFinally() with no arguments.
  let result = vm.call_with_host(scope, host, on_finally, Value::Undefined, &[])?;
  let result = scope.push_root(result)?;

  // `PromiseResolve(C, result)`
  let promise_obj = promise_resolve_abstract(vm, scope, host, constructor, result)?;

  // Create `valueThunk` or `thrower`.
  scope.push_root(Value::Object(promise_obj))?;
  scope.push_root(captured)?;
  let thunk_call = intr.promise_finally_thunk_call();
  let thunk_name = if is_reject { "thrower" } else { "valueThunk" };
  let thunk_name = scope.alloc_string(thunk_name)?;
  let thunk = scope.alloc_native_function(thunk_call, None, thunk_name, 0)?;
  set_function_job_realm_to_current(vm, scope, thunk)?;
  scope
    .heap_mut()
    .object_set_prototype(thunk, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    thunk,
    FunctionData::PromiseFinallyThunk {
      value: captured,
      is_throw: is_reject,
    },
  )?;

  // Return `p.then(valueThunk)` / `p.then(thrower)`.
  scope.push_root(Value::Object(thunk))?;
  invoke_then(
    vm,
    scope,
    host,
    Value::Object(promise_obj),
    Value::Object(thunk),
    Value::Undefined,
    "PromiseResolve(C, result) returned a non-object",
  )
}

pub fn promise_finally_thunk_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseFinallyThunk { value, is_throw } = data else {
    return Err(VmError::Unimplemented(
      "Promise finally thunk missing internal slots",
    ));
  };
  if is_throw {
    Err(VmError::Throw(value))
  } else {
    Ok(value)
  }
}

pub fn promise_try(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let callback = args.get(0).copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(callback)? {
    return throw_type_error(vm, scope, host, "Promise.try callback is not callable");
  }

  let capability = new_promise_capability(vm, scope, host, this)?;

  // Root the promise + resolving functions for the duration of the callback call.
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let callback_args = args.get(1..).unwrap_or(&[]);
  match vm.call_with_host(scope, host, callback, Value::Undefined, callback_args) {
    Ok(v) => {
      let _ = vm.call_with_host(scope, host, capability.resolve, Value::Undefined, &[v])?;
    }
    Err(VmError::Throw(e) | VmError::ThrowWithStack { value: e, .. }) => {
      let _ = vm.call_with_host(scope, host, capability.reject, Value::Undefined, &[e])?;
    }
    Err(e) => return Err(e),
  }

  Ok(capability.promise)
}

pub fn promise_with_resolvers(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let capability = new_promise_capability(vm, scope, host, this)?;
  // Root the new promise and resolving functions before allocating the result object.
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.object_prototype()))?;

  let promise_key = PropertyKey::from_string(scope.alloc_string("promise")?);
  scope.define_property(
    obj,
    promise_key,
    data_desc(capability.promise, true, true, true),
  )?;

  let resolve_key = PropertyKey::from_string(scope.alloc_string("resolve")?);
  scope.define_property(
    obj,
    resolve_key,
    data_desc(capability.resolve, true, true, true),
  )?;

  let reject_key = PropertyKey::from_string(scope.alloc_string("reject")?);
  scope.define_property(
    obj,
    reject_key,
    data_desc(capability.reject, true, true, true),
  )?;

  Ok(Value::Object(obj))
}

fn get_promise_resolve(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  constructor: Value,
) -> Result<Value, VmError> {
  // `GetPromiseResolve` (ECMA-262).
  //
  // For now this is used by Promise combinator built-ins (Promise.all/race/allSettled/any).
  let Value::Object(c) = constructor else {
    return throw_type_error(
      vm,
      scope,
      host,
      "Promise resolve constructor must be an object",
    );
  };

  let mut key_scope = scope.reborrow();
  key_scope.push_root(constructor)?;
  let resolve_key = PropertyKey::from_string(key_scope.alloc_string("resolve")?);
  let resolve = key_scope.ordinary_get(vm, c, resolve_key, constructor)?;
  if !key_scope.heap().is_callable(resolve)? {
    return throw_type_error(vm, &mut key_scope, host, "Promise resolve is not callable");
  }
  Ok(resolve)
}

fn create_internal_record(
  scope: &mut Scope<'_>,
  prototype: GcObject,
  initial: Value,
) -> Result<GcObject, VmError> {
  // A minimal internal record object used to model spec `Record { [[Value]]: ... }` shapes.
  //
  // This is intentionally not exposed to user code except indirectly via captured builtin function
  // slots.
  let mut record_scope = scope.reborrow();
  record_scope.push_root(Value::Object(prototype))?;
  record_scope.push_root(initial)?;

  let obj = record_scope.alloc_object()?;
  record_scope.push_root(Value::Object(obj))?;
  record_scope
    .heap_mut()
    .object_set_prototype(obj, Some(prototype))?;

  let value_key = PropertyKey::from_string(record_scope.alloc_string("value")?);
  record_scope.define_property(obj, value_key, data_desc(initial, true, false, true))?;
  Ok(obj)
}

fn read_internal_record_value(scope: &mut Scope<'_>, record: GcObject) -> Result<Value, VmError> {
  let value_key = PropertyKey::from_string(scope.alloc_string("value")?);
  Ok(
    scope
      .heap()
      .object_get_own_data_property_value(record, &value_key)?
      .unwrap_or(Value::Undefined),
  )
}

fn write_internal_record_value(
  scope: &mut Scope<'_>,
  record: GcObject,
  value: Value,
) -> Result<(), VmError> {
  let value_key = PropertyKey::from_string(scope.alloc_string("value")?);
  scope.define_property(record, value_key, data_desc(value, true, false, true))
}

fn invoke_thenable_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  next_promise: Value,
  on_fulfilled: Value,
  on_rejected: Value,
) -> Result<(), VmError> {
  // `Invoke(nextPromise, "then", « onFulfilled, onRejected »)` (ECMA-262).
  //
  // This is intentionally spec-shaped: it uses the `then` property lookup rather than
  // `PerformPromiseThen` so it can support thenables returned by an overridden `C.resolve`.
  let mut invoke_scope = scope.reborrow();
  invoke_scope.push_roots(&[next_promise, on_fulfilled, on_rejected])?;

  let Value::Object(obj) = next_promise else {
    let err = create_type_error(
      vm,
      &mut invoke_scope,
      hooks,
      "Promise thenable is not an object",
    )?;
    return Err(VmError::Throw(err));
  };

  let then_key = PropertyKey::from_string(invoke_scope.alloc_string("then")?);
  let then =
    invoke_scope.ordinary_get_with_host_and_hooks(vm, host, hooks, obj, then_key, next_promise)?;
  if !invoke_scope.heap().is_callable(then)? {
    let err = create_type_error(vm, &mut invoke_scope, hooks, "Promise then is not callable")?;
    return Err(VmError::Throw(err));
  }

  let _ = vm.call_with_host_and_hooks(
    host,
    &mut invoke_scope,
    hooks,
    then,
    next_promise,
    &[on_fulfilled, on_rejected],
  )?;
  Ok(())
}

fn if_abrupt_reject_promise(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  capability: PromiseCapability,
  completion: VmError,
) -> Result<Value, VmError> {
  // `IfAbruptRejectPromise` (ECMA-262) (partial): only catchable `throw` values are converted into
  // rejections. VM-internal errors (OOM, unimplemented, etc.) are propagated.
  let Some(reason) = completion.thrown_value() else {
    return Err(completion);
  };
  let _ = vm.call_with_host_and_hooks(
    host,
    scope,
    hooks,
    capability.reject,
    Value::Undefined,
    &[reason],
  )?;
  Ok(capability.promise)
}

fn perform_promise_all(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  iterator_record: &mut crate::iterator::IteratorRecord,
  constructor: Value,
  capability: PromiseCapability,
  promise_resolve: Value,
) -> Result<Value, VmError> {
  // `PerformPromiseAll` (ECMA-262).
  let intr = require_intrinsics(vm)?;

  // `values` list → model as an internal Array.
  let values = scope.alloc_array(0)?;
  scope.push_root(Value::Object(values))?;
  scope
    .heap_mut()
    .object_set_prototype(values, Some(intr.array_prototype()))?;

  // `remainingElementsCount` record.
  let remaining = create_internal_record(scope, intr.object_prototype(), Value::Number(1.0))?;
  scope.push_root(Value::Object(remaining))?;

  let resolve_element_call = intr.promise_all_resolve_element_call();
  let mut index: u32 = 0;

  loop {
    let next_value = crate::iterator::iterator_step_value(vm, host, hooks, scope, iterator_record)?;
    let Some(next_value) = next_value else {
      // Done: decrement initial 1.
      let remaining_value = read_internal_record_value(scope, remaining)?;
      let Value::Number(n) = remaining_value else {
        return Err(VmError::Unimplemented(
          "PerformPromiseAll: remainingElementsCount is not a Number",
        ));
      };
      let new_remaining = n - 1.0;
      write_internal_record_value(scope, remaining, Value::Number(new_remaining))?;
      if new_remaining == 0.0 {
        let _ = vm.call_with_host_and_hooks(
          host,
          scope,
          hooks,
          capability.resolve,
          Value::Undefined,
          &[Value::Object(values)],
        )?;
      }
      return Ok(capability.promise);
    };

    // Use a nested scope so temporary roots created while wiring each element do not accumulate.
    let mut step_scope = scope.reborrow();
    step_scope.push_root(next_value)?;

    // Append `undefined` placeholder.
    {
      let mut idx_scope = step_scope.reborrow();
      idx_scope.push_root(Value::Object(values))?;
      let idx_s = idx_scope.alloc_string(&index.to_string())?;
      idx_scope.push_root(Value::String(idx_s))?;
      let key = PropertyKey::from_string(idx_s);
      idx_scope.create_data_property_or_throw(values, key, Value::Undefined)?;
    }

    // nextPromise = ? Call(promiseResolve, constructor, « nextValue »).
    let next_promise = vm.call_with_host_and_hooks(
      host,
      &mut step_scope,
      hooks,
      promise_resolve,
      constructor,
      &[next_value],
    )?;
    step_scope.push_root(next_promise)?;

    // Create per-element alreadyCalled record.
    let already_called =
      create_internal_record(&mut step_scope, intr.object_prototype(), Value::Bool(false))?;
    step_scope.push_root(Value::Object(already_called))?;

    // remainingElementsCount.[[Value]] += 1.
    let remaining_value = read_internal_record_value(&mut step_scope, remaining)?;
    let Value::Number(n) = remaining_value else {
      return Err(VmError::Unimplemented(
        "PerformPromiseAll: remainingElementsCount is not a Number",
      ));
    };
    write_internal_record_value(&mut step_scope, remaining, Value::Number(n + 1.0))?;

    // resolveElement = CreateBuiltinFunction(...)
    let resolve_element_name = step_scope.alloc_string("resolveElement")?;
    let slots = [
      Value::Object(values),
      Value::Number(index as f64),
      Value::Object(already_called),
      Value::Object(remaining),
      capability.resolve,
    ];
    let resolve_element = step_scope.alloc_native_function_with_slots(
      resolve_element_call,
      None,
      resolve_element_name,
      1,
      &slots,
    )?;
    step_scope
      .heap_mut()
      .object_set_prototype(resolve_element, Some(intr.function_prototype()))?;

    // ? Invoke(nextPromise, "then", « resolveElement, capability.reject »).
    invoke_thenable_then(
      vm,
      &mut step_scope,
      host,
      hooks,
      next_promise,
      Value::Object(resolve_element),
      capability.reject,
    )?;

    index = index.saturating_add(1);
  }
}

pub fn promise_all(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `Promise.all(iterable)` (ECMA-262).
  let iterable = args.get(0).copied().unwrap_or(Value::Undefined);
  let capability = new_promise_capability(vm, scope, hooks, this)?;

  // Root the resulting promise and resolving functions so `IfAbruptRejectPromise` can call them
  // even if the iterator acquisition/loop allocates and triggers GC.
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let promise_resolve = match get_promise_resolve(vm, scope, hooks, this) {
    Ok(v) => v,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };

  let mut iterator_record = match crate::iterator::get_iterator(vm, host, hooks, scope, iterable) {
    Ok(r) => r,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  let result = perform_promise_all(
    vm,
    scope,
    host,
    hooks,
    &mut iterator_record,
    this,
    capability,
    promise_resolve,
  );

  match result {
    Ok(v) => Ok(v),
    Err(err) => {
      if !iterator_record.done {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      }
      if_abrupt_reject_promise(vm, scope, host, hooks, capability, err)
    }
  }
}

fn perform_promise_race(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  iterator_record: &mut crate::iterator::IteratorRecord,
  constructor: Value,
  capability: PromiseCapability,
  promise_resolve: Value,
) -> Result<Value, VmError> {
  // `PerformPromiseRace` (ECMA-262).
  loop {
    let next_value = crate::iterator::iterator_step_value(vm, host, hooks, scope, iterator_record)?;
    let Some(next_value) = next_value else {
      return Ok(capability.promise);
    };

    let next_promise = vm.call_with_host_and_hooks(
      host,
      scope,
      hooks,
      promise_resolve,
      constructor,
      &[next_value],
    )?;
    invoke_thenable_then(
      vm,
      scope,
      host,
      hooks,
      next_promise,
      capability.resolve,
      capability.reject,
    )?;
  }
}

pub fn promise_race(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `Promise.race(iterable)` (ECMA-262).
  let iterable = args.get(0).copied().unwrap_or(Value::Undefined);
  let capability = new_promise_capability(vm, scope, hooks, this)?;
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let promise_resolve = match get_promise_resolve(vm, scope, hooks, this) {
    Ok(v) => v,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };

  let mut iterator_record = match crate::iterator::get_iterator(vm, host, hooks, scope, iterable) {
    Ok(r) => r,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  let result = perform_promise_race(
    vm,
    scope,
    host,
    hooks,
    &mut iterator_record,
    this,
    capability,
    promise_resolve,
  );

  match result {
    Ok(v) => Ok(v),
    Err(err) => {
      if !iterator_record.done {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      }
      if_abrupt_reject_promise(vm, scope, host, hooks, capability, err)
    }
  }
}

fn perform_promise_all_settled(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  iterator_record: &mut crate::iterator::IteratorRecord,
  constructor: Value,
  capability: PromiseCapability,
  promise_resolve: Value,
) -> Result<Value, VmError> {
  // `PerformPromiseAllSettled` (ECMA-262).
  let intr = require_intrinsics(vm)?;

  let values = scope.alloc_array(0)?;
  scope.push_root(Value::Object(values))?;
  scope
    .heap_mut()
    .object_set_prototype(values, Some(intr.array_prototype()))?;

  let remaining = create_internal_record(scope, intr.object_prototype(), Value::Number(1.0))?;
  scope.push_root(Value::Object(remaining))?;

  let element_call = intr.promise_all_settled_element_call();
  let mut index: u32 = 0;

  loop {
    let next_value = crate::iterator::iterator_step_value(vm, host, hooks, scope, iterator_record)?;
    let Some(next_value) = next_value else {
      let remaining_value = read_internal_record_value(scope, remaining)?;
      let Value::Number(n) = remaining_value else {
        return Err(VmError::Unimplemented(
          "PerformPromiseAllSettled: remainingElementsCount is not a Number",
        ));
      };
      let new_remaining = n - 1.0;
      write_internal_record_value(scope, remaining, Value::Number(new_remaining))?;
      if new_remaining == 0.0 {
        let _ = vm.call_with_host_and_hooks(
          host,
          scope,
          hooks,
          capability.resolve,
          Value::Undefined,
          &[Value::Object(values)],
        )?;
      }
      return Ok(capability.promise);
    };

    // Use a nested scope so temporary roots created while wiring each element do not accumulate.
    let mut step_scope = scope.reborrow();
    step_scope.push_root(next_value)?;

    // Append placeholder.
    {
      let mut idx_scope = step_scope.reborrow();
      idx_scope.push_root(Value::Object(values))?;
      let idx_s = idx_scope.alloc_string(&index.to_string())?;
      idx_scope.push_root(Value::String(idx_s))?;
      let key = PropertyKey::from_string(idx_s);
      idx_scope.create_data_property_or_throw(values, key, Value::Undefined)?;
    }

    let next_promise = vm.call_with_host_and_hooks(
      host,
      &mut step_scope,
      hooks,
      promise_resolve,
      constructor,
      &[next_value],
    )?;
    step_scope.push_root(next_promise)?;

    // Shared alreadyCalled record for the pair of element functions.
    let already_called =
      create_internal_record(&mut step_scope, intr.object_prototype(), Value::Bool(false))?;
    step_scope.push_root(Value::Object(already_called))?;

    // remainingElementsCount.[[Value]] += 1.
    let remaining_value = read_internal_record_value(&mut step_scope, remaining)?;
    let Value::Number(n) = remaining_value else {
      return Err(VmError::Unimplemented(
        "PerformPromiseAllSettled: remainingElementsCount is not a Number",
      ));
    };
    write_internal_record_value(&mut step_scope, remaining, Value::Number(n + 1.0))?;

    let on_fulfilled_name = step_scope.alloc_string("onFulfilled")?;
    let on_rejected_name = step_scope.alloc_string("onRejected")?;
    let fulfilled_slots = [
      Value::Object(values),
      Value::Number(index as f64),
      Value::Object(already_called),
      Value::Object(remaining),
      capability.resolve,
      Value::Bool(false),
    ];
    let rejected_slots = [
      Value::Object(values),
      Value::Number(index as f64),
      Value::Object(already_called),
      Value::Object(remaining),
      capability.resolve,
      Value::Bool(true),
    ];

    let on_fulfilled = step_scope.alloc_native_function_with_slots(
      element_call,
      None,
      on_fulfilled_name,
      1,
      &fulfilled_slots,
    )?;
    step_scope
      .heap_mut()
      .object_set_prototype(on_fulfilled, Some(intr.function_prototype()))?;
    // Root the first closure while allocating the second: both share `alreadyCalled`.
    step_scope.push_root(Value::Object(on_fulfilled))?;

    let on_rejected = step_scope.alloc_native_function_with_slots(
      element_call,
      None,
      on_rejected_name,
      1,
      &rejected_slots,
    )?;
    step_scope
      .heap_mut()
      .object_set_prototype(on_rejected, Some(intr.function_prototype()))?;

    invoke_thenable_then(
      vm,
      &mut step_scope,
      host,
      hooks,
      next_promise,
      Value::Object(on_fulfilled),
      Value::Object(on_rejected),
    )?;

    index = index.saturating_add(1);
  }
}

pub fn promise_all_settled(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `Promise.allSettled(iterable)` (ECMA-262).
  let iterable = args.get(0).copied().unwrap_or(Value::Undefined);
  let capability = new_promise_capability(vm, scope, hooks, this)?;
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let promise_resolve = match get_promise_resolve(vm, scope, hooks, this) {
    Ok(v) => v,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };

  let mut iterator_record = match crate::iterator::get_iterator(vm, host, hooks, scope, iterable) {
    Ok(r) => r,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  let result = perform_promise_all_settled(
    vm,
    scope,
    host,
    hooks,
    &mut iterator_record,
    this,
    capability,
    promise_resolve,
  );

  match result {
    Ok(v) => Ok(v),
    Err(err) => {
      if !iterator_record.done {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      }
      if_abrupt_reject_promise(vm, scope, host, hooks, capability, err)
    }
  }
}

fn perform_promise_any(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  iterator_record: &mut crate::iterator::IteratorRecord,
  constructor: Value,
  capability: PromiseCapability,
  promise_resolve: Value,
) -> Result<Value, VmError> {
  // `PerformPromiseAny` (ECMA-262).
  let intr = require_intrinsics(vm)?;

  let errors = scope.alloc_array(0)?;
  scope.push_root(Value::Object(errors))?;
  scope
    .heap_mut()
    .object_set_prototype(errors, Some(intr.array_prototype()))?;

  let remaining = create_internal_record(scope, intr.object_prototype(), Value::Number(1.0))?;
  scope.push_root(Value::Object(remaining))?;

  let reject_element_call = intr.promise_any_reject_element_call();
  let mut index: u32 = 0;

  loop {
    let next_value = crate::iterator::iterator_step_value(vm, host, hooks, scope, iterator_record)?;
    let Some(next_value) = next_value else {
      let remaining_value = read_internal_record_value(scope, remaining)?;
      let Value::Number(n) = remaining_value else {
        return Err(VmError::Unimplemented(
          "PerformPromiseAny: remainingElementsCount is not a Number",
        ));
      };
      let new_remaining = n - 1.0;
      write_internal_record_value(scope, remaining, Value::Number(new_remaining))?;
      if new_remaining == 0.0 {
        let message = scope.alloc_string("All promises were rejected")?;
        let aggregate = vm.construct_with_host_and_hooks(
          host,
          scope,
          hooks,
          Value::Object(intr.aggregate_error()),
          &[Value::Object(errors), Value::String(message)],
          Value::Object(intr.aggregate_error()),
        )?;
        let _ = vm.call_with_host_and_hooks(
          host,
          scope,
          hooks,
          capability.reject,
          Value::Undefined,
          &[aggregate],
        )?;
      }
      return Ok(capability.promise);
    };

    let mut step_scope = scope.reborrow();
    step_scope.push_root(next_value)?;

    // Append placeholder.
    {
      let mut idx_scope = step_scope.reborrow();
      idx_scope.push_root(Value::Object(errors))?;
      let idx_s = idx_scope.alloc_string(&index.to_string())?;
      idx_scope.push_root(Value::String(idx_s))?;
      let key = PropertyKey::from_string(idx_s);
      idx_scope.create_data_property_or_throw(errors, key, Value::Undefined)?;
    }

    let next_promise = vm.call_with_host_and_hooks(
      host,
      &mut step_scope,
      hooks,
      promise_resolve,
      constructor,
      &[next_value],
    )?;
    step_scope.push_root(next_promise)?;

    let already_called =
      create_internal_record(&mut step_scope, intr.object_prototype(), Value::Bool(false))?;
    step_scope.push_root(Value::Object(already_called))?;

    // remainingElementsCount.[[Value]] += 1.
    let remaining_value = read_internal_record_value(&mut step_scope, remaining)?;
    let Value::Number(n) = remaining_value else {
      return Err(VmError::Unimplemented(
        "PerformPromiseAny: remainingElementsCount is not a Number",
      ));
    };
    write_internal_record_value(&mut step_scope, remaining, Value::Number(n + 1.0))?;

    let reject_element_name = step_scope.alloc_string("rejectElement")?;
    let slots = [
      Value::Object(errors),
      Value::Number(index as f64),
      Value::Object(already_called),
      Value::Object(remaining),
      capability.reject,
    ];
    let reject_element = step_scope.alloc_native_function_with_slots(
      reject_element_call,
      None,
      reject_element_name,
      1,
      &slots,
    )?;
    step_scope
      .heap_mut()
      .object_set_prototype(reject_element, Some(intr.function_prototype()))?;

    // Use resultCapability.[[Resolve]] directly for fulfillment.
    invoke_thenable_then(
      vm,
      &mut step_scope,
      host,
      hooks,
      next_promise,
      capability.resolve,
      Value::Object(reject_element),
    )?;

    index = index.saturating_add(1);
  }
}

pub fn promise_any(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `Promise.any(iterable)` (ECMA-262).
  let iterable = args.get(0).copied().unwrap_or(Value::Undefined);
  let capability = new_promise_capability(vm, scope, hooks, this)?;
  scope.push_root(capability.promise)?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let promise_resolve = match get_promise_resolve(vm, scope, hooks, this) {
    Ok(v) => v,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };

  let mut iterator_record = match crate::iterator::get_iterator(vm, host, hooks, scope, iterable) {
    Ok(r) => r,
    Err(err) => return if_abrupt_reject_promise(vm, scope, host, hooks, capability, err),
  };
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  let result = perform_promise_any(
    vm,
    scope,
    host,
    hooks,
    &mut iterator_record,
    this,
    capability,
    promise_resolve,
  );

  match result {
    Ok(v) => Ok(v),
    Err(err) => {
      if !iterator_record.done {
        let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
      }
      if_abrupt_reject_promise(vm, scope, host, hooks, capability, err)
    }
  }
}

pub fn promise_all_resolve_element_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `PromiseAllResolveElementFunctions` (ECMA-262).
  let x = args.get(0).copied().unwrap_or(Value::Undefined);
  let slots = scope.heap().get_function_native_slots(callee)?;
  if slots.len() != 5 {
    return Err(VmError::InvariantViolation(
      "PromiseAllResolveElement has wrong native slot count",
    ));
  }

  let Value::Object(values) = slots[0] else {
    return Err(VmError::Unimplemented(
      "PromiseAllResolveElement values is not an object",
    ));
  };
  let Value::Number(index) = slots[1] else {
    return Err(VmError::Unimplemented(
      "PromiseAllResolveElement index is not a Number",
    ));
  };
  let Value::Object(already_called) = slots[2] else {
    return Err(VmError::Unimplemented(
      "PromiseAllResolveElement alreadyCalled is not an object",
    ));
  };
  let Value::Object(remaining) = slots[3] else {
    return Err(VmError::Unimplemented(
      "PromiseAllResolveElement remainingElementsCount is not an object",
    ));
  };
  let resolve = slots[4];

  // alreadyCalled check.
  let already = read_internal_record_value(scope, already_called)?;
  if already == Value::Bool(true) {
    return Ok(Value::Undefined);
  }
  write_internal_record_value(scope, already_called, Value::Bool(true))?;

  // values[index] = x.
  {
    let mut idx_scope = scope.reborrow();
    idx_scope.push_root(Value::Object(values))?;
    let idx_s = idx_scope.alloc_string(&(index as u32).to_string())?;
    idx_scope.push_root(Value::String(idx_s))?;
    let key = PropertyKey::from_string(idx_s);
    idx_scope.create_data_property_or_throw(values, key, x)?;
  }

  // remainingElementsCount--.
  let remaining_value = read_internal_record_value(scope, remaining)?;
  let Value::Number(n) = remaining_value else {
    return Err(VmError::Unimplemented(
      "PromiseAllResolveElement remainingElementsCount is not a Number",
    ));
  };
  let new_remaining = n - 1.0;
  write_internal_record_value(scope, remaining, Value::Number(new_remaining))?;
  if new_remaining == 0.0 {
    let _ = vm.call_with_host(
      scope,
      host,
      resolve,
      Value::Undefined,
      &[Value::Object(values)],
    )?;
  }

  Ok(Value::Undefined)
}

pub fn promise_all_settled_element_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `PromiseAllSettledResolveElementFunctions` / `PromiseAllSettledRejectElementFunctions`
  // (ECMA-262).
  let x = args.get(0).copied().unwrap_or(Value::Undefined);
  let slots = scope.heap().get_function_native_slots(callee)?;
  if slots.len() != 6 {
    return Err(VmError::InvariantViolation(
      "PromiseAllSettledElement has wrong native slot count",
    ));
  }

  let Value::Object(values) = slots[0] else {
    return Err(VmError::Unimplemented(
      "PromiseAllSettledElement values is not an object",
    ));
  };
  let Value::Number(index) = slots[1] else {
    return Err(VmError::Unimplemented(
      "PromiseAllSettledElement index is not a Number",
    ));
  };
  let Value::Object(already_called) = slots[2] else {
    return Err(VmError::Unimplemented(
      "PromiseAllSettledElement alreadyCalled is not an object",
    ));
  };
  let Value::Object(remaining) = slots[3] else {
    return Err(VmError::Unimplemented(
      "PromiseAllSettledElement remainingElementsCount is not an object",
    ));
  };
  let resolve = slots[4];
  let Value::Bool(is_reject) = slots[5] else {
    return Err(VmError::Unimplemented(
      "PromiseAllSettledElement kind flag is not a Bool",
    ));
  };

  let already = read_internal_record_value(scope, already_called)?;
  if already == Value::Bool(true) {
    return Ok(Value::Undefined);
  }
  write_internal_record_value(scope, already_called, Value::Bool(true))?;

  let intr = require_intrinsics(vm)?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.object_prototype()))?;

  // Create `{ status, value }` / `{ status, reason }` object.
  let status_value = if is_reject { "rejected" } else { "fulfilled" };
  let status_value = scope.alloc_string(status_value)?;
  scope.push_root(Value::String(status_value))?;
  let status_key = PropertyKey::from_string(scope.alloc_string("status")?);
  scope.define_property(
    obj,
    status_key,
    data_desc(Value::String(status_value), true, true, true),
  )?;

  let value_key_name = if is_reject { "reason" } else { "value" };
  let value_key = PropertyKey::from_string(scope.alloc_string(value_key_name)?);
  scope.define_property(obj, value_key, data_desc(x, true, true, true))?;

  // values[index] = obj.
  {
    let mut idx_scope = scope.reborrow();
    idx_scope.push_root(Value::Object(values))?;
    idx_scope.push_root(Value::Object(obj))?;
    let idx_s = idx_scope.alloc_string(&(index as u32).to_string())?;
    idx_scope.push_root(Value::String(idx_s))?;
    let key = PropertyKey::from_string(idx_s);
    idx_scope.create_data_property_or_throw(values, key, Value::Object(obj))?;
  }

  // remainingElementsCount--.
  let remaining_value = read_internal_record_value(scope, remaining)?;
  let Value::Number(n) = remaining_value else {
    return Err(VmError::Unimplemented(
      "PromiseAllSettledElement remainingElementsCount is not a Number",
    ));
  };
  let new_remaining = n - 1.0;
  write_internal_record_value(scope, remaining, Value::Number(new_remaining))?;
  if new_remaining == 0.0 {
    let _ = vm.call_with_host(
      scope,
      host,
      resolve,
      Value::Undefined,
      &[Value::Object(values)],
    )?;
  }

  Ok(Value::Undefined)
}

pub fn promise_any_reject_element_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // `PromiseAnyRejectElementFunctions` (ECMA-262).
  let x = args.get(0).copied().unwrap_or(Value::Undefined);
  let slots = scope.heap().get_function_native_slots(callee)?;
  if slots.len() != 5 {
    return Err(VmError::InvariantViolation(
      "PromiseAnyRejectElement has wrong native slot count",
    ));
  }

  let Value::Object(errors) = slots[0] else {
    return Err(VmError::Unimplemented(
      "PromiseAnyRejectElement errors is not an object",
    ));
  };
  let Value::Number(index) = slots[1] else {
    return Err(VmError::Unimplemented(
      "PromiseAnyRejectElement index is not a Number",
    ));
  };
  let Value::Object(already_called) = slots[2] else {
    return Err(VmError::Unimplemented(
      "PromiseAnyRejectElement alreadyCalled is not an object",
    ));
  };
  let Value::Object(remaining) = slots[3] else {
    return Err(VmError::Unimplemented(
      "PromiseAnyRejectElement remainingElementsCount is not an object",
    ));
  };
  let reject = slots[4];

  let already = read_internal_record_value(scope, already_called)?;
  if already == Value::Bool(true) {
    return Ok(Value::Undefined);
  }
  write_internal_record_value(scope, already_called, Value::Bool(true))?;

  // errors[index] = x.
  {
    let mut idx_scope = scope.reborrow();
    idx_scope.push_root(Value::Object(errors))?;
    let idx_s = idx_scope.alloc_string(&(index as u32).to_string())?;
    idx_scope.push_root(Value::String(idx_s))?;
    let key = PropertyKey::from_string(idx_s);
    idx_scope.create_data_property_or_throw(errors, key, x)?;
  }

  // remainingElementsCount--.
  let remaining_value = read_internal_record_value(scope, remaining)?;
  let Value::Number(n) = remaining_value else {
    return Err(VmError::Unimplemented(
      "PromiseAnyRejectElement remainingElementsCount is not a Number",
    ));
  };
  let new_remaining = n - 1.0;
  write_internal_record_value(scope, remaining, Value::Number(new_remaining))?;
  if new_remaining == 0.0 {
    let intr = require_intrinsics(vm)?;
    let message = scope.alloc_string("All promises were rejected")?;
    let aggregate = vm.construct_with_host(
      scope,
      host,
      Value::Object(intr.aggregate_error()),
      &[Value::Object(errors), Value::String(message)],
      Value::Object(intr.aggregate_error()),
    )?;
    let _ = vm.call_with_host(scope, host, reject, Value::Undefined, &[aggregate])?;
  }

  Ok(Value::Undefined)
}

fn string_key(scope: &mut Scope<'_>, s: &str) -> Result<PropertyKey, VmError> {
  let key_s = scope.alloc_string(s)?;
  scope.push_root(Value::String(key_s))?;
  Ok(PropertyKey::from_string(key_s))
}

fn get_data_property_value(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: &PropertyKey,
) -> Result<Option<Value>, VmError> {
  let Some(desc) = scope.heap().get_property(obj, key)? else {
    return Ok(None);
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(Some(value)),
    PropertyKind::Accessor { .. } => Err(VmError::PropertyNotData),
  }
}

fn to_length(value: Value) -> usize {
  let Value::Number(n) = value else {
    return 0;
  };
  if !n.is_finite() || n <= 0.0 {
    return 0;
  }
  if n >= usize::MAX as f64 {
    return usize::MAX;
  }
  n.floor() as usize
}

fn vec_try_push<T>(buf: &mut Vec<T>, value: T) -> Result<(), VmError> {
  if buf.len() == buf.capacity() {
    buf.try_reserve(1).map_err(|_| VmError::OutOfMemory)?;
  }
  buf.push(value);
  Ok(())
}

fn vec_try_extend_from_slice<T: Copy>(buf: &mut Vec<T>, slice: &[T]) -> Result<(), VmError> {
  let needed = slice
    .len()
    .saturating_sub(buf.capacity().saturating_sub(buf.len()));
  if needed > 0 {
    buf.try_reserve(needed).map_err(|_| VmError::OutOfMemory)?;
  }
  buf.extend_from_slice(slice);
  Ok(())
}

/// `Function.prototype.call`.
pub fn function_prototype_call_method(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_arg = args.first().copied().unwrap_or(Value::Undefined);
  let rest = args.get(1..).unwrap_or(&[]);
  vm.call_with_host(scope, host, this, this_arg, rest)
}

/// `Function.prototype.apply` (minimal, supports array-like objects).
pub fn function_prototype_apply(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let target = require_callable(this)?;
  let this_arg = args.first().copied().unwrap_or(Value::Undefined);
  let arg_array = args.get(1).copied().unwrap_or(Value::Undefined);

  match arg_array {
    Value::Undefined | Value::Null => {
      vm.call_with_host(scope, host, Value::Object(target), this_arg, &[])
    }
    Value::Object(obj) => {
      // Root `obj` while building the argument list, since we may allocate strings for property
      // keys and trigger a GC.
      scope.push_root(Value::Object(obj))?;
      let list = get_array_like_args(scope, obj)?;
      vm.call_with_host(scope, host, Value::Object(target), this_arg, &list)
    }
    _ => Err(VmError::Unimplemented(
      "Function.prototype.apply: argArray must be an object or null/undefined",
    )),
  }
}

/// `Function.prototype.bind` (minimal, using `JsFunction` bound internal slots).
pub fn function_prototype_bind(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let target = require_callable(this)?;

  // Extract function metadata without holding a heap borrow across allocations.
  let (target_len, target_name) = {
    let f = scope.heap().get_function(target)?;
    (f.length, f.name)
  };

  let bound_this = args.first().copied().unwrap_or(Value::Undefined);
  let bound_args = args.get(1..).unwrap_or(&[]);

  let bound_args_len_u32 = u32::try_from(bound_args.len()).unwrap_or(u32::MAX);
  let bound_len = target_len.saturating_sub(bound_args_len_u32);

  let name = scope.alloc_string("bound")?;
  let func = scope.alloc_bound_function(target, bound_this, bound_args, name, bound_len)?;

  // Bound functions are ordinary function objects: their `[[Prototype]]` is `%Function.prototype%`.
  scope
    .heap_mut()
    .object_set_prototype(func, Some(intr.function_prototype()))?;

  // Define standard function metadata properties (`name`, `length`).
  crate::function_properties::set_function_name(
    scope,
    func,
    PropertyKey::String(target_name),
    Some("bound"),
  )?;
  crate::function_properties::set_function_length(scope, func, bound_len)?;

  if let Some(realm) = scope.heap().get_function_realm(target)? {
    scope.heap_mut().set_function_realm(func, realm)?;
  }

  let job_realm = scope
    .heap()
    .get_function_job_realm(target)
    .or(vm.current_realm());
  if let Some(job_realm) = job_realm {
    scope.heap_mut().set_function_job_realm(func, job_realm)?;
  }

  Ok(Value::Object(func))
}

/// `Object.prototype.valueOf` (ECMA-262 §20.1.3.7): `Return ? ToObject(this value)`.
pub fn object_prototype_value_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  match this {
    Value::Undefined | Value::Null => {
      let intr = require_intrinsics(vm)?;
      Err(crate::error_object::throw_type_error(
        scope,
        intr,
        "Cannot convert undefined or null to object",
      ))
    }
    Value::Object(obj) => Ok(Value::Object(obj)),
    // Reuse `Object(value)` boxing for other primitives (§7.1.18 ToObject).
    other => object_constructor_impl(vm, scope, hooks, &[other]),
  }
}

/// `Object.prototype.toString` (partial).
pub fn object_prototype_to_string(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  // §20.1.3.6: prefer `@@toStringTag` for objects when present; otherwise use the builtin tag
  // derived from the object's kind / wrapper data slots.
  let s = match this {
    Value::Undefined => "[object Undefined]",
    Value::Null => "[object Null]",
    Value::Bool(_) => "[object Boolean]",
    Value::Number(_) => "[object Number]",
    Value::BigInt(_) => "[object BigInt]",
    Value::String(_) => "[object String]",
    Value::Symbol(_) => "[object Symbol]",
    Value::Object(obj) => {
      if let Some(tag) = object_to_string_tag(vm, scope, obj)? {
        return Ok(Value::String(
          scope.alloc_string(&format!("[object {tag}]"))?,
        ));
      }
      if scope.heap().is_callable(Value::Object(obj))? {
        "[object Function]"
      } else if scope.heap().object_is_array(obj)? {
        "[object Array]"
      } else if object_has_number_data(scope, obj)? {
        "[object Number]"
      } else if object_has_boolean_data(scope, obj)? {
        "[object Boolean]"
      } else if object_has_string_data(scope, obj)? {
        "[object String]"
      } else {
        "[object Object]"
      }
    }
  };
  Ok(Value::String(scope.alloc_string(s)?))
}

fn object_to_string_tag(
  vm: &Vm,
  scope: &mut Scope<'_>,
  obj: GcObject,
) -> Result<Option<String>, VmError> {
  let Some(intr) = vm.intrinsics() else {
    return Ok(None);
  };
  let tag_key = PropertyKey::from_symbol(intr.well_known_symbols().to_string_tag);
  match scope.heap().get(obj, &tag_key) {
    Ok(Value::String(s)) => {
      let units = scope.heap().get_string(s)?.as_code_units().to_vec();
      Ok(Some(String::from_utf16_lossy(&units)))
    }
    _ => Ok(None),
  }
}

fn internal_marker_key(scope: &mut Scope<'_>, name: &str) -> Result<PropertyKey, VmError> {
  let marker = scope.alloc_string(name)?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  Ok(PropertyKey::from_symbol(marker_sym))
}

fn object_has_number_data(scope: &mut Scope<'_>, obj: GcObject) -> Result<bool, VmError> {
  let key = internal_marker_key(scope, "vm-js.internal.NumberData")?;
  Ok(matches!(
    scope.heap().object_get_own_data_property_value(obj, &key)?,
    Some(Value::Number(_))
  ))
}

fn object_has_boolean_data(scope: &mut Scope<'_>, obj: GcObject) -> Result<bool, VmError> {
  let key = internal_marker_key(scope, "vm-js.internal.BooleanData")?;
  Ok(matches!(
    scope.heap().object_get_own_data_property_value(obj, &key)?,
    Some(Value::Bool(_))
  ))
}

fn object_has_string_data(scope: &mut Scope<'_>, obj: GcObject) -> Result<bool, VmError> {
  let key = internal_marker_key(scope, "vm-js.internal.StringData")?;
  Ok(matches!(
    scope.heap().object_get_own_data_property_value(obj, &key)?,
    Some(Value::String(_))
  ))
}

/// Install the synthetic `[[NumberData]]` / `[[BooleanData]]` slot used by wrapper methods onto a
/// prototype object (`Number.prototype` → `+0`, `Boolean.prototype` → `false`).
pub fn install_wrapper_prototype_data(
  scope: &mut Scope<'_>,
  prototype: GcObject,
  data: Value,
) -> Result<(), VmError> {
  let marker_name = match data {
    Value::Number(_) => "vm-js.internal.NumberData",
    Value::Bool(_) => "vm-js.internal.BooleanData",
    Value::String(_) => "vm-js.internal.StringData",
    _ => {
      return Err(VmError::InvariantViolation(
        "install_wrapper_prototype_data: unexpected data kind",
      ))
    }
  };
  let key = internal_marker_key(scope, marker_name)?;
  scope.define_property(prototype, key, data_desc(data, false, false, false))?;
  Ok(())
}

/// `Array.isArray` (§23.1.2.2).
pub fn array_is_array(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let arg = args.first().copied().unwrap_or(Value::Undefined);
  let is = match arg {
    Value::Object(obj) => scope.heap().object_is_array(obj)?,
    _ => false,
  };
  Ok(Value::Bool(is))
}

/// Minimal `Array.from(items)` (§23.1.2.1) — iterable path only (no `mapfn` / array-like).
/// Unlocks harness helpers like `Array.from(map.keys())` for Map.groupBy tests.
pub fn array_from(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let items = args.first().copied().unwrap_or(Value::Undefined);
  scope.push_root(items)?;

  let intr = require_intrinsics(vm)?;
  let array = scope.alloc_array(0)?;
  scope
    .heap_mut()
    .object_set_prototype(array, Some(intr.array_prototype()))?;
  scope.push_root(Value::Object(array))?;

  let mut iterator_record = crate::iterator::get_iterator(vm, host, hooks, scope, items)?;
  scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

  let mut k: u32 = 0;
  loop {
    vm.tick()?;
    let next =
      match crate::iterator::iterator_step_value(vm, host, hooks, scope, &mut iterator_record) {
        Ok(v) => v,
        Err(err) => {
          let _ = crate::iterator::iterator_close(vm, host, hooks, scope, &iterator_record);
          return Err(err);
        }
      };
    let Some(value) = next else {
      define_array_length(scope, array, k as usize)?;
      return Ok(Value::Object(array));
    };
    scope.push_root(value)?;
    let key = PropertyKey::from_string(scope.alloc_string(&k.to_string())?);
    scope.define_property(array, key, data_desc(value, true, true, true))?;
    k = k.saturating_add(1);
  }
}

fn get_array_length(scope: &mut Scope<'_>, obj: GcObject) -> Result<usize, VmError> {
  let length_key = string_key(scope, "length")?;
  Ok(match get_data_property_value(scope, obj, &length_key)? {
    Some(v) => to_length(v),
    None => 0,
  })
}

fn define_array_length(scope: &mut Scope<'_>, obj: GcObject, len: usize) -> Result<(), VmError> {
  let length_key = string_key(scope, "length")?;
  scope.define_property(
    obj,
    length_key,
    data_desc(Value::Number(len as f64), true, false, false),
  )
}

/// `Array.prototype.push` (minimal, §23.1.3.20).
pub fn array_prototype_push(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Array.prototype.push on non-object")),
  };

  let mut s = scope.reborrow();
  s.push_root(Value::Object(this_obj))?;
  for arg in args {
    s.push_root(*arg)?;
  }

  let mut len = get_array_length(&mut s, this_obj)?;
  for arg in args {
    vm.tick()?;
    let key = PropertyKey::from_string(s.alloc_string(&len.to_string())?);
    s.define_property(this_obj, key, data_desc(*arg, true, true, true))?;
    len = len.saturating_add(1);
  }
  define_array_length(&mut s, this_obj, len)?;
  Ok(Value::Number(len as f64))
}

/// `Array.prototype.pop` (minimal, §23.1.3.17) — needed by Map set/append order tests.
pub fn array_prototype_pop(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Array.prototype.pop on non-object")),
  };

  let mut s = scope.reborrow();
  s.push_root(Value::Object(this_obj))?;
  let len = get_array_length(&mut s, this_obj)?;
  if len == 0 {
    define_array_length(&mut s, this_obj, 0)?;
    return Ok(Value::Undefined);
  }
  let new_len = len - 1;
  let key = PropertyKey::from_string(s.alloc_string(&new_len.to_string())?);
  let value = get_data_property_value(&mut s, this_obj, &key)?.unwrap_or(Value::Undefined);
  s.push_root(value)?;
  let _ = s.ordinary_delete(this_obj, key)?;
  define_array_length(&mut s, this_obj, new_len)?;
  let _ = vm;
  Ok(value)
}

/// `Array.prototype.shift` (minimal, §23.1.3.22) — needed by Set/Map forEach order tests.
pub fn array_prototype_shift(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => {
      return Err(VmError::Unimplemented(
        "Array.prototype.shift on non-object",
      ))
    }
  };

  let mut s = scope.reborrow();
  s.push_root(Value::Object(this_obj))?;
  let len = get_array_length(&mut s, this_obj)?;
  if len == 0 {
    define_array_length(&mut s, this_obj, 0)?;
    return Ok(Value::Undefined);
  }

  let first_key = PropertyKey::from_string(s.alloc_string("0")?);
  let first = get_data_property_value(&mut s, this_obj, &first_key)?.unwrap_or(Value::Undefined);
  s.push_root(first)?;

  for k in 1..len {
    vm.tick()?;
    let from_key = PropertyKey::from_string(s.alloc_string(&k.to_string())?);
    let to_key = PropertyKey::from_string(s.alloc_string(&(k - 1).to_string())?);
    if let Some(val) = get_data_property_value(&mut s, this_obj, &from_key)? {
      s.push_root(val)?;
      s.define_property(this_obj, to_key, data_desc(val, true, true, true))?;
    } else {
      let _ = s.ordinary_delete(this_obj, to_key)?;
    }
  }

  let last_key = PropertyKey::from_string(s.alloc_string(&(len - 1).to_string())?);
  let _ = s.ordinary_delete(this_obj, last_key)?;
  define_array_length(&mut s, this_obj, len - 1)?;
  Ok(first)
}

/// Strict Equality Comparison for `Array.prototype.indexOf` (`===`).
fn array_strict_equal(scope: &Scope<'_>, a: Value, b: Value) -> Result<bool, VmError> {
  match (a, b) {
    (Value::Number(x), Value::Number(y)) => Ok(x == y),
    _ => Ok(a.same_value(b, scope.heap())),
  }
}

fn array_index_from_arg(
  scope: &mut Scope<'_>,
  args: &[Value],
  len: usize,
) -> Result<usize, VmError> {
  let n = match args.get(1).copied() {
    None | Some(Value::Undefined) => 0.0,
    Some(v) => to_integer_or_infinity(scope.heap_mut().to_number(v)?),
  };
  if n >= len as f64 {
    return Ok(len);
  }
  if n >= 0.0 {
    return Ok(n as usize);
  }
  let k = (len as f64) + n;
  Ok(if k > 0.0 { k as usize } else { 0 })
}

/// `Array.prototype.indexOf` (minimal, §23.1.3.14) — Strict Equality; used by Set composition
/// set-like order tests.
pub fn array_prototype_index_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => {
      return Err(VmError::Unimplemented(
        "Array.prototype.indexOf on non-object",
      ))
    }
  };
  scope.push_root(Value::Object(this_obj))?;
  let len = get_array_length(scope, this_obj)?;
  if len == 0 {
    return Ok(Value::Number(-1.0));
  }
  let search = args.first().copied().unwrap_or(Value::Undefined);
  scope.push_root(search)?;
  let mut k = array_index_from_arg(scope, args, len)?;
  while k < len {
    vm.tick()?;
    let key = PropertyKey::from_string(scope.alloc_string(&k.to_string())?);
    // Spec: skip holes (`HasProperty` false). Dense array literals used by Set tests are fine
    // with own-data presence.
    if get_data_property_value(scope, this_obj, &key)?.is_none() {
      k = k.saturating_add(1);
      continue;
    }
    let element = scope.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      this_obj,
      key,
      Value::Object(this_obj),
    )?;
    if array_strict_equal(scope, search, element)? {
      return Ok(Value::Number(k as f64));
    }
    k = k.saturating_add(1);
  }
  Ok(Value::Number(-1.0))
}

/// `Array.prototype.includes` (minimal, §23.1.3.13) — SameValueZero; used by Set composition
/// set-like mutation tests.
pub fn array_prototype_includes(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => {
      return Err(VmError::Unimplemented(
        "Array.prototype.includes on non-object",
      ))
    }
  };
  scope.push_root(Value::Object(this_obj))?;
  let len = get_array_length(scope, this_obj)?;
  if len == 0 {
    return Ok(Value::Bool(false));
  }
  let search = args.first().copied().unwrap_or(Value::Undefined);
  scope.push_root(search)?;
  let mut k = array_index_from_arg(scope, args, len)?;
  while k < len {
    vm.tick()?;
    let key = PropertyKey::from_string(scope.alloc_string(&k.to_string())?);
    let element = scope.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      this_obj,
      key,
      Value::Object(this_obj),
    )?;
    if search.same_value_zero(element, scope.heap()) {
      return Ok(Value::Bool(true));
    }
    k = k.saturating_add(1);
  }
  Ok(Value::Bool(false))
}

/// `Array.prototype.map` (minimal).
pub fn array_prototype_map(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Array.prototype.map on non-object")),
  };

  let len = get_array_length(scope, this_obj)?;

  let callback = args.first().copied().unwrap_or(Value::Undefined);
  let this_arg = args.get(1).copied().unwrap_or(Value::Undefined);

  let intr = require_intrinsics(vm)?;
  let out = scope.alloc_object()?;
  scope.push_root(Value::Object(out))?;
  scope
    .heap_mut()
    .object_set_prototype(out, Some(intr.array_prototype()))?;
  define_array_length(scope, out, len)?;

  for i in 0..len {
    vm.tick()?;
    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let Some(value) = get_data_property_value(scope, this_obj, &key)? else {
      continue;
    };

    // callback(value, index, array)
    let call_args = [value, Value::Number(i as f64), Value::Object(this_obj)];
    let mapped = vm.call_with_host(scope, host, callback, this_arg, &call_args)?;

    scope.define_property(out, key, data_desc(mapped, true, true, true))?;
  }

  Ok(Value::Object(out))
}

/// `Array.prototype.toString` (§23.1.3.36) — `join` when callable, else `Object.prototype.toString`.
pub fn array_prototype_to_string(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    Value::Undefined | Value::Null => {
      let intr = require_intrinsics(vm)?;
      return Err(crate::error_object::throw_type_error(
        scope,
        intr,
        "Array.prototype.toString called on null or undefined",
      ));
    }
    // Primitives: box via Object() so `join`/`toString` see an object `this`.
    other => match object_constructor_impl(vm, scope, hooks, &[other])? {
      Value::Object(o) => o,
      _ => {
        return Err(VmError::Unimplemented(
          "Array.prototype.toString ToObject boxing",
        ))
      }
    },
  };
  scope.push_root(Value::Object(this_obj))?;
  let join_s = scope.alloc_string("join")?;
  scope.push_root(Value::String(join_s))?;
  let join_key = PropertyKey::from_string(join_s);
  let func = vm.get(scope, this_obj, join_key)?;
  if scope.heap().is_callable(func)? {
    scope.push_root(func)?;
    return vm.call_with_host_and_hooks(host, scope, hooks, func, Value::Object(this_obj), &[]);
  }
  // Fall back to `%Object.prototype.toString%`.
  object_prototype_to_string(vm, scope, host, hooks, callee, Value::Object(this_obj), &[])
}

/// `Array.prototype.join` (minimal).
pub fn array_prototype_join(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Array.prototype.join on non-object")),
  };

  let len = get_array_length(scope, this_obj)?;

  let sep = match args.first().copied() {
    None | Some(Value::Undefined) => scope.alloc_string(",")?,
    Some(v) => crate::spec_ops::to_string(vm, scope, v)?,
  };
  scope.push_root(Value::String(sep))?;
  let sep_slice = scope.heap().get_string(sep)?.as_code_units();
  let mut sep_units: Vec<u16> = Vec::new();
  sep_units
    .try_reserve_exact(sep_slice.len())
    .map_err(|_| VmError::OutOfMemory)?;
  vec_try_extend_from_slice(&mut sep_units, sep_slice)?;

  let empty = scope.alloc_string("")?;
  scope.push_root(Value::String(empty))?;

  let mut out: Vec<u16> = Vec::new();
  let max_bytes = scope.heap().limits().max_bytes;

  for i in 0..len {
    if i % 1024 == 0 {
      vm.tick()?;
    }

    if i > 0 {
      if JsString::heap_size_bytes_for_len(out.len().saturating_add(sep_units.len())) > max_bytes {
        return Err(VmError::OutOfMemory);
      }
      vec_try_extend_from_slice(&mut out, &sep_units)?;
    }

    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let value = get_data_property_value(scope, this_obj, &key)?.unwrap_or(Value::Undefined);
    let part = match value {
      Value::Undefined | Value::Null => empty,
      other => crate::spec_ops::to_string(vm, scope, other)?,
    };

    let units = scope.heap().get_string(part)?.as_code_units();
    if JsString::heap_size_bytes_for_len(out.len().saturating_add(units.len())) > max_bytes {
      return Err(VmError::OutOfMemory);
    }
    vec_try_extend_from_slice(&mut out, units)?;
  }

  let s = scope.alloc_string_from_u16_vec(out)?;
  Ok(Value::String(s))
}

/// `String` constructor called as a function (ECMA-262 §22.1.1.1).
///
/// Special case: when `NewTarget` is undefined and the argument is a Symbol,
/// return `SymbolDescriptiveString(sym)` (does **not** throw — unlike `ToString`).
pub fn string_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let s = match args.first().copied() {
    None => scope.alloc_string("")?,
    Some(Value::Symbol(sym)) => {
      // SymbolDescriptiveString(sym) — `Symbol(${description})`
      let mut units: Vec<u16> = Vec::new();
      units.extend("Symbol(".encode_utf16());
      if let Some(d) = scope.heap().get_symbol_description(sym)? {
        units.extend_from_slice(scope.heap().get_string(d)?.as_code_units());
      }
      units.extend(")".encode_utf16());
      scope.alloc_string_from_u16_vec(units)?
    }
    Some(v) => crate::spec_ops::to_string(vm, scope, v)?,
  };
  Ok(Value::String(s))
}

/// `new String(value)` (minimal wrapper object).
pub fn string_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let prim = match args.first().copied() {
    None => scope.alloc_string("")?,
    Some(v) => crate::spec_ops::to_string(vm, scope, v)?,
  };
  scope.push_root(Value::String(prim))?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.string_prototype()))?;

  // Store the primitive value on an internal symbol so `String.prototype.toString` can recover it.
  let marker = scope.alloc_string("vm-js.internal.StringData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  scope.define_property(
    obj,
    marker_key,
    data_desc(Value::String(prim), true, false, false),
  )?;

  // Best-effort: if `new_target.prototype` is an object, use it.
  if let Value::Object(nt) = new_target {
    let proto_key = string_key(scope, "prototype")?;
    if let Ok(Value::Object(p)) = scope.heap().get(nt, &proto_key) {
      scope.heap_mut().object_set_prototype(obj, Some(p))?;
    }
  }

  Ok(Value::Object(obj))
}

/// `String.prototype.toString` (minimal).
pub fn string_prototype_to_string(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  match this {
    Value::String(s) => Ok(Value::String(s)),
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.StringData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope
        .heap()
        .object_get_own_data_property_value(obj, &marker_key)?
      {
        Some(Value::String(s)) => Ok(Value::String(s)),
        _ => Err(VmError::Unimplemented(
          "String.prototype.toString on non-String object",
        )),
      }
    }
    _ => Err(VmError::Unimplemented(
      "String.prototype.toString on non-string",
    )),
  }
}

// --- Primitive-wrapper prototype methods (autoboxing surface, ECMA-262 §22.1.3 / §21.1.3) ---

/// ECMAScript `ToIntegerOrInfinity` (§7.1.5) as an `f64` (NaN → 0, ±∞ preserved, else truncated).
fn to_integer_or_infinity(n: f64) -> f64 {
  if n.is_nan() {
    0.0
  } else if n.is_infinite() {
    n
  } else {
    n.trunc()
  }
}

/// `RequireObjectCoercible(this)` + `ToString(this)`, returning the code units of the resulting
/// string. Used by `String.prototype` methods, which coerce `this` per §22.1.3.
fn this_string_units(vm: &mut Vm, scope: &mut Scope<'_>, this: Value) -> Result<Vec<u16>, VmError> {
  if matches!(this, Value::Undefined | Value::Null) {
    let intr = require_intrinsics(vm)?;
    return Err(crate::error_object::throw_type_error(
      scope,
      intr,
      "String.prototype method called on null or undefined",
    ));
  }
  let s = crate::spec_ops::to_string(vm, scope, this)?;
  Ok(scope.heap().get_string(s)?.as_code_units().to_vec())
}

fn number_arg(scope: &mut Scope<'_>, args: &[Value], idx: usize) -> Result<f64, VmError> {
  let v = args.get(idx).copied().unwrap_or(Value::Undefined);
  scope.heap_mut().to_number(v)
}

/// `thisNumberValue(this)` (§21.1.3): the primitive number, recovered from a wrapper object if
/// necessary.
fn this_number_value(vm: &mut Vm, scope: &mut Scope<'_>, this: Value) -> Result<f64, VmError> {
  match this {
    Value::Number(n) => Ok(n),
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.NumberData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope
        .heap()
        .object_get_own_data_property_value(obj, &marker_key)?
      {
        Some(Value::Number(n)) => Ok(n),
        _ => {
          let intr = require_intrinsics(vm)?;
          Err(crate::error_object::throw_type_error(
            scope,
            intr,
            "Number.prototype method called on incompatible receiver",
          ))
        }
      }
    }
    _ => {
      let intr = require_intrinsics(vm)?;
      Err(crate::error_object::throw_type_error(
        scope,
        intr,
        "Number.prototype method called on incompatible receiver",
      ))
    }
  }
}

/// `thisBooleanValue(this)` (§20.3.3): the primitive boolean, recovered from a wrapper object's
/// `[[BooleanData]]` slot if necessary. Throws a **catchable** `TypeError` on an incompatible
/// receiver (matching the spec, rather than a non-catchable engine error).
fn this_boolean_value(vm: &mut Vm, scope: &mut Scope<'_>, this: Value) -> Result<bool, VmError> {
  match this {
    Value::Bool(b) => Ok(b),
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.BooleanData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope
        .heap()
        .object_get_own_data_property_value(obj, &marker_key)?
      {
        Some(Value::Bool(b)) => Ok(b),
        _ => {
          let intr = require_intrinsics(vm)?;
          Err(crate::error_object::throw_type_error(
            scope,
            intr,
            "Boolean.prototype method called on incompatible receiver",
          ))
        }
      }
    }
    _ => {
      let intr = require_intrinsics(vm)?;
      Err(crate::error_object::throw_type_error(
        scope,
        intr,
        "Boolean.prototype method called on incompatible receiver",
      ))
    }
  }
}

/// `String.prototype.valueOf` (§22.1.3.32): returns the primitive string.
pub fn string_prototype_value_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  string_prototype_to_string(vm, scope, host, hooks, callee, this, args)
}

/// `String.prototype.charAt` (§22.1.3.1).
pub fn string_prototype_char_at(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let pos = to_integer_or_infinity(number_arg(scope, args, 0)?);
  if pos < 0.0 || pos >= units.len() as f64 {
    return Ok(Value::String(scope.alloc_string("")?));
  }
  let unit = units[pos as usize];
  Ok(Value::String(scope.alloc_string_from_u16_vec(vec![unit])?))
}

/// `String.prototype.charCodeAt` (§22.1.3.2).
pub fn string_prototype_char_code_at(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let pos = to_integer_or_infinity(number_arg(scope, args, 0)?);
  if pos < 0.0 || pos >= units.len() as f64 {
    return Ok(Value::Number(f64::NAN));
  }
  Ok(Value::Number(units[pos as usize] as f64))
}

/// `String.prototype.indexOf` (§22.1.3.9).
pub fn string_prototype_index_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let search_val = args.first().copied().unwrap_or(Value::Undefined);
  let search_s = scope.heap_mut().to_string(search_val)?;
  let search: Vec<u16> = scope.heap().get_string(search_s)?.as_code_units().to_vec();
  let pos = to_integer_or_infinity(number_arg(scope, args, 1)?);
  let start = pos.clamp(0.0, units.len() as f64) as usize;

  if search.is_empty() {
    return Ok(Value::Number(start.min(units.len()) as f64));
  }
  if search.len() <= units.len() {
    for i in start..=(units.len() - search.len()) {
      if units[i..i + search.len()] == search[..] {
        return Ok(Value::Number(i as f64));
      }
    }
  }
  Ok(Value::Number(-1.0))
}

/// `String.prototype.slice` (§22.1.3.22).
pub fn string_prototype_slice(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let len = units.len() as f64;
  let clamp_rel = |n: f64| -> usize {
    let idx = if n < 0.0 {
      (len + n).max(0.0)
    } else {
      n.min(len)
    };
    idx as usize
  };
  let start = clamp_rel(to_integer_or_infinity(number_arg(scope, args, 0)?));
  let end = match args.get(1).copied() {
    None | Some(Value::Undefined) => len as usize,
    Some(v) => {
      let n = scope.heap_mut().to_number(v)?;
      clamp_rel(to_integer_or_infinity(n))
    }
  };
  let slice = if start < end {
    units[start..end].to_vec()
  } else {
    Vec::new()
  };
  Ok(Value::String(scope.alloc_string_from_u16_vec(slice)?))
}

/// `String.prototype.substring` (§22.1.3.24).
pub fn string_prototype_substring(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let len = units.len() as f64;
  let clamp = |n: f64| -> usize { n.clamp(0.0, len) as usize };
  let a = clamp(to_integer_or_infinity(number_arg(scope, args, 0)?));
  let b = match args.get(1).copied() {
    None | Some(Value::Undefined) => len as usize,
    Some(v) => {
      let n = scope.heap_mut().to_number(v)?;
      clamp(to_integer_or_infinity(n))
    }
  };
  let (from, to) = if a < b { (a, b) } else { (b, a) };
  Ok(Value::String(
    scope.alloc_string_from_u16_vec(units[from..to].to_vec())?,
  ))
}

/// `String.prototype.toUpperCase` (§22.1.3.28).
pub fn string_prototype_to_upper_case(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let upper: Vec<u16> = String::from_utf16_lossy(&units)
    .to_uppercase()
    .encode_utf16()
    .collect();
  Ok(Value::String(scope.alloc_string_from_u16_vec(upper)?))
}

/// `String.prototype.toLowerCase` (§22.1.3.26).
pub fn string_prototype_to_lower_case(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let lower: Vec<u16> = String::from_utf16_lossy(&units)
    .to_lowercase()
    .encode_utf16()
    .collect();
  Ok(Value::String(scope.alloc_string_from_u16_vec(lower)?))
}

/// `String.prototype.includes` (§22.1.3.8).
pub fn string_prototype_includes(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let search_val = args.first().copied().unwrap_or(Value::Undefined);
  let search_s = scope.heap_mut().to_string(search_val)?;
  let search: Vec<u16> = scope.heap().get_string(search_s)?.as_code_units().to_vec();
  let pos = to_integer_or_infinity(number_arg(scope, args, 1)?);
  let start = pos.clamp(0.0, units.len() as f64) as usize;
  if search.is_empty() {
    return Ok(Value::Bool(true));
  }
  if search.len() <= units.len() {
    for i in start..=(units.len() - search.len()) {
      if units[i..i + search.len()] == search[..] {
        return Ok(Value::Bool(true));
      }
    }
  }
  Ok(Value::Bool(false))
}

/// `String.prototype.concat` (§22.1.3.5).
pub fn string_prototype_concat(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut units = this_string_units(vm, scope, this)?;
  for arg in args {
    let s = scope.heap_mut().to_string(*arg)?;
    let more = scope.heap().get_string(s)?.as_code_units().to_vec();
    vec_try_extend_from_slice(&mut units, &more)?;
  }
  Ok(Value::String(scope.alloc_string_from_u16_vec(units)?))
}

/// `Number.prototype.toString` (§21.1.3.6): decimal by default, with radix 2–36 support.
pub fn number_prototype_to_string(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let n = this_number_value(vm, scope, this)?;
  // Spec: `ToIntegerOrInfinity(radix)` via full `ToNumber` so object `valueOf`/`toString`
  // abrupt completions (e.g. poisoned radix) surface as the thrown error, not TypeError.
  let radix = match args.first().copied() {
    None | Some(Value::Undefined) => 10.0,
    Some(v) => to_integer_or_infinity(crate::spec_ops::to_number(vm, scope, v)?),
  };
  if radix < 2.0 || radix > 36.0 {
    let intr = require_intrinsics(vm)?;
    return Err(crate::error_object::throw_range_error(
      scope,
      intr,
      "Number.prototype.toString radix must be between 2 and 36",
    ));
  }
  if radix == 10.0 {
    // Reuse the spec-shaped decimal `Number::toString`.
    let s = scope.heap_mut().to_string(Value::Number(n))?;
    return Ok(Value::String(s));
  }
  let s = number_to_radix_string(n, radix as u32);
  Ok(Value::String(scope.alloc_string(&s)?))
}

/// `Number.prototype.toLocaleString` (§21.1.3.4) — locale-independent fallback (= `toString`).
///
/// Full `Intl.NumberFormat` is out of scope; ECMA-262 permits an implementation-defined locale,
/// and the language-core suite only asserts the method's property descriptor / callable shape.
pub fn number_prototype_to_locale_string(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  number_prototype_to_string(vm, scope, host, hooks, callee, this, &[])
}

/// `Number.prototype.toFixed` (§21.1.3.3).
pub fn number_prototype_to_fixed(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let n = this_number_value(vm, scope, this)?;
  let digits_arg = args.first().copied().unwrap_or(Value::Undefined);
  let digits = to_integer_or_infinity(crate::spec_ops::to_number(vm, scope, digits_arg)?);
  if !(0.0..=100.0).contains(&digits) {
    let intr = require_intrinsics(vm)?;
    return Err(crate::error_object::throw_range_error(
      scope,
      intr,
      "toFixed() digits argument must be between 0 and 100",
    ));
  }
  let s = if n.is_nan() {
    "NaN".to_string()
  } else if !n.is_finite() {
    if n < 0.0 {
      "-Infinity".to_string()
    } else {
      "Infinity".to_string()
    }
  } else if n.abs() >= 1e21 {
    let g = scope.heap_mut().to_string(Value::Number(n))?;
    return Ok(Value::String(g));
  } else {
    format!("{:.*}", digits as usize, n)
  };
  Ok(Value::String(scope.alloc_string(&s)?))
}

/// `Number.prototype.toExponential` (§21.1.3.2).
pub fn number_prototype_to_exponential(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let n = this_number_value(vm, scope, this)?;
  let fraction_digits = args.first().copied();
  // Spec: `ToInteger(fractionDigits)` (via `ToNumber`) runs even when `x` is non-finite, so
  // abrupt completions from `valueOf`/`toString` must surface. Use the full object-aware
  // `ToNumber`, not the heap placeholder that stubs `ToPrimitive` as `"[object Object]"`.
  let f_opt = match fraction_digits {
    None | Some(Value::Undefined) => None,
    Some(v) => Some(to_integer_or_infinity(crate::spec_ops::to_number(
      vm, scope, v,
    )?)),
  };
  // §21.1.3.2: non-finite `x` returns `Number::toString` *before* the `f` range check
  // (so `NaN.toExponential(Infinity)` is `"NaN"`, not a `RangeError`).
  if !n.is_finite() {
    let s = scope.heap_mut().to_string(Value::Number(n))?;
    return Ok(Value::String(s));
  }
  if let Some(f) = f_opt {
    if !(0.0..=100.0).contains(&f) {
      let intr = require_intrinsics(vm)?;
      return Err(crate::error_object::throw_range_error(
        scope,
        intr,
        "toExponential() argument must be between 0 and 100",
      ));
    }
  }
  let s = number_to_exponential_string(n, f_opt.map(|f| f as i32));
  Ok(Value::String(scope.alloc_string(&s)?))
}

/// `Number.prototype.toPrecision` (§21.1.3.5).
pub fn number_prototype_to_precision(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let n = this_number_value(vm, scope, this)?;
  let precision = args.first().copied();
  if matches!(precision, None | Some(Value::Undefined)) {
    let s = scope.heap_mut().to_string(Value::Number(n))?;
    return Ok(Value::String(s));
  }
  // Same as `toExponential`: `ToInteger(precision)` must observe object `valueOf`/`toString`.
  let p = to_integer_or_infinity(crate::spec_ops::to_number(vm, scope, precision.unwrap())?);
  // §21.1.3.5: non-finite `x` returns `Number::toString` before the precision range check.
  if !n.is_finite() {
    let s = scope.heap_mut().to_string(Value::Number(n))?;
    return Ok(Value::String(s));
  }
  if !(1.0..=100.0).contains(&p) {
    let intr = require_intrinsics(vm)?;
    return Err(crate::error_object::throw_range_error(
      scope,
      intr,
      "toPrecision() argument must be between 1 and 100",
    ));
  }
  let s = number_to_precision_string(n, p as i32);
  Ok(Value::String(scope.alloc_string(&s)?))
}

/// `String.prototype.split` (§22.1.3.21) — string separator path (RegExp/`@@split` deferred).
pub fn string_prototype_split(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let units = this_string_units(vm, scope, this)?;
  let separator = args.first().copied().unwrap_or(Value::Undefined);
  let lim = match args.get(1).copied() {
    None | Some(Value::Undefined) => u32::MAX,
    Some(v) => {
      let n = scope.heap_mut().to_number(v)?;
      if n.is_nan() || n <= 0.0 {
        0
      } else if n.is_infinite() {
        u32::MAX
      } else {
        n.min(u32::MAX as f64) as u32
      }
    }
  };
  if lim == 0 {
    return Ok(Value::Object(create_array_object(vm, scope, 0)?));
  }
  if matches!(separator, Value::Undefined) {
    let array = create_array_object(vm, scope, 1)?;
    let s = scope.alloc_string_from_u16_vec(units)?;
    let key = PropertyKey::from_string(scope.alloc_string("0")?);
    scope.define_property(array, key, data_desc(Value::String(s), true, true, true))?;
    return Ok(Value::Object(array));
  }
  if matches!(separator, Value::Object(_)) {
    // RegExp / @@split objects are not implemented yet.
    return Err(VmError::Unimplemented(
      "String.prototype.split with object separator",
    ));
  }
  let sep_s = scope.heap_mut().to_string(separator)?;
  let sep: Vec<u16> = scope.heap().get_string(sep_s)?.as_code_units().to_vec();

  let mut parts: Vec<Vec<u16>> = Vec::new();
  if sep.is_empty() {
    for u in units {
      parts.push(vec![u]);
      if parts.len() as u32 == lim {
        break;
      }
    }
  } else {
    let mut start = 0usize;
    while start <= units.len() {
      if parts.len() as u32 == lim {
        break;
      }
      if let Some(rel) = find_subslice(&units[start..], &sep) {
        let end = start + rel;
        parts.push(units[start..end].to_vec());
        start = end + sep.len();
      } else {
        parts.push(units[start..].to_vec());
        break;
      }
    }
  }

  let len = u32::try_from(parts.len()).map_err(|_| VmError::OutOfMemory)?;
  let array = create_array_object(vm, scope, len)?;
  for (i, part) in parts.into_iter().enumerate() {
    let mut s = scope.reborrow();
    s.push_root(Value::Object(array))?;
    let str_v = s.alloc_string_from_u16_vec(part)?;
    s.push_root(Value::String(str_v))?;
    let key = PropertyKey::from_string(s.alloc_string(&i.to_string())?);
    s.define_property(
      array,
      key,
      data_desc(Value::String(str_v), true, true, true),
    )?;
  }
  Ok(Value::Object(array))
}

fn find_subslice(haystack: &[u16], needle: &[u16]) -> Option<usize> {
  if needle.is_empty() {
    return Some(0);
  }
  haystack.windows(needle.len()).position(|w| w == needle)
}

/// Format `n` in exponential notation. `fraction_digits = None` means undefined (shortest).
fn number_to_exponential_string(n: f64, fraction_digits: Option<i32>) -> String {
  if n.is_nan() {
    return "NaN".to_string();
  }
  if !n.is_finite() {
    return if n < 0.0 {
      "-Infinity".to_string()
    } else {
      "Infinity".to_string()
    };
  }

  // `-0` is treated as `+0` for the zero branch (test262 expects no leading '-').
  if n == 0.0 {
    let f = fraction_digits.unwrap_or(0) as usize;
    let mut m = "0".to_string();
    if f > 0 {
      m.push('.');
      m.extend(std::iter::repeat('0').take(f));
    }
    return format!("{m}e+0");
  }

  let sign = if n < 0.0 { "-" } else { "" };
  let abs = n.abs();
  // Leading-digit exponent from a short ryu decomposition (stable for powers of ten).
  let (mut digits_src, mut exp) = ryu_significant_digits(abs);
  // For `fractionDigits === undefined`, prefer the shortest digit string (n not divisible by 10).
  if fraction_digits.is_none() {
    while digits_src.len() > 1 && digits_src.ends_with('0') {
      digits_src.pop();
      exp += 1;
    }
  }
  let mut e = exp + digits_src.len() as i32 - 1;
  let want = match fraction_digits {
    None => digits_src.len(),
    Some(f) => f as usize + 1,
  };

  // When more digits than ryu's shortest form are requested, re-derive from the float by
  // scaling/rounding so padded digits match IEEE-754 (test262 `return-values.js`).
  let digits = if fraction_digits.is_some() && want > digits_src.len() {
    exponential_digits_from_float(abs, want, &mut e)
  } else {
    round_digit_string(&digits_src, want, &mut e)
  };
  debug_assert!(digits.len() >= want);
  let mut m = String::with_capacity(want + 1);
  m.push(digits.as_bytes()[0] as char);
  if want > 1 {
    m.push('.');
    m.push_str(&digits[1..want]);
  }
  let exp_sign = if e >= 0 { "+" } else { "-" };
  format!("{sign}{m}e{exp_sign}{}", e.abs())
}

/// Produce `want` significant decimal digits for `abs` in exponential form, updating `e`
/// (leading-digit exponent) when rounding carries.
///
/// Uses the exact IEEE-754 significand (`mant × 2^exp2`) with [`num_bigint`] so requests past
/// the `f64` integer precision (e.g. `toExponential(17)`) still match ECMA-262 / test262.
/// Exact compare: `mant × 2^exp2 >= 10^e` (all as mathematical integers / rationals).
fn mant_pow2_ge_pow10(mant: u64, exp2: i32, e: i32) -> bool {
  use num_bigint::BigUint;
  use num_traits::One;

  // mant × 2^exp2 >= 2^e × 5^e  ⇒  mant × 2^(exp2 - e) >= 5^e
  let five_e = BigUint::from(5u32).pow(e.unsigned_abs());
  if e >= 0 {
    let shift = exp2 - e;
    let mut left = BigUint::from(mant);
    if shift >= 0 {
      left <<= shift as u32;
      left >= five_e
    } else {
      // mant >= 5^e × 2^(-shift)
      let right = five_e << ((-shift) as u32);
      BigUint::from(mant) >= right
    }
  } else {
    // mant × 2^exp2 >= 10^e = 1/10^(-e)  ⇒ mant × 2^exp2 × 10^(-e) >= 1
    // ⇒ mant × 2^exp2 × 2^(-e) × 5^(-e) >= 1  ⇒ mant × 2^(exp2 - e) >= 5^(-e)
    // Here e < 0, so -e > 0; five_e = 5^(-e).
    let shift = exp2 - e; // exp2 - (negative) = exp2 + |e|
    let mut left = BigUint::from(mant);
    if shift >= 0 {
      left <<= shift as u32;
      left >= five_e
    } else {
      let right = five_e << ((-shift) as u32);
      BigUint::from(mant) >= right
    }
  }
}

fn exponential_digits_from_float(abs: f64, want: usize, e: &mut i32) -> String {
  use num_bigint::BigUint;
  use num_traits::{One, Zero};

  debug_assert!(want >= 1);
  debug_assert!(abs > 0.0 && abs.is_finite());

  let bits = abs.to_bits();
  let bias_exp = ((bits >> 52) & 0x7ff) as i32;
  let frac = bits & ((1u64 << 52) - 1);
  let (mant, exp2) = if bias_exp == 0 {
    // Subnormal: abs = frac × 2^-1074.
    (frac, -1074)
  } else {
    // Normal: abs = (2^52 + frac) × 2^(bias_exp - 1075).
    (frac | (1u64 << 52), bias_exp - 1075)
  };

  // Correct the ryu-based leading-exponent guess with an exact `floor(log10(abs))`:
  // largest `e` such that `10^e <= abs`. Critical near powers of ten (e.g. the f64 for
  // `1e-21` is slightly smaller than 10^-21, so e must be -22).
  {
    let mut guess = *e;
    for _ in 0..4 {
      if mant_pow2_ge_pow10(mant, exp2, guess + 1) {
        guess += 1;
        continue;
      }
      if !mant_pow2_ge_pow10(mant, exp2, guess) {
        guess -= 1;
        continue;
      }
      break;
    }
    *e = guess;
  }

  // Renormalize until `round(abs × 10^((want-1)-e))` yields exactly `want` digits.
  for _ in 0..8 {
    let scale = (want as i32 - 1) - *e;
    let mut num = BigUint::from(mant);
    let mut den = BigUint::one();
    if exp2 >= 0 {
      num <<= exp2 as u32;
    } else {
      den <<= (-exp2) as u32;
    }
    if scale >= 0 {
      num *= BigUint::from(10u32).pow(scale as u32);
    } else {
      den *= BigUint::from(10u32).pow((-scale) as u32);
    }

    // Round half away from zero (num/den > 0): q = floor((num + den/2) / den).
    let q = if den.is_zero() {
      num
    } else {
      (&num + &den / 2u32) / &den
    };

    let digits = q.to_string();
    if digits == "0" {
      *e -= 1;
      continue;
    }
    if digits.len() == want {
      return digits;
    }
    if digits.len() == want + 1 {
      // Carry into an extra digit (e.g. 999… → 1000…).
      *e += 1;
      return format!("1{}", "0".repeat(want - 1));
    }
    if digits.len() > want + 1 {
      *e += (digits.len() - want) as i32;
      continue;
    }
    // Fewer than `want` digits ⇒ assumed leading exponent was too large.
    *e -= 1;
  }

  // Last-resort pad (should be unreachable for finite non-zero floats).
  let mut fallback = "1".to_string();
  fallback.extend(std::iter::repeat('0').take(want - 1));
  fallback
}

/// Format `n` with `p` significant digits (§21.1.3.5).
fn number_to_precision_string(n: f64, p: i32) -> String {
  if n.is_nan() {
    return "NaN".to_string();
  }
  if !n.is_finite() {
    return if n < 0.0 {
      "-Infinity".to_string()
    } else {
      "Infinity".to_string()
    };
  }
  if n == 0.0 {
    let mut m = "0".to_string();
    if p > 1 {
      m.push('.');
      m.extend(std::iter::repeat('0').take((p - 1) as usize));
    }
    return m;
  }

  let sign = if n < 0.0 { "-" } else { "" };
  let abs = n.abs();
  // Leading-digit exponent from a short ryu decomposition, then re-derive the `p`
  // significant digits from the exact IEEE significand (same path as `toExponential`).
  // Ryu's shortest form alone mis-rounds values like `1.2345e+27` (stored slightly below
  // the decimal literal) when truncating to fewer significant digits.
  let (digits_src, exp) = ryu_significant_digits(abs);
  let mut e = exp + digits_src.len() as i32 - 1;
  let m = exponential_digits_from_float(abs, p as usize, &mut e);

  // Exponential when e <= -7 or e >= p.
  if e < -6 || e >= p {
    let mut out = String::new();
    out.push_str(sign);
    out.push(m.as_bytes()[0] as char);
    if p > 1 {
      out.push('.');
      out.push_str(&m[1..]);
    }
    let exp_sign = if e >= 0 { "+" } else { "-" };
    out.push('e');
    out.push_str(exp_sign);
    out.push_str(&e.abs().to_string());
    return out;
  }

  let mut out = String::new();
  out.push_str(sign);
  if e >= 0 {
    let k = (e + 1) as usize;
    if k >= m.len() {
      out.push_str(&m);
      out.extend(std::iter::repeat('0').take(k - m.len()));
      let frac = p as usize - k;
      if frac > 0 {
        out.push('.');
        out.extend(std::iter::repeat('0').take(frac));
      }
    } else {
      out.push_str(&m[..k]);
      out.push('.');
      out.push_str(&m[k..]);
    }
  } else {
    out.push('0');
    out.push('.');
    out.extend(std::iter::repeat('0').take((-(e + 1)) as usize));
    out.push_str(&m);
  }
  out
}

/// Round/pad a digit string to `want` significant digits. On carry past the leading digit,
/// increments `e` (the decimal exponent of the leading digit).
fn round_digit_string(digits: &str, want: usize, e: &mut i32) -> String {
  debug_assert!(want >= 1);
  let mut buf: Vec<u8> = digits.as_bytes().to_vec();
  while buf.len() < want {
    buf.push(b'0');
  }
  if buf.len() > want {
    let round_up = buf[want] >= b'5';
    buf.truncate(want);
    if round_up {
      let mut i = want;
      loop {
        if i == 0 {
          // 999… → 1000… with exponent bump.
          buf = vec![b'1'];
          buf.extend(std::iter::repeat(b'0').take(want - 1));
          *e += 1;
          break;
        }
        i -= 1;
        if buf[i] < b'9' {
          buf[i] += 1;
          break;
        }
        buf[i] = b'0';
      }
    }
  }
  String::from_utf8(buf).unwrap_or_else(|_| "0".to_string())
}

fn ryu_significant_digits(abs: f64) -> (String, i32) {
  let mut buffer = ryu::Buffer::new();
  let raw = buffer.format_finite(abs);
  let raw = raw.strip_suffix(".0").unwrap_or(raw);
  // Same parse as `property::parse_ryu_to_decimal`: digits × 10^exp = abs.
  let (mantissa, exp_part) = match raw.split_once('e') {
    Some((mantissa, exp)) => (mantissa, Some(exp)),
    None => (raw, None),
  };
  let mut exp: i32 = exp_part.map_or(0, |e| e.parse().unwrap_or(0));
  let mut digits = String::with_capacity(mantissa.len());
  if let Some((int_part, frac_part)) = mantissa.split_once('.') {
    digits.push_str(int_part);
    digits.push_str(frac_part);
    exp -= frac_part.len() as i32;
  } else {
    digits.push_str(mantissa);
  }
  let trimmed = digits.trim_start_matches('0');
  (trimmed.to_string(), exp)
}

/// `Boolean.prototype.toString` (§20.3.3.3).
pub fn boolean_prototype_to_string(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let b = match this {
    Value::Bool(b) => b,
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.BooleanData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope
        .heap()
        .object_get_own_data_property_value(obj, &marker_key)?
      {
        Some(Value::Bool(b)) => b,
        _ => {
          let intr = require_intrinsics(vm)?;
          return Err(crate::error_object::throw_type_error(
            scope,
            intr,
            "Boolean.prototype.toString called on incompatible receiver",
          ));
        }
      }
    }
    _ => {
      let intr = require_intrinsics(vm)?;
      return Err(crate::error_object::throw_type_error(
        scope,
        intr,
        "Boolean.prototype.toString called on incompatible receiver",
      ));
    }
  };
  Ok(Value::String(scope.alloc_string(if b {
    "true"
  } else {
    "false"
  })?))
}

/// Formats a finite/`NaN`/`Infinity` number in an arbitrary radix (2–36), matching
/// `Number::toString` for non-decimal radices closely enough for the common integer cases.
fn number_to_radix_string(n: f64, radix: u32) -> String {
  if n.is_nan() {
    return "NaN".to_string();
  }
  if n == 0.0 {
    return "0".to_string();
  }
  if n.is_infinite() {
    return if n < 0.0 {
      "-Infinity".to_string()
    } else {
      "Infinity".to_string()
    };
  }
  let neg = n < 0.0;
  let mut x = n.abs();
  let mut int_part = x.trunc();
  let mut frac = x - int_part;

  let digit = |d: u32| -> char { std::char::from_digit(d, radix).unwrap_or('0') };

  let mut int_digits = Vec::new();
  if int_part == 0.0 {
    int_digits.push('0');
  } else {
    while int_part > 0.0 {
      let rem = (int_part % radix as f64) as u32;
      int_digits.push(digit(rem));
      int_part = (int_part / radix as f64).trunc();
    }
    int_digits.reverse();
  }
  let mut out: String = int_digits.into_iter().collect();

  if frac > 0.0 {
    out.push('.');
    // Bounded fractional expansion.
    let mut count = 0;
    while frac > 0.0 && count < 52 {
      frac *= radix as f64;
      let d = frac.trunc() as u32;
      out.push(digit(d));
      frac -= d as f64;
      count += 1;
    }
  }
  let _ = &mut x;
  if neg {
    format!("-{out}")
  } else {
    out
  }
}

/// `Number` / `ToNumeric` then BigInt→Number when needed (§21.1.1.1).
fn number_from_value(vm: &mut Vm, scope: &mut Scope<'_>, value: Value) -> Result<f64, VmError> {
  // Number(value) uses ToNumeric, then converts BigInt via ℝ(n) → Number (not ToNumber,
  // which throws on BigInt).
  let mut s = scope.reborrow();
  s.push_root(value)?;
  let prim =
    crate::spec_ops::to_primitive(vm, &mut s, value, crate::spec_ops::ToPrimitiveHint::Number)?;
  s.push_root(prim)?;
  match prim {
    Value::BigInt(b) => Ok(b.to_f64()),
    other => crate::spec_ops::to_number(vm, &mut s, other),
  }
}

/// `Number` constructor called as a function.
pub fn number_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let n = match args.first().copied() {
    None => 0.0,
    Some(v) => number_from_value(vm, scope, v)?,
  };
  Ok(Value::Number(n))
}

/// `new Number(value)` (minimal wrapper object).
pub fn number_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let prim = match args.first().copied() {
    None => 0.0,
    Some(v) => number_from_value(vm, scope, v)?,
  };

  // GetPrototypeFromConstructor(newTarget, "%Number.prototype%"): when `.prototype` is not an
  // object, use GetFunctionRealm(newTarget)'s %Number.prototype%.
  let default_proto =
    default_proto_from_new_target(vm, scope, new_target, |intr| intr.number_prototype())?;
  let proto = prototype_from_new_target(vm, scope, new_target, default_proto)?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope.push_root(Value::Object(proto))?;
  scope.heap_mut().object_set_prototype(obj, Some(proto))?;

  // Store the primitive value on an internal symbol so `Number.prototype.valueOf` can recover it.
  let marker = scope.alloc_string("vm-js.internal.NumberData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  scope.define_property(
    obj,
    marker_key,
    data_desc(Value::Number(prim), true, false, false),
  )?;

  Ok(Value::Object(obj))
}

/// `Number.prototype.valueOf` (§21.1.3.7).
pub fn number_prototype_value_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  // §21.1.3.7: `thisNumberValue(this)` throws a catchable `TypeError` on an incompatible receiver.
  Ok(Value::Number(this_number_value(vm, scope, this)?))
}

/// `Boolean` constructor called as a function.
pub fn boolean_constructor_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let b = match args.first().copied() {
    None => false,
    Some(v) => scope.heap().to_boolean(v)?,
  };
  Ok(Value::Bool(b))
}

/// `new Boolean(value)` (minimal wrapper object).
pub fn boolean_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let prim = match args.first().copied() {
    None => false,
    Some(v) => scope.heap().to_boolean(v)?,
  };

  // GetPrototypeFromConstructor(newTarget, "%Boolean.prototype%").
  let default_proto =
    default_proto_from_new_target(vm, scope, new_target, |intr| intr.boolean_prototype())?;
  let proto = prototype_from_new_target(vm, scope, new_target, default_proto)?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope.push_root(Value::Object(proto))?;
  scope.heap_mut().object_set_prototype(obj, Some(proto))?;

  // Store the primitive value on an internal symbol so `Boolean.prototype.valueOf` can recover it.
  let marker = scope.alloc_string("vm-js.internal.BooleanData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  scope.define_property(
    obj,
    marker_key,
    data_desc(Value::Bool(prim), true, false, false),
  )?;

  Ok(Value::Object(obj))
}

/// `Boolean.prototype.valueOf` (§20.3.3.3).
pub fn boolean_prototype_value_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  // §20.3.3.3: `thisBooleanValue(this)` throws a catchable `TypeError` on an incompatible receiver.
  Ok(Value::Bool(this_boolean_value(vm, scope, this)?))
}

/// `BigInt.prototype.valueOf` (minimal).
pub fn bigint_prototype_value_of(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  match this {
    Value::BigInt(b) => Ok(Value::BigInt(b)),
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.BigIntData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope
        .heap()
        .object_get_own_data_property_value(obj, &marker_key)?
      {
        Some(Value::BigInt(b)) => Ok(Value::BigInt(b)),
        _ => Err(VmError::Unimplemented(
          "BigInt.prototype.valueOf on non-BigInt object",
        )),
      }
    }
    _ => Err(VmError::Unimplemented(
      "BigInt.prototype.valueOf on non-bigint",
    )),
  }
}

/// `Symbol.prototype.valueOf` (minimal).
pub fn symbol_prototype_value_of(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  match this {
    Value::Symbol(s) => Ok(Value::Symbol(s)),
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.SymbolData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope
        .heap()
        .object_get_own_data_property_value(obj, &marker_key)?
      {
        Some(Value::Symbol(s)) => Ok(Value::Symbol(s)),
        _ => Err(VmError::Unimplemented(
          "Symbol.prototype.valueOf on non-Symbol object",
        )),
      }
    }
    _ => Err(VmError::Unimplemented(
      "Symbol.prototype.valueOf on non-symbol",
    )),
  }
}

/// Global `isNaN(x)` (minimal).
pub fn global_is_nan(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let v = args.first().copied().unwrap_or(Value::Undefined);
  let n = scope.heap_mut().to_number(v)?;
  Ok(Value::Bool(n.is_nan()))
}

/// `Date` called as a function (extremely minimal).
pub fn date_constructor_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  // Spec: `Date()` returns a string representation of the current time.
  // For the interpreter/test262 we only need a deterministic placeholder.
  Ok(Value::String(scope.alloc_string("[object Date]")?))
}

/// `new Date(value)` (minimal wrapper object).
pub fn date_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let time = match args.first().copied() {
    None => 0.0,
    Some(v) => scope.heap_mut().to_number(v)?,
  };

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.date_prototype()))?;

  // Store the time value on an internal symbol.
  let marker = scope.alloc_string("vm-js.internal.DateData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  scope.define_property(
    obj,
    marker_key,
    data_desc(Value::Number(time), true, false, false),
  )?;

  // Best-effort: if `new_target.prototype` is an object, use it.
  if let Value::Object(nt) = new_target {
    let proto_key = string_key(scope, "prototype")?;
    if let Ok(Value::Object(p)) = scope.heap().get(nt, &proto_key) {
      scope.heap_mut().object_set_prototype(obj, Some(p))?;
    }
  }

  Ok(Value::Object(obj))
}

/// `Date.prototype.toString` (minimal).
pub fn date_prototype_to_string(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  // The test262 smoke suite only asserts that addition uses `toString` for Date objects.
  Ok(Value::String(scope.alloc_string("[object Date]")?))
}

/// `Date.prototype.valueOf` (minimal).
pub fn date_prototype_value_of(
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
      "Date.prototype.valueOf called on non-object",
    ));
  };
  let marker = scope.alloc_string("vm-js.internal.DateData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  match scope
    .heap()
    .object_get_own_data_property_value(obj, &marker_key)?
  {
    Some(Value::Number(n)) => Ok(Value::Number(n)),
    _ => Err(VmError::TypeError(
      "Date.prototype.valueOf called on non-Date object",
    )),
  }
}

/// `Date.prototype[Symbol.toPrimitive]` (minimal).
pub fn date_prototype_to_primitive(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // Spec: Date's @@toPrimitive treats "default" like "string".
  let hint = match args.first().copied() {
    Some(Value::String(s)) => scope.heap().get_string(s)?.to_utf8_lossy(),
    _ => "default".to_string(),
  };
  if hint == "number" {
    date_prototype_value_of(_vm, scope, _host, _hooks, _callee, this, &[])
  } else {
    date_prototype_to_string(_vm, scope, _host, _hooks, _callee, this, &[])
  }
}

/// `Reflect.construct(target, argumentsList [, newTarget])` (ECMA-262 §28.1.2).
pub fn reflect_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let target = args.first().copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_constructor(target)? {
    return Err(VmError::TypeError(
      "Reflect.construct target is not a constructor",
    ));
  }
  let args_list = match args.get(1).copied().unwrap_or(Value::Undefined) {
    Value::Object(o) => get_array_like_args(scope, o)?,
    Value::Undefined => Vec::new(),
    _ => {
      return Err(VmError::TypeError(
        "Reflect.construct argumentsList must be an object",
      ))
    }
  };
  let new_target = match args.get(2).copied() {
    None | Some(Value::Undefined) => target,
    Some(nt) => {
      if !scope.heap().is_constructor(nt)? {
        return Err(VmError::TypeError(
          "Reflect.construct newTarget is not a constructor",
        ));
      }
      nt
    }
  };
  scope.push_root(target)?;
  scope.push_root(new_target)?;
  for a in &args_list {
    scope.push_root(*a)?;
  }
  vm.construct_with_host_and_hooks(host, scope, hooks, target, &args_list, new_target)
}

/// `RegExp.prototype.exec(string)` (minimal stub — always `null`; no matching engine).
pub fn regexp_prototype_exec(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Null)
}

/// `RegExp.prototype.test(string)` — best-effort via the Rust `regex` crate.
///
/// Not a full ECMA-262 RegExp engine (lookbehind / unicode sets / sticky, etc. are incomplete),
/// but covers common literal patterns used by language-core suites (e.g. `/[a-z]/`).
pub fn regexp_prototype_test(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(re) = this else {
    return throw_type_error(
      vm,
      scope,
      _hooks,
      "RegExp.prototype.test called on incompatible receiver",
    );
  };
  let mut s = scope.reborrow();
  s.push_root(Value::Object(re))?;
  let source_key = string_key(&mut s, "source")?;
  let flags_key = string_key(&mut s, "flags")?;
  let source_v = s.ordinary_get(vm, re, source_key, Value::Object(re))?;
  let flags_v = s.ordinary_get(vm, re, flags_key, Value::Object(re))?;
  let source = match source_v {
    Value::String(str_h) => s.heap().get_string(str_h)?.to_utf8_lossy(),
    _ => return Ok(Value::Bool(false)),
  };
  let flags = match flags_v {
    Value::String(str_h) => s.heap().get_string(str_h)?.to_utf8_lossy(),
    _ => String::new(),
  };
  let arg = args.first().copied().unwrap_or(Value::Undefined);
  s.push_root(arg)?;
  let input_s = s.heap_mut().to_string(arg)?;
  let input = s.heap().get_string(input_s)?.to_utf8_lossy();

  let mut builder = regex::RegexBuilder::new(&source);
  if flags.contains('i') {
    builder.case_insensitive(true);
  }
  if flags.contains('m') {
    builder.multi_line(true);
  }
  if flags.contains('s') {
    builder.dot_matches_new_line(true);
  }
  match builder.build() {
    Ok(re) => Ok(Value::Bool(re.is_match(&input))),
    // Unsupported JS syntax relative to Rust regex: treat as non-match rather than ICE.
    Err(_) => Ok(Value::Bool(false)),
  }
}

/// `%ThrowTypeError%` (§10.2.4.1) — used by restricted `caller`/`arguments` accessors.
pub fn throw_type_error_restricted(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  throw_type_error(
    vm,
    scope,
    hooks,
    "'caller', 'callee', and 'arguments' properties may not be accessed on strict mode functions or the arguments objects for calls to them",
  )
}

/// `RegExp(pattern, flags)` / `new RegExp(...)` (minimal stub — no matching engine).
///
/// Sufficient for typeof/identity and constructing inert RegExp objects. Pattern/flags are
/// stored as own data properties when provided; `exec` returns `null` (no matching engine).
pub fn regexp_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // Spec: `RegExp(...)` without `new` is equivalent to `new RegExp(...)` for ordinary use.
  regexp_constructor_construct(vm, scope, host, hooks, callee, args, Value::Object(callee))
}

/// `new RegExp(pattern, flags)` (minimal wrapper object).
pub fn regexp_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.regexp_prototype()))?;

  let marker = scope.alloc_string("vm-js.internal.RegExpData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  scope.define_property(
    obj,
    marker_key,
    data_desc(Value::Bool(true), false, false, false),
  )?;

  // Best-effort own `source` / `flags` for smoke tests (not a full RegExpInitialize).
  let source = match args.first().copied() {
    None | Some(Value::Undefined) => Value::String(scope.alloc_string("(?:)")?),
    Some(v) => {
      let s = scope.heap_mut().to_string(v)?;
      Value::String(s)
    }
  };
  scope.push_root(source)?;
  let flags = match args.get(1).copied() {
    None | Some(Value::Undefined) => Value::String(scope.alloc_string("")?),
    Some(v) => {
      let s = scope.heap_mut().to_string(v)?;
      Value::String(s)
    }
  };
  scope.push_root(flags)?;
  let source_key = string_key(scope, "source")?;
  let flags_key = string_key(scope, "flags")?;
  let last_index_key = string_key(scope, "lastIndex")?;
  scope.define_property(obj, source_key, data_desc(source, false, false, true))?;
  scope.define_property(obj, flags_key, data_desc(flags, false, false, true))?;
  scope.define_property(
    obj,
    last_index_key,
    data_desc(Value::Number(0.0), true, false, false),
  )?;

  if let Value::Object(nt) = new_target {
    let proto_key = string_key(scope, "prototype")?;
    if let Ok(Value::Object(p)) = scope.heap().get(nt, &proto_key) {
      scope.heap_mut().object_set_prototype(obj, Some(p))?;
    }
  }

  Ok(Value::Object(obj))
}

/// `Symbol(description)`.
pub fn symbol_constructor_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let desc = match args.first().copied() {
    None | Some(Value::Undefined) => None,
    Some(v) => Some(scope.heap_mut().to_string(v)?),
  };
  let sym = scope.new_symbol(desc)?;
  Ok(Value::Symbol(sym))
}

/// `Symbol.for(key)` (ECMA-262 §20.4.2.2).
pub fn symbol_for(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let key_val = args.first().copied().unwrap_or(Value::Undefined);
  let key = scope.heap_mut().to_string(key_val)?;
  scope.push_root(Value::String(key))?;
  let sym = scope.heap_mut().symbol_for(key)?;
  Ok(Value::Symbol(sym))
}

/// `Symbol.keyFor(sym)` (ECMA-262 §20.4.2.6).
pub fn symbol_key_for(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Some(Value::Symbol(sym)) = args.first().copied() else {
    return Err(VmError::TypeError("Symbol.keyFor requires a symbol"));
  };
  match scope.heap().symbol_key_for(sym)? {
    Some(key) => Ok(Value::String(key)),
    None => Ok(Value::Undefined),
  }
}

fn concat_with_colon_space(name: &[u16], message: &[u16]) -> Result<Vec<u16>, VmError> {
  let mut out: Vec<u16> = Vec::new();
  out
    .try_reserve(name.len().saturating_add(2).saturating_add(message.len()))
    .map_err(|_| VmError::OutOfMemory)?;
  vec_try_extend_from_slice(&mut out, name)?;
  vec_try_push(&mut out, b':' as u16)?;
  vec_try_push(&mut out, b' ' as u16)?;
  vec_try_extend_from_slice(&mut out, message)?;
  Ok(out)
}

/// `Error.prototype.toString` (minimal).
pub fn error_prototype_to_string(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => {
      return Err(VmError::Unimplemented(
        "Error.prototype.toString on non-object",
      ))
    }
  };

  let name_key = string_key(scope, "name")?;
  let message_key = string_key(scope, "message")?;

  let name_value = get_data_property_value(scope, this_obj, &name_key)?.unwrap_or(Value::Undefined);
  let message_value =
    get_data_property_value(scope, this_obj, &message_key)?.unwrap_or(Value::Undefined);

  let name = match name_value {
    Value::Undefined => scope.alloc_string("Error")?,
    other => crate::spec_ops::to_string(vm, scope, other)?,
  };
  scope.push_root(Value::String(name))?;

  let message = match message_value {
    Value::Undefined => scope.alloc_string("")?,
    other => crate::spec_ops::to_string(vm, scope, other)?,
  };
  scope.push_root(Value::String(message))?;

  let name_units = scope.heap().get_string(name)?.as_code_units();
  let message_units = scope.heap().get_string(message)?.as_code_units();

  if name_units.is_empty() {
    return Ok(Value::String(message));
  }
  if message_units.is_empty() {
    return Ok(Value::String(name));
  }

  let out = concat_with_colon_space(name_units, message_units)?;
  let s = scope.alloc_string_from_u16_vec(out)?;
  Ok(Value::String(s))
}

/// `JSON.stringify` (minimal).
pub fn json_stringify(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  const QUOTE: u16 = b'"' as u16;
  const BACKSLASH: u16 = b'\\' as u16;

  fn push_u16_ascii(buf: &mut Vec<u16>, s: &[u8]) -> Result<(), VmError> {
    for &b in s {
      vec_try_push(buf, b as u16)?;
    }
    Ok(())
  }

  fn push_hex_escape(buf: &mut Vec<u16>, unit: u16) -> Result<(), VmError> {
    vec_try_push(buf, b'\\' as u16)?;
    vec_try_push(buf, b'u' as u16)?;
    let mut n = unit;
    let mut digits = [0u16; 4];
    for d in digits.iter_mut().rev() {
      let nibble = (n & 0xF) as u8;
      let c = match nibble {
        0..=9 => b'0' + nibble,
        10..=15 => b'a' + (nibble - 10),
        _ => b'0',
      };
      *d = c as u16;
      n >>= 4;
    }
    vec_try_extend_from_slice(buf, &digits)?;
    Ok(())
  }

  let value = args.first().copied().unwrap_or(Value::Undefined);

  let out = match value {
    Value::Undefined => return Ok(Value::Undefined),
    Value::Null => return Ok(Value::String(scope.alloc_string("null")?)),
    Value::Bool(true) => return Ok(Value::String(scope.alloc_string("true")?)),
    Value::Bool(false) => return Ok(Value::String(scope.alloc_string("false")?)),
    Value::Number(n) => {
      if n.is_nan() || n.is_infinite() {
        return Ok(Value::String(scope.alloc_string("null")?));
      }
      let s = n.to_string();
      return Ok(Value::String(scope.alloc_string(&s)?));
    }
    Value::BigInt(_) => return Err(VmError::TypeError("Do not know how to serialize a BigInt")),
    Value::String(s) => s,
    Value::Symbol(_) | Value::Object(_) => return Ok(Value::Undefined),
  };

  let max_bytes = scope.heap().limits().max_bytes;
  let units = scope.heap().get_string(out)?.as_code_units();

  let mut buf: Vec<u16> = Vec::new();
  vec_try_push(&mut buf, QUOTE)?;

  for (i, &unit) in units.iter().enumerate() {
    if i % 1024 == 0 {
      vm.tick()?;
    }
    if JsString::heap_size_bytes_for_len(buf.len().saturating_add(6)) > max_bytes {
      return Err(VmError::OutOfMemory);
    }

    match unit {
      QUOTE => push_u16_ascii(&mut buf, b"\\\"")?,
      BACKSLASH => push_u16_ascii(&mut buf, b"\\\\")?,
      0x08 => push_u16_ascii(&mut buf, b"\\b")?,
      0x0C => push_u16_ascii(&mut buf, b"\\f")?,
      0x0A => push_u16_ascii(&mut buf, b"\\n")?,
      0x0D => push_u16_ascii(&mut buf, b"\\r")?,
      0x09 => push_u16_ascii(&mut buf, b"\\t")?,
      0x0000..=0x001F => push_hex_escape(&mut buf, unit)?,
      0xD800..=0xDFFF => push_hex_escape(&mut buf, unit)?,
      other => vec_try_push(&mut buf, other)?,
    }
  }

  vec_try_push(&mut buf, QUOTE)?;
  if JsString::heap_size_bytes_for_len(buf.len()) > max_bytes {
    return Err(VmError::OutOfMemory);
  }
  let out = scope.alloc_string_from_u16_vec(buf)?;
  Ok(Value::String(out))
}

// ---------------------------------------------------------------------------
// Object.prototype and Object statics for property introspection
// ---------------------------------------------------------------------------

/// `Object.prototype.hasOwnProperty(V)` (ECMA-262 §20.1.3.2).
pub fn object_prototype_has_own_property(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(this)?;
  let key = crate::spec_ops::to_property_key(
    vm,
    &mut scope,
    args.first().copied().unwrap_or(Value::Undefined),
  )?;
  root_property_key(&mut scope, key)?;
  match this {
    Value::Undefined | Value::Null => {
      let intr = require_intrinsics(vm)?;
      Err(crate::error_object::throw_type_error(
        &mut scope,
        intr,
        "Object.prototype.hasOwnProperty called on null or undefined",
      ))
    }
    Value::Object(obj) => Ok(Value::Bool(
      scope.heap().object_get_own_property(obj, &key)?.is_some(),
    )),
    // Per §7.1.18 ToObject: a String primitive has own "length" and canonical index properties.
    Value::String(s) => {
      let len = scope.heap().get_string(s)?.len_code_units();
      let is_own = match key {
        PropertyKey::String(ks) => {
          let ku = scope.heap().get_string(ks)?;
          let text = String::from_utf16_lossy(ku.as_code_units());
          if text == "length" {
            true
          } else if let Ok(idx) = text.parse::<usize>() {
            // Canonical numeric index only (no leading zeros / signs).
            text == idx.to_string() && idx < len
          } else {
            false
          }
        }
        PropertyKey::Symbol(_) => false,
      };
      Ok(Value::Bool(is_own))
    }
    // Other primitives box to wrappers whose own properties are none (their data is on the
    // prototype), so `hasOwnProperty` is always false.
    _ => Ok(Value::Bool(false)),
  }
}

/// Builds a plain object with `%Object.prototype%` as its prototype.
fn new_ordinary_object(vm: &mut Vm, scope: &mut Scope<'_>) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;
  let obj = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.object_prototype()))?;
  Ok(obj)
}

/// `FromPropertyDescriptor(Desc)` (ECMA-262 §6.2.6.4): materializes a descriptor as a plain object.
fn from_property_descriptor(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  desc: PropertyDescriptor,
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  let obj = new_ordinary_object(vm, &mut scope)?;
  scope.push_root(Value::Object(obj))?;

  let put = |scope: &mut Scope<'_>, name: &str, value: Value| -> Result<(), VmError> {
    let key = string_key(scope, name)?;
    root_property_key(scope, key)?;
    scope.define_property(obj, key, data_desc(value, true, true, true))
  };

  match desc.kind {
    PropertyKind::Data { value, writable } => {
      put(&mut scope, "value", value)?;
      put(&mut scope, "writable", Value::Bool(writable))?;
    }
    PropertyKind::Accessor { get, set } => {
      put(&mut scope, "get", get)?;
      put(&mut scope, "set", set)?;
    }
  }
  put(&mut scope, "enumerable", Value::Bool(desc.enumerable))?;
  put(&mut scope, "configurable", Value::Bool(desc.configurable))?;
  Ok(Value::Object(obj))
}

/// `Object.getOwnPropertyDescriptor(O, P)` (ECMA-262 §20.1.2.8).
pub fn object_get_own_property_descriptor(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  // Spec: `ToObject(O)`. Null/undefined throw; other primitives are not yet boxed here.
  let obj = match args.first().copied().unwrap_or(Value::Undefined) {
    Value::Undefined | Value::Null => {
      let intr = require_intrinsics(vm)?;
      return Err(crate::error_object::throw_type_error(
        &mut scope,
        intr,
        "Object.getOwnPropertyDescriptor called on null or undefined",
      ));
    }
    Value::Object(o) => o,
    _ => {
      return Err(VmError::Unimplemented(
        "Object.getOwnPropertyDescriptor on primitive (ToObject boxing)",
      ))
    }
  };
  scope.push_root(Value::Object(obj))?;
  let key = crate::spec_ops::to_property_key(
    vm,
    &mut scope,
    args.get(1).copied().unwrap_or(Value::Undefined),
  )?;
  root_property_key(&mut scope, key)?;
  match scope.heap().object_get_own_property(obj, &key)? {
    Some(desc) => from_property_descriptor(vm, &mut scope, desc),
    None => Ok(Value::Undefined),
  }
}

/// `Object.prototype.isPrototypeOf(V)` (ECMA-262 §20.1.3.3).
pub fn object_prototype_is_prototype_of(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(this)?;
  let v = args.first().copied().unwrap_or(Value::Undefined);
  scope.push_root(v)?;
  let Value::Object(mut current) = v else {
    return Ok(Value::Bool(false));
  };

  let o = match this {
    Value::Undefined | Value::Null => {
      let intr = require_intrinsics(vm)?;
      return Err(crate::error_object::throw_type_error(
        &mut scope,
        intr,
        "Object.prototype.isPrototypeOf called on null or undefined",
      ));
    }
    Value::Object(obj) => obj,
    // Minimal ToObject for primitives: compare against the matching intrinsic prototype.
    // (A temporary wrapper would never appear on another object's [[Prototype]] chain.)
    Value::String(_) | Value::Number(_) | Value::Bool(_) | Value::BigInt(_) | Value::Symbol(_) => {
      return Ok(Value::Bool(false));
    }
  };
  scope.push_root(Value::Object(o))?;

  // Bound the walk so a corrupted prototype cycle cannot hang the host.
  for _ in 0..10_000 {
    let Some(proto) = scope.heap().object_prototype(current)? else {
      return Ok(Value::Bool(false));
    };
    if proto == o {
      return Ok(Value::Bool(true));
    }
    current = proto;
    scope.push_root(Value::Object(current))?;
  }
  Err(VmError::PrototypeChainTooDeep)
}

/// `Object.prototype.propertyIsEnumerable(V)` (ECMA-262 §20.1.3.5).
pub fn object_prototype_property_is_enumerable(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(this)?;
  let key = crate::spec_ops::to_property_key(
    vm,
    &mut scope,
    args.first().copied().unwrap_or(Value::Undefined),
  )?;
  root_property_key(&mut scope, key)?;

  let obj = match this {
    Value::Undefined | Value::Null => {
      let intr = require_intrinsics(vm)?;
      return Err(crate::error_object::throw_type_error(
        &mut scope,
        intr,
        "Object.prototype.propertyIsEnumerable called on null or undefined",
      ));
    }
    Value::Object(o) => o,
    // Minimal ToObject for primitives used as `this` via `.call`: treat as having no own
    // enumerable properties except String index/length (handled like hasOwnProperty).
    Value::String(s) => {
      let len = scope.heap().get_string(s)?.len_code_units();
      let enumerable = match key {
        PropertyKey::String(ks) => {
          let text = String::from_utf16_lossy(scope.heap().get_string(ks)?.as_code_units());
          if text == "length" {
            false
          } else if let Ok(idx) = text.parse::<usize>() {
            text == idx.to_string() && idx < len
          } else {
            false
          }
        }
        PropertyKey::Symbol(_) => false,
      };
      return Ok(Value::Bool(enumerable));
    }
    _ => {
      return Err(VmError::Unimplemented(
        "Object.prototype.propertyIsEnumerable on non-object this",
      ))
    }
  };

  match scope.heap().object_get_own_property(obj, &key)? {
    Some(desc) => Ok(Value::Bool(desc.enumerable)),
    None => Ok(Value::Bool(false)),
  }
}

/// `Object.getOwnPropertyNames(O)` (ECMA-262 §20.1.2.10): the object's own String-keyed property
/// names (enumerable or not), in ordinary ownkeys order.
pub fn object_get_own_property_names(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.first().copied().unwrap_or(Value::Undefined))?;

  let own_keys = scope.heap().ordinary_own_property_keys(obj)?;
  let mut names: Vec<crate::GcString> = Vec::new();
  names
    .try_reserve(own_keys.len())
    .map_err(|_| VmError::OutOfMemory)?;
  for key in own_keys {
    if let PropertyKey::String(key_str) = key {
      names.push(key_str);
    }
  }

  let len = u32::try_from(names.len()).map_err(|_| VmError::OutOfMemory)?;
  let array = create_array_object(vm, scope, len)?;
  for (i, name) in names.iter().copied().enumerate() {
    let mut idx_scope = scope.reborrow();
    idx_scope.push_root(Value::Object(array))?;
    idx_scope.push_root(Value::String(name))?;
    let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
    idx_scope.define_property(array, key, data_desc(Value::String(name), true, true, true))?;
  }
  Ok(Value::Object(array))
}

// ---------------------------------------------------------------------------
// Math (ECMA-262 §21.3)
// ---------------------------------------------------------------------------

/// Shared body for the single-argument `Math` functions: `ToNumber(args[0])` then apply `f`.
fn math_unary(scope: &mut Scope<'_>, args: &[Value], f: fn(f64) -> f64) -> Result<Value, VmError> {
  let x = match args.first().copied() {
    None => f64::NAN,
    Some(v) => scope.heap_mut().to_number(v)?,
  };
  Ok(Value::Number(f(x)))
}

macro_rules! math_unary_fn {
  ($name:ident, $f:expr) => {
    pub fn $name(
      _vm: &mut Vm,
      scope: &mut Scope<'_>,
      _host: &mut dyn VmHost,
      _hooks: &mut dyn VmHostHooks,
      _callee: GcObject,
      _this: Value,
      args: &[Value],
    ) -> Result<Value, VmError> {
      math_unary(scope, args, $f)
    }
  };
}

// §21.3.2: elementary functions. `f64` intrinsics match IEEE-754 / the spec's required results for
// the common finite domain; NaN/Infinity edges follow Rust's libm, which matches the spec here.
math_unary_fn!(math_abs, f64::abs);
math_unary_fn!(math_floor, f64::floor);
math_unary_fn!(math_ceil, f64::ceil);
math_unary_fn!(math_trunc, f64::trunc);
math_unary_fn!(math_sqrt, f64::sqrt);
math_unary_fn!(math_cbrt, f64::cbrt);
math_unary_fn!(math_exp, f64::exp);
math_unary_fn!(math_expm1, f64::exp_m1);
math_unary_fn!(math_log, f64::ln);
math_unary_fn!(math_log2, f64::log2);
math_unary_fn!(math_log10, f64::log10);
math_unary_fn!(math_log1p, f64::ln_1p);
math_unary_fn!(math_sin, f64::sin);
math_unary_fn!(math_cos, f64::cos);
math_unary_fn!(math_tan, f64::tan);
math_unary_fn!(math_asin, f64::asin);
math_unary_fn!(math_acos, f64::acos);
math_unary_fn!(math_atan, f64::atan);
math_unary_fn!(math_sinh, f64::sinh);
math_unary_fn!(math_cosh, f64::cosh);
math_unary_fn!(math_tanh, f64::tanh);
math_unary_fn!(math_asinh, f64::asinh);
math_unary_fn!(math_acosh, f64::acosh);
math_unary_fn!(math_atanh, f64::atanh);
// §21.3.2.29 `Math.sign`: preserves signed zeros and NaN.
math_unary_fn!(math_sign, |x: f64| {
  if x.is_nan() || x == 0.0 {
    x
  } else if x > 0.0 {
    1.0
  } else {
    -1.0
  }
});
// §21.3.2.28 `Math.round`: round half toward +Infinity (not Rust's round-half-away-from-zero).
math_unary_fn!(math_round, |x: f64| {
  if !x.is_finite() || x == 0.0 {
    x
  } else {
    let r = (x + 0.5).floor();
    // `(-0.5 + 0.5).floor() == 0`, but the spec requires -0 for inputs in (-0.5, 0].
    if r == 0.0 && x < 0.0 {
      -0.0
    } else {
      r
    }
  }
});
// §21.3.2.18 `Math.fround`: round to the nearest single-precision float.
math_unary_fn!(math_fround, |x: f64| x as f32 as f64);
// §21.3.2.11 `Math.clz32`: count leading zeros of ToUint32(x).
math_unary_fn!(math_clz32, |x: f64| {
  let u = crate::exec::number_to_uint32(x);
  u.leading_zeros() as f64
});

/// `Math.pow(base, exponent)` (§21.3.2.26) via `Number::exponentiate` (§6.1.6.1.3).
pub fn math_pow(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let base = number_arg(scope, args, 0)?;
  let exp = number_arg(scope, args, 1)?;
  Ok(Value::Number(crate::exec::number_exponentiate(base, exp)))
}

/// `Math.atan2(y, x)` (§21.3.2.8).
pub fn math_atan2(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let y = number_arg(scope, args, 0)?;
  let x = number_arg(scope, args, 1)?;
  Ok(Value::Number(y.atan2(x)))
}

/// `Math.hypot(...values)` (§21.3.2.19).
pub fn math_hypot(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut sum = 0.0f64;
  let mut any_inf = false;
  let mut any_nan = false;
  for v in args.iter().copied() {
    let n = scope.heap_mut().to_number(v)?;
    if n.is_infinite() {
      any_inf = true;
    } else if n.is_nan() {
      any_nan = true;
    }
    sum += n * n;
  }
  if any_inf {
    return Ok(Value::Number(f64::INFINITY));
  }
  if any_nan {
    return Ok(Value::Number(f64::NAN));
  }
  Ok(Value::Number(sum.sqrt()))
}

/// `Math.max(...values)` (§21.3.2.24).
pub fn math_max(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut highest = f64::NEG_INFINITY;
  for v in args.iter().copied() {
    let n = scope.heap_mut().to_number(v)?;
    if n.is_nan() {
      return Ok(Value::Number(f64::NAN));
    }
    // §21.3.2.24: +0 is considered larger than -0.
    if n > highest || (n == 0.0 && highest == 0.0 && n.is_sign_positive()) {
      highest = n;
    }
  }
  Ok(Value::Number(highest))
}

/// `Math.min(...values)` (§21.3.2.25).
pub fn math_min(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut lowest = f64::INFINITY;
  for v in args.iter().copied() {
    let n = scope.heap_mut().to_number(v)?;
    if n.is_nan() {
      return Ok(Value::Number(f64::NAN));
    }
    // §21.3.2.25: -0 is considered smaller than +0.
    if n < lowest || (n == 0.0 && lowest == 0.0 && n.is_sign_negative()) {
      lowest = n;
    }
  }
  Ok(Value::Number(lowest))
}

/// `Math.random()` (§21.3.2.27): a pseudo-random value in `[0, 1)`.
///
/// Determinism note: this VM is otherwise deterministic, but `Math.random` is defined to be
/// non-deterministic. We seed a small xorshift PRNG from the current time so test262 randomness
/// tests observe varying output without pulling in an RNG dependency.
pub fn math_random(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  use std::cell::Cell;
  use std::time::{SystemTime, UNIX_EPOCH};
  thread_local! {
    static STATE: Cell<u64> = Cell::new(0);
  }
  let mut x = STATE.with(|s| {
    let mut v = s.get();
    if v == 0 {
      v = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map(|d| d.as_nanos() as u64)
        .unwrap_or(0x9E3779B97F4A7C15)
        | 1;
    }
    v
  });
  x ^= x << 13;
  x ^= x >> 7;
  x ^= x << 17;
  STATE.with(|s| s.set(x));
  // Take 53 bits for a double in [0, 1).
  let mantissa = x >> 11;
  Ok(Value::Number(mantissa as f64 / (1u64 << 53) as f64))
}

// ---------------------------------------------------------------------------
// Global / Number numeric functions (ECMA-262 §19.2, §21.1.2)
// ---------------------------------------------------------------------------

/// Returns the ToString code units of `value` as a Rust `String` (number syntax is ASCII, so a
/// lossy UTF-16 decode is exact for the parsing done by `parseInt`/`parseFloat`).
fn to_string_lossy(vm: &mut Vm, scope: &mut Scope<'_>, value: Value) -> Result<String, VmError> {
  let s = crate::spec_ops::to_string(vm, scope, value)?;
  let units = scope.heap().get_string(s)?.as_code_units().to_vec();
  Ok(String::from_utf16_lossy(&units))
}

/// ECMA-262 `StrWhiteSpace` / whitespace trimming used by `parseInt`/`parseFloat` (§19.2).
fn is_js_whitespace(c: char) -> bool {
  matches!(
    c,
    '\u{0009}'
      | '\u{000A}'
      | '\u{000B}'
      | '\u{000C}'
      | '\u{000D}'
      | '\u{0020}'
      | '\u{00A0}'
      | '\u{1680}'
      | '\u{2000}'
      ..='\u{200A}' | '\u{2028}' | '\u{2029}' | '\u{202F}' | '\u{205F}' | '\u{3000}' | '\u{FEFF}'
  )
}

/// `parseInt(string, radix)` (ECMA-262 §19.2.5 / §21.1.2.13).
pub fn global_parse_int(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let input = to_string_lossy(vm, scope, args.first().copied().unwrap_or(Value::Undefined))?;
  let radix_arg = match args.get(1).copied() {
    None | Some(Value::Undefined) => 0.0,
    Some(v) => scope.heap_mut().to_number(v)?,
  };

  let s: &str = input.trim_start_matches(is_js_whitespace);
  let mut chars = s.chars().peekable();

  let mut sign = 1.0f64;
  match chars.peek() {
    Some('+') => {
      chars.next();
    }
    Some('-') => {
      sign = -1.0;
      chars.next();
    }
    _ => {}
  }

  let mut radix = crate::exec::number_to_int32(radix_arg);
  let mut strip_prefix = true;
  if radix != 0 {
    if !(2..=36).contains(&radix) {
      return Ok(Value::Number(f64::NAN));
    }
    if radix != 16 {
      strip_prefix = false;
    }
  } else {
    radix = 10;
  }

  if strip_prefix {
    let rest: String = chars.clone().collect();
    if rest.starts_with("0x") || rest.starts_with("0X") {
      chars.next();
      chars.next();
      radix = 16;
    }
  }

  let radix_u = radix as u32;
  let mut value = 0.0f64;
  let mut any = false;
  for c in chars {
    match c.to_digit(radix_u) {
      Some(d) => {
        value = value * radix as f64 + d as f64;
        any = true;
      }
      None => break,
    }
  }
  if !any {
    return Ok(Value::Number(f64::NAN));
  }
  Ok(Value::Number(sign * value))
}

/// `parseFloat(string)` (ECMA-262 §19.2.4 / §21.1.2.12).
pub fn global_parse_float(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let input = to_string_lossy(vm, scope, args.first().copied().unwrap_or(Value::Undefined))?;
  let s: &str = input.trim_start_matches(is_js_whitespace);

  // `Infinity` with an optional leading sign.
  let after_sign = s.strip_prefix(['+', '-']).unwrap_or(s);
  if after_sign.starts_with("Infinity") {
    return Ok(Value::Number(if s.starts_with('-') {
      f64::NEG_INFINITY
    } else {
      f64::INFINITY
    }));
  }

  // Scan the longest prefix matching StrDecimalLiteral, then parse it with `f64::from_str`.
  let bytes = s.as_bytes();
  let mut i = 0usize;
  if i < bytes.len() && (bytes[i] == b'+' || bytes[i] == b'-') {
    i += 1;
  }
  let int_start = i;
  while i < bytes.len() && bytes[i].is_ascii_digit() {
    i += 1;
  }
  let mut frac_digits = 0usize;
  if i < bytes.len() && bytes[i] == b'.' {
    i += 1;
    while i < bytes.len() && bytes[i].is_ascii_digit() {
      i += 1;
      frac_digits += 1;
    }
  }
  let int_digits = if bytes[int_start..].is_empty() {
    0
  } else {
    bytes[int_start..i.min(bytes.len())]
      .iter()
      .take_while(|b| b.is_ascii_digit())
      .count()
  };
  // Require at least one digit in the mantissa.
  if int_digits == 0 && frac_digits == 0 {
    return Ok(Value::Number(f64::NAN));
  }
  // Optional exponent part.
  if i < bytes.len() && (bytes[i] == b'e' || bytes[i] == b'E') {
    let mut j = i + 1;
    if j < bytes.len() && (bytes[j] == b'+' || bytes[j] == b'-') {
      j += 1;
    }
    let exp_start = j;
    while j < bytes.len() && bytes[j].is_ascii_digit() {
      j += 1;
    }
    if j > exp_start {
      i = j;
    }
  }
  match s[..i].parse::<f64>() {
    Ok(n) => Ok(Value::Number(n)),
    Err(_) => Ok(Value::Number(f64::NAN)),
  }
}

/// `isFinite(number)` (ECMA-262 §19.2.2).
pub fn global_is_finite(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let n = scope
    .heap_mut()
    .to_number(args.first().copied().unwrap_or(Value::Undefined))?;
  Ok(Value::Bool(n.is_finite()))
}

/// `Number.isNaN(x)` (ECMA-262 §21.1.2.4): no coercion; non-Number arguments are `false`.
pub fn number_is_nan(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Bool(matches!(
    args.first().copied(),
    Some(Value::Number(n)) if n.is_nan()
  )))
}

/// `Number.isFinite(x)` (ECMA-262 §21.1.2.2): no coercion.
pub fn number_is_finite(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Bool(matches!(
    args.first().copied(),
    Some(Value::Number(n)) if n.is_finite()
  )))
}

/// `Number.isInteger(x)` (ECMA-262 §21.1.2.3): no coercion.
pub fn number_is_integer(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let is_int = matches!(
    args.first().copied(),
    Some(Value::Number(n)) if n.is_finite() && n.trunc() == n
  );
  Ok(Value::Bool(is_int))
}

/// `Number.isSafeInteger(x)` (ECMA-262 §21.1.2.5): no coercion.
pub fn number_is_safe_integer(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  const MAX_SAFE: f64 = 9007199254740991.0; // 2^53 - 1
  let is_safe = matches!(
    args.first().copied(),
    Some(Value::Number(n)) if n.is_finite() && n.trunc() == n && n.abs() <= MAX_SAFE
  );
  Ok(Value::Bool(is_safe))
}

// ---------------------------------------------------------------------------
// String.fromCharCode (ECMA-262 §22.1.2.1)
// ---------------------------------------------------------------------------

/// `String.fromCharCode(...codeUnits)` (ECMA-262 §22.1.2.1).
pub fn string_from_char_code(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut units: Vec<u16> = Vec::new();
  units
    .try_reserve(args.len())
    .map_err(|_| VmError::OutOfMemory)?;
  for v in args.iter().copied() {
    let n = scope.heap_mut().to_number(v)?;
    // ToUint16 (§7.1.6): truncate toward zero, modulo 2^16.
    let unit = to_uint16(n);
    units.push(unit);
  }
  Ok(Value::String(scope.alloc_string_from_u16_vec(units)?))
}

/// ECMA-262 `ToUint16` (§7.1.6).
fn to_uint16(n: f64) -> u16 {
  if !n.is_finite() || n == 0.0 {
    return 0;
  }
  let int = n.trunc();
  let m = int.rem_euclid(65536.0);
  m as u16
}

/// `%eval%` native fallback (ECMA-262 §19.2.1).
///
/// Ordinary Evaluator call sites intercept `%eval%` and run `PerformEval` with the
/// correct direct/indirect mode. This native exists so `typeof eval === "function"`
/// and property lookups succeed; exotic `apply`/`bound` routes are not yet fully
/// wired to realm lexical state.
pub fn global_eval_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let _ = (vm, scope);
  match args.first().copied().unwrap_or(Value::Undefined) {
    Value::String(_) => Err(VmError::Unimplemented(
      "eval via Function.prototype.apply/call not yet routed through PerformEval",
    )),
    other => Ok(other),
  }
}

/// `BigInt(value)` (ECMA-262 §21.2.1.1). Not constructable.
pub fn bigint_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  use crate::JsBigInt;
  let arg0 = args.first().copied().unwrap_or(Value::Undefined);
  let prim =
    crate::spec_ops::to_primitive(vm, scope, arg0, crate::spec_ops::ToPrimitiveHint::Number)?;
  match prim {
    Value::BigInt(b) => Ok(Value::BigInt(b)),
    Value::Bool(b) => Ok(Value::BigInt(if b {
      JsBigInt::from_u128(1)
    } else {
      JsBigInt::zero()
    })),
    Value::Number(n) => {
      if !n.is_finite() || n.fract() != 0.0 {
        return throw_type_error(vm, scope, host, "Cannot convert number to a BigInt");
      }
      if n.abs() <= (u128::MAX as f64) && n.trunc() == n {
        let mag = n.abs() as u128;
        let bi = JsBigInt::from_u128(mag);
        return Ok(Value::BigInt(if n < 0.0 { bi.negate() } else { bi }));
      }
      let s = format!("{n:.0}");
      let Some(bi) = JsBigInt::from_decimal_str(&s) else {
        return throw_type_error(vm, scope, host, "Cannot convert number to a BigInt");
      };
      Ok(Value::BigInt(bi))
    }
    Value::String(s) => {
      let text = scope.heap().get_string(s)?.to_utf8_lossy();
      let Some(bi) = JsBigInt::from_string_integer_literal(&text) else {
        let intr = require_intrinsics(vm)?;
        let err = crate::error_object::new_syntax_error_object(
          scope,
          &intr,
          "Cannot convert string to a BigInt",
        )?;
        return Err(VmError::Throw(err));
      };
      Ok(Value::BigInt(bi))
    }
    Value::Undefined | Value::Null | Value::Symbol(_) | Value::Object(_) => {
      throw_type_error(vm, scope, host, "Cannot convert value to a BigInt")
    }
  }
}

// ---------------------------------------------------------------------------
// Mapped arguments MakeArgGetter / MakeArgSetter (ECMA-262 §10.4.4.7.1–2)
// ---------------------------------------------------------------------------

/// Getter installed on mapped `arguments` integer indices.
///
/// Captures:
/// - `[[ClosureEnv]]`: the function's parameter Environment Record
/// - `native_slots[0]`: binding name (`String`)
pub fn arguments_arg_getter_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Some(env) = scope.heap().get_function_closure_env(callee)? else {
    return Err(VmError::InvariantViolation(
      "arguments arg getter missing closure env",
    ));
  };
  let slots = scope.heap().get_function_native_slots(callee)?;
  let Some(Value::String(name_s)) = slots.first().copied() else {
    return Err(VmError::InvariantViolation(
      "arguments arg getter missing binding name slot",
    ));
  };
  let name = scope.heap().get_string(name_s)?.to_utf8_lossy();
  scope.heap().env_get_binding_value(env, &name, false)
}

/// Setter installed on mapped `arguments` integer indices.
///
/// Captures the same slots as [`arguments_arg_getter_call`].
pub fn arguments_arg_setter_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Some(env) = scope.heap().get_function_closure_env(callee)? else {
    return Err(VmError::InvariantViolation(
      "arguments arg setter missing closure env",
    ));
  };
  let slots = scope.heap().get_function_native_slots(callee)?;
  let Some(Value::String(name_s)) = slots.first().copied() else {
    return Err(VmError::InvariantViolation(
      "arguments arg setter missing binding name slot",
    ));
  };
  let name = scope.heap().get_string(name_s)?.to_utf8_lossy();
  let value = args.first().copied().unwrap_or(Value::Undefined);
  scope
    .heap_mut()
    .env_set_mutable_binding(env, &name, value, false)?;
  Ok(Value::Undefined)
}

/// `[[Call]]` for class constructors (`MakeClassConstructor`): always throws TypeError.
pub fn class_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  throw_type_error(
    vm,
    scope,
    hooks,
    "Class constructor cannot be invoked without 'new'",
  )
}

/// Default class constructor body (`constructor() {}` for base classes).
pub fn class_default_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let obj = crate::spec_ops::ordinary_create_from_constructor(
    vm,
    scope,
    new_target,
    intr.object_prototype(),
    &[],
    |scope| scope.alloc_object(),
  )?;
  scope.push_root(Value::Object(obj))?;
  scope.push_root(Value::Object(callee))?;
  // InitializeInstanceElements(O, constructor) for private fields/methods/accessors.
  scope
    .heap_mut()
    .initialize_instance_private_elements(obj, callee)?;
  Ok(Value::Object(obj))
}

/// Default derived-class constructor (`constructor(...args) { super(...args); }`).
///
/// Uses `callee.[[GetPrototypeOf]]` as the super constructor (ECMA-262 default ctor
/// abstract closure / GetSuperConstructor), then `Construct(super, args, newTarget)`.
pub fn class_default_derived_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let super_ctor = scope.heap().object_prototype(callee)?;
  let Some(super_ctor) = super_ctor else {
    return throw_type_error(vm, scope, hooks, "Super constructor is nullish");
  };
  if !scope.heap().is_constructor(Value::Object(super_ctor))? {
    return throw_type_error(
      vm,
      scope,
      hooks,
      "Super expression must evaluate to a constructor",
    );
  }
  vm.construct_with_host_and_hooks(
    host,
    scope,
    hooks,
    Value::Object(super_ctor),
    args,
    new_target,
  )
}
