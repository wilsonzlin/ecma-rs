use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Scope, Value, Vm, VmError};

fn data_desc(value: Value, writable: bool, enumerable: bool, configurable: bool) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable,
    configurable,
    kind: PropertyKind::Data { value, writable },
  }
}

fn require_intrinsics(vm: &Vm) -> Result<crate::Intrinsics, VmError> {
  vm.intrinsics()
    .ok_or(VmError::Unimplemented("native builtins require Vm::intrinsics to be set"))
}

pub fn function_prototype_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn object_constructor_impl(vm: &mut Vm, scope: &mut Scope<'_>, args: &[Value]) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let arg0 = args.get(0).copied().unwrap_or(Value::Undefined);
  match arg0 {
    Value::Undefined | Value::Null => {
      let obj = scope.alloc_object()?;
      scope
        .heap_mut()
        .object_set_prototype(obj, Some(intr.object_prototype()))?;
      Ok(Value::Object(obj))
    }
    Value::Object(obj) => Ok(Value::Object(obj)),
    _ => Err(VmError::Unimplemented("ToObject boxing")),
  }
}

pub fn object_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, args)
}

pub fn object_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, args)
}

fn create_array_object(vm: &mut Vm, scope: &mut Scope<'_>, len: u32) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;

  let array = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(array, Some(intr.array_prototype()))?;

  let length_key = PropertyKey::from_string(scope.alloc_string("length")?);
  scope.define_property(
    array,
    length_key,
    data_desc(Value::Number(len as f64), true, false, false),
  )?;

  Ok(array)
}

fn array_constructor_impl(vm: &mut Vm, scope: &mut Scope<'_>, args: &[Value]) -> Result<Value, VmError> {
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
        idx_scope.push_root(Value::Object(array));
        idx_scope.push_root(el);

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
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn array_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn function_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Function constructor"))
}

pub fn function_constructor_construct(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Function constructor"))
}

pub fn error_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  error_constructor_construct(vm, scope, callee, args, Value::Object(callee))
}

pub fn error_constructor_construct(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
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

  // Message argument: AggregateError(message is the second argument).
  let message_arg = if scope.heap().get_string(name)?.to_utf8_lossy() == "AggregateError" {
    args.get(1).copied().or_else(|| args.first().copied())
  } else {
    args.first().copied()
  };

  let message_string = match message_arg {
    Some(Value::Undefined) | None => scope.alloc_string("")?,
    Some(other) => scope.heap_mut().to_string(other)?,
  };
  scope.push_root(Value::String(message_string));

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(instance_prototype))?;

  let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
  scope.define_property(obj, name_key, data_desc(Value::String(name), true, false, true))?;

  let message_key = PropertyKey::from_string(scope.alloc_string("message")?);
  scope.define_property(
    obj,
    message_key,
    data_desc(Value::String(message_string), true, false, true),
  )?;

  Ok(Value::Object(obj))
}
