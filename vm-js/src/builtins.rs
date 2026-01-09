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
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, args)
}

pub fn object_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
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
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn array_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn function_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Function constructor"))
}

pub fn function_constructor_construct(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Function constructor"))
}

pub fn error_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Error constructor"))
}

pub fn error_constructor_construct(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Error constructor"))
}

