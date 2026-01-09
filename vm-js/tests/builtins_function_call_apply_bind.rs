use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Realm, Scope, Value,
  Vm, VmError, VmOptions,
};

fn data_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

fn get_builtin(scope: &mut Scope<'_>, realm: &Realm, name: &str) -> Result<Value, VmError> {
  let key_s = scope.alloc_string(name)?;
  let key = PropertyKey::from_string(key_s);
  let proto = realm.intrinsics().function_prototype();
  let desc = scope
    .heap()
    .get_property(proto, &key)?
    .ok_or(VmError::PropertyNotFound)?;
  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(value),
    PropertyKind::Accessor { .. } => Err(VmError::Unimplemented(
      "unexpected accessor on Function.prototype builtin",
    )),
  }
}

fn native_add(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let a = match args.get(0).copied().unwrap_or(Value::Undefined) {
    Value::Number(n) => n,
    _ => return Err(VmError::Unimplemented("add: arg0 not number")),
  };
  let b = match args.get(1).copied().unwrap_or(Value::Undefined) {
    Value::Number(n) => n,
    _ => return Err(VmError::Unimplemented("add: arg1 not number")),
  };
  Ok(Value::Number(a + b))
}

fn native_get_x(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(obj) = this else {
    return Ok(Value::Undefined);
  };
  let key_s = scope.alloc_string("x")?;
  let key = PropertyKey::from_string(key_s);
  let desc = scope.heap().get_property(obj, &key)?;
  let value = match desc.map(|d| d.kind) {
    Some(PropertyKind::Data { value, .. }) => value,
    Some(PropertyKind::Accessor { .. }) => {
      return Err(VmError::Unimplemented("get_x: accessor x"));
    }
    None => Value::Undefined,
  };
  Ok(value)
}

#[test]
fn function_prototype_call_apply_bind() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  {
    let mut scope = heap.scope();

    let call_builtin = get_builtin(&mut scope, &realm, "call")?;
    let apply_builtin = get_builtin(&mut scope, &realm, "apply")?;
    let bind_builtin = get_builtin(&mut scope, &realm, "bind")?;

    let call_id = vm.register_native_call(native_add)?;
    let add_name = scope.alloc_string("add")?;
    let add = scope.alloc_native_function(call_id, None, add_name, 2)?;

    // add.call(undefined, 1, 2) === 3
    let result = vm.call(
      &mut scope,
      call_builtin,
      Value::Object(add),
      &[Value::Undefined, Value::Number(1.0), Value::Number(2.0)],
    )?;
    assert_eq!(result, Value::Number(3.0));

    // add.apply(undefined, [1,2]) === 3 (array-like object)
    let arg_array = scope.alloc_object()?;
    scope.push_root(Value::Object(arg_array))?;
    let k0 = PropertyKey::from_string(scope.alloc_string("0")?);
    let k1 = PropertyKey::from_string(scope.alloc_string("1")?);
    let klen = PropertyKey::from_string(scope.alloc_string("length")?);
    scope.define_property(arg_array, k0, data_desc(Value::Number(1.0)))?;
    scope.define_property(arg_array, k1, data_desc(Value::Number(2.0)))?;
    scope.define_property(arg_array, klen, data_desc(Value::Number(2.0)))?;

    let result = vm.call(
      &mut scope,
      apply_builtin,
      Value::Object(add),
      &[Value::Undefined, Value::Object(arg_array)],
    )?;
    assert_eq!(result, Value::Number(3.0));

    // var add1 = add.bind(undefined, 1); add1(2) === 3
    let add1 = vm.call(
      &mut scope,
      bind_builtin,
      Value::Object(add),
      &[Value::Undefined, Value::Number(1.0)],
    )?;
    scope.push_root(add1)?;
    let result = vm.call(&mut scope, add1, Value::Undefined, &[Value::Number(2.0)])?;
    assert_eq!(result, Value::Number(3.0));

    // var o={x:2, f:function(){return this.x;}}; var g=o.f.bind({x:5}); g()===5
    let get_x_id = vm.register_native_call(native_get_x)?;
    let get_x_name = scope.alloc_string("get_x")?;
    let get_x = scope.alloc_native_function(get_x_id, None, get_x_name, 0)?;

    let bound_this = scope.alloc_object()?;
    scope.push_root(Value::Object(bound_this))?;
    let kx = PropertyKey::from_string(scope.alloc_string("x")?);
    scope.define_property(bound_this, kx, data_desc(Value::Number(5.0)))?;

    let g = vm.call(
      &mut scope,
      bind_builtin,
      Value::Object(get_x),
      &[Value::Object(bound_this)],
    )?;
    scope.push_root(g)?;
    let result = vm.call(&mut scope, g, Value::Undefined, &[])?;
    assert_eq!(result, Value::Number(5.0));
  }

  realm.teardown(&mut heap);
  Ok(())
}
