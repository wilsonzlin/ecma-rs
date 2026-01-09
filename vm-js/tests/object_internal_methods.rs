use vm_js::{
  ordinary_get, ordinary_set, own_property_keys, Heap, HeapLimits, PropertyDescriptor, PropertyKey,
  PropertyKind, Scope, Value, Vm, VmError, VmOptions,
};

fn getter_returns_own_value(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Ok(Value::Undefined);
  };
  let key = PropertyKey::from_string(scope.alloc_string("value")?);
  Ok(
    scope
      .heap()
      .object_get_own_data_property_value(this_obj, &key)?
      .unwrap_or(Value::Undefined),
  )
}

fn setter_sets_seen(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Ok(Value::Undefined);
  };
  let value = args.get(0).copied().unwrap_or(Value::Undefined);

  let key = PropertyKey::from_string(scope.alloc_string("seen")?);
  scope.define_property(
    this_obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value,
        writable: true,
      },
    },
  )?;

  Ok(Value::Undefined)
}

#[test]
fn ordinary_get_reads_data_properties_own_and_via_prototype() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let proto = scope.alloc_object()?;
  let key_x = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    proto,
    key_x,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(1.0),
        writable: true,
      },
    },
  )?;

  let child = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(child, Some(proto))?;

  let key_y = PropertyKey::from_string(scope.alloc_string("y")?);
  scope.define_property(
    child,
    key_y,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(2.0),
        writable: true,
      },
    },
  )?;

  assert_eq!(
    ordinary_get(&mut vm, &mut scope, Value::Object(child), key_y)?,
    Value::Number(2.0)
  );
  assert_eq!(
    ordinary_get(&mut vm, &mut scope, Value::Object(child), key_x)?,
    Value::Number(1.0)
  );

  Ok(())
}

#[test]
fn ordinary_get_invokes_accessor_getter_with_receiver() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let call_id = vm.register_native_call(getter_returns_own_value);
  let getter = {
    let name = scope.alloc_string("get_value")?;
    scope.alloc_native_function(call_id, None, name, 0)?
  };

  let proto = scope.alloc_object()?;
  let key_value_proto = PropertyKey::from_string(scope.alloc_string("value")?);
  scope.define_property(
    proto,
    key_value_proto,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(20.0),
        writable: true,
      },
    },
  )?;

  let key_prop = PropertyKey::from_string(scope.alloc_string("prop")?);
  scope.define_property(
    proto,
    key_prop,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Accessor {
        get: Value::Object(getter),
        set: Value::Undefined,
      },
    },
  )?;

  let child = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(child, Some(proto))?;
  let key_value_child = PropertyKey::from_string(scope.alloc_string("value")?);
  scope.define_property(
    child,
    key_value_child,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(10.0),
        writable: true,
      },
    },
  )?;

  let value = ordinary_get(&mut vm, &mut scope, Value::Object(child), key_prop)?;
  assert_eq!(value, Value::Number(10.0));

  Ok(())
}

#[test]
fn ordinary_set_invokes_accessor_setter_with_receiver() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let call_id = vm.register_native_call(setter_sets_seen);
  let setter = {
    let name = scope.alloc_string("set_seen")?;
    scope.alloc_native_function(call_id, None, name, 1)?
  };

  let proto = scope.alloc_object()?;
  let key_prop = PropertyKey::from_string(scope.alloc_string("prop")?);
  scope.define_property(
    proto,
    key_prop,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Accessor {
        get: Value::Undefined,
        set: Value::Object(setter),
      },
    },
  )?;

  let child = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(child, Some(proto))?;

  ordinary_set(
    &mut vm,
    &mut scope,
    Value::Object(child),
    key_prop,
    Value::Number(99.0),
    true,
  )?;

  let key_seen = PropertyKey::from_string(scope.alloc_string("seen")?);
  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(child, &key_seen)?,
    Some(Value::Number(99.0))
  );
  assert!(scope.heap().object_get_own_property(proto, &key_seen)?.is_none());

  Ok(())
}

#[test]
fn ordinary_set_on_inherited_writable_data_property_creates_own_property() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let proto = scope.alloc_object()?;
  let key_x = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    proto,
    key_x,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(1.0),
        writable: true,
      },
    },
  )?;

  let child = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(child, Some(proto))?;

  ordinary_set(
    &mut vm,
    &mut scope,
    Value::Object(child),
    key_x,
    Value::Number(2.0),
    true,
  )?;

  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(proto, &key_x)?,
    Some(Value::Number(1.0))
  );
  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(child, &key_x)?,
    Some(Value::Number(2.0))
  );

  Ok(())
}

#[test]
fn own_property_keys_orders_array_indices_strings_and_symbols() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let mut scope = heap.scope();
  let obj = scope.alloc_object()?;

  let k2 = PropertyKey::from_string(scope.alloc_string("2")?);
  let ka = PropertyKey::from_string(scope.alloc_string("a")?);
  let k0 = PropertyKey::from_string(scope.alloc_string("0")?);
  let sym = scope.alloc_symbol(None)?;
  let ksym = PropertyKey::from_symbol(sym);

  // Insert out of order; `[[OwnPropertyKeys]]` should re-order indices but preserve insertion order
  // for non-indices and symbols.
  for k in [k2, ka, ksym, k0] {
    scope.define_property(
      obj,
      k,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Undefined,
          writable: true,
        },
      },
    )?;
  }

  let keys = own_property_keys(scope.heap(), obj)?;
  assert_eq!(keys, vec![k0, k2, ka, ksym]);

  Ok(())
}
