use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Scope, Value, Vm,
  VmError, VmHostHooks, VmOptions, MAX_PROTOTYPE_CHAIN,
};

fn getter_returns_own_value(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Ok(Value::Undefined);
  };
  let key = PropertyKey::String(scope.alloc_string("value")?);
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
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Value::Object(this_obj) = this else {
    return Ok(Value::Undefined);
  };
  let value = args.get(0).copied().unwrap_or(Value::Undefined);

  let key = PropertyKey::String(scope.alloc_string("seen")?);
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
fn heap_ordinary_get_invokes_accessor_getter_with_receiver() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let (proto, child) = {
    let mut scope = heap.scope();

    let call_id = vm.register_native_call(getter_returns_own_value)?;
    let getter = {
      let name = scope.alloc_string("get_value")?;
      scope.alloc_native_function(call_id, None, name, 0)?
    };

    let proto = scope.alloc_object()?;
    let key_value_proto = PropertyKey::String(scope.alloc_string("value")?);
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

    let key_prop = PropertyKey::String(scope.alloc_string("prop")?);
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
    scope.object_set_prototype(child, Some(proto))?;
    let key_value_child = PropertyKey::String(scope.alloc_string("value")?);
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

    let proto_root = scope.heap_mut().add_root(Value::Object(proto))?;
    let child_root = scope.heap_mut().add_root(Value::Object(child))?;
    drop(scope);

    // Return the roots so the objects stay alive while we call via `Heap` APIs.
    (proto_root, child_root)
  };

  let _proto_obj = heap.get_root(proto).ok_or(VmError::InvalidHandle)?.as_object().unwrap();
  let child_obj = heap.get_root(child).ok_or(VmError::InvalidHandle)?.as_object().unwrap();

  let mut scope = heap.scope();
  let key_prop = PropertyKey::String(scope.alloc_string("prop")?);
  drop(scope);

  let value = heap.ordinary_get(&mut vm, child_obj, key_prop, Value::Object(child_obj))?;
  assert_eq!(value, Value::Number(10.0));

  heap.remove_root(proto);
  heap.remove_root(child);
  Ok(())
}

#[test]
fn heap_ordinary_set_invokes_accessor_setter_with_receiver() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let (proto_root, child_root) = {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(setter_sets_seen)?;
    let setter = {
      let name = scope.alloc_string("set_seen")?;
      scope.alloc_native_function(call_id, None, name, 1)?
    };

    let proto = scope.alloc_object()?;
    let key_prop = PropertyKey::String(scope.alloc_string("prop")?);
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
    scope.object_set_prototype(child, Some(proto))?;

    let proto_root = scope.heap_mut().add_root(Value::Object(proto))?;
    let child_root = scope.heap_mut().add_root(Value::Object(child))?;
    drop(scope);

    (proto_root, child_root)
  };

  let child = heap
    .get_root(child_root)
    .ok_or(VmError::InvalidHandle)?
    .as_object()
    .unwrap();

  let mut scope = heap.scope();
  let key_prop = PropertyKey::String(scope.alloc_string("prop")?);
  let key_seen = PropertyKey::String(scope.alloc_string("seen")?);
  drop(scope);

  assert!(heap.ordinary_set(
    &mut vm,
    child,
    key_prop,
    Value::Number(99.0),
    Value::Object(child)
  )?);

  assert_eq!(
    heap.object_get_own_data_property_value(child, &key_seen)?,
    Some(Value::Number(99.0))
  );

  heap.remove_root(proto_root);
  heap.remove_root(child_root);
  Ok(())
}

#[test]
fn heap_ordinary_get_and_set_respect_prototype_chain_bounds() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(32 * 1024 * 1024, 32 * 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  // Put the property at the base of a long prototype chain.
  let (base_root, leaf_root, too_deep_root) = {
    let mut scope = heap.scope();
    let base = scope.alloc_object()?;
    let key = PropertyKey::String(scope.alloc_string("x")?);
    scope.define_property(
      base,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Number(123.0),
          writable: true,
        },
      },
    )?;

    let mut prev = base;
    for _ in 0..(MAX_PROTOTYPE_CHAIN - 1) {
      let obj = scope.alloc_object()?;
      unsafe {
        scope
          .heap_mut()
          .object_set_prototype_unchecked(obj, Some(prev))?;
      }
      prev = obj;
    }
    let leaf = prev;

    // One more hop should exceed the cap.
    let too_deep = scope.alloc_object()?;
    unsafe {
      scope
        .heap_mut()
        .object_set_prototype_unchecked(too_deep, Some(leaf))?;
    }

    let base_root = scope.heap_mut().add_root(Value::Object(base))?;
    let leaf_root = scope.heap_mut().add_root(Value::Object(leaf))?;
    let too_deep_root = scope.heap_mut().add_root(Value::Object(too_deep))?;
    drop(scope);
    (base_root, leaf_root, too_deep_root)
  };

  let base = heap
    .get_root(base_root)
    .ok_or(VmError::InvalidHandle)?
    .as_object()
    .unwrap();
  let leaf = heap
    .get_root(leaf_root)
    .ok_or(VmError::InvalidHandle)?
    .as_object()
    .unwrap();
  let too_deep = heap
    .get_root(too_deep_root)
    .ok_or(VmError::InvalidHandle)?
    .as_object()
    .unwrap();

  let mut scope = heap.scope();
  let key = PropertyKey::String(scope.alloc_string("x")?);
  drop(scope);

  assert_eq!(
    heap.ordinary_get(&mut vm, leaf, key, Value::Object(leaf))?,
    Value::Number(123.0)
  );
  assert!(matches!(
    heap.ordinary_get(&mut vm, too_deep, key, Value::Object(too_deep)),
    Err(VmError::PrototypeChainTooDeep)
  ));
  assert!(matches!(
    heap.ordinary_set(
      &mut vm,
      too_deep,
      key,
      Value::Number(999.0),
      Value::Object(too_deep)
    ),
    Err(VmError::PrototypeChainTooDeep)
  ));
  assert!(heap.ordinary_set(
    &mut vm,
    leaf,
    key,
    Value::Number(456.0),
    Value::Object(leaf)
  )?);

  // Ensure we defined an own property on `leaf` and did not mutate the base.
  assert_eq!(
    heap.object_get_own_data_property_value(leaf, &key)?,
    Some(Value::Number(456.0))
  );
  assert_eq!(
    heap.object_get_own_data_property_value(base, &key)?,
    Some(Value::Number(123.0))
  );

  heap.remove_root(base_root);
  heap.remove_root(leaf_root);
  heap.remove_root(too_deep_root);
  Ok(())
}

trait ValueExt {
  fn as_object(self) -> Option<GcObject>;
}

impl ValueExt for Value {
  fn as_object(self) -> Option<GcObject> {
    match self {
      Value::Object(o) => Some(o),
      _ => None,
    }
  }
}
