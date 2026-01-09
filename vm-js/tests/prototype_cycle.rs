use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Scope, Value, Vm,
  VmError, VmHost, VmHostHooks, VmOptions,
  MAX_PROTOTYPE_CHAIN,
};

fn return_undefined(
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

#[test]
fn set_prototype_rejects_direct_self() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  assert!(matches!(
    scope.heap_mut().object_set_prototype(obj, Some(obj)),
    Err(VmError::PrototypeCycle)
  ));

  Ok(())
}

#[test]
fn set_prototype_rejects_indirect_cycle() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let a = scope.alloc_object()?;
  let b = scope.alloc_object()?;
  let c = scope.alloc_object()?;

  scope.heap_mut().object_set_prototype(a, Some(b))?;
  scope.heap_mut().object_set_prototype(b, Some(c))?;

  assert!(matches!(
    scope.heap_mut().object_set_prototype(c, Some(a)),
    Err(VmError::PrototypeCycle)
  ));

  Ok(())
}

#[test]
fn set_prototype_rejects_indirect_cycle_including_functions() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let call_id = vm.register_native_call(return_undefined)?;
  let mut scope = heap.scope();

  let name1 = scope.alloc_string("f1")?;
  let name2 = scope.alloc_string("f2")?;
  let f1 = scope.alloc_native_function(call_id, None, name1, 0)?;
  let f2 = scope.alloc_native_function(call_id, None, name2, 0)?;

  scope.heap_mut().object_set_prototype(f1, Some(f2))?;
  assert!(matches!(
    scope.heap_mut().object_set_prototype(f2, Some(f1)),
    Err(VmError::PrototypeCycle)
  ));
  Ok(())
}

#[test]
fn set_prototype_rejects_cycle_involving_function_and_object() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let call_id = vm.register_native_call(return_undefined)?;
  let mut scope = heap.scope();

  let func_name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function(call_id, None, func_name, 0)?;
  scope.push_root(Value::Object(func))?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  scope.heap_mut().object_set_prototype(obj, Some(func))?;
  assert!(matches!(
    scope.heap_mut().object_set_prototype(func, Some(obj)),
    Err(VmError::PrototypeCycle)
  ));
  Ok(())
}

#[test]
fn prototype_chain_traversal_is_bounded() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(32 * 1024 * 1024, 32 * 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut scope = heap.scope();

  let key_str = scope.alloc_string("x")?;
  let key = PropertyKey::from_string(key_str);
  let desc = PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value: Value::Number(123.0),
      writable: true,
    },
  };

  // Put the property at the base of a long prototype chain.
  let base = scope.alloc_object()?;
  scope.define_property(base, key, desc)?;

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

  assert!(matches!(scope.heap().get_property(leaf, &key)?, Some(_)));

  // One more hop should exceed the cap.
  let too_deep = scope.alloc_object()?;
  unsafe {
    scope
      .heap_mut()
      .object_set_prototype_unchecked(too_deep, Some(leaf))?;
  }
  assert!(matches!(
    scope.heap().get_property(too_deep, &key),
    Err(VmError::PrototypeChainTooDeep)
  ));

  // The ordinary object internal methods should have the same traversal guards (and must not rely
  // on recursion, which can overflow the stack for large but legal chains).
  assert_eq!(
    scope.ordinary_get(&mut vm, leaf, key, Value::Object(leaf))?,
    Value::Number(123.0)
  );
  assert!(matches!(
    scope.ordinary_get(&mut vm, too_deep, key, Value::Object(too_deep)),
    Err(VmError::PrototypeChainTooDeep)
  ));
  assert!(matches!(
    scope.ordinary_set(
      &mut vm,
      too_deep,
      key,
      Value::Number(999.0),
      Value::Object(too_deep)
    ),
    Err(VmError::PrototypeChainTooDeep)
  ));
  assert!(scope.ordinary_set(
    &mut vm,
    leaf,
    key,
    Value::Number(456.0),
    Value::Object(leaf)
  )?);
  assert_eq!(
    scope.heap().object_get_own_data_property_value(leaf, &key)?,
    Some(Value::Number(456.0))
  );
  assert_eq!(
    scope.heap().object_get_own_data_property_value(base, &key)?,
    Some(Value::Number(123.0))
  );

  // If a cycle is introduced (e.g. via a host bug / unsafe mutation), lookups must not loop.
  let a = scope.alloc_object()?;
  let b = scope.alloc_object()?;
  unsafe {
    scope.heap_mut().object_set_prototype_unchecked(a, Some(b))?;
    scope.heap_mut().object_set_prototype_unchecked(b, Some(a))?;
  }

  let missing_key_str = scope.alloc_string("missing")?;
  let missing_key = PropertyKey::from_string(missing_key_str);
  assert!(matches!(
    scope.heap().get_property(a, &missing_key),
    Err(VmError::PrototypeCycle)
  ));
  assert!(matches!(
    scope.ordinary_get(&mut vm, a, missing_key, Value::Object(a)),
    Err(VmError::PrototypeCycle)
  ));
  assert!(matches!(
    scope.ordinary_set(
      &mut vm,
      a,
      missing_key,
      Value::Number(1.0),
      Value::Object(a)
    ),
    Err(VmError::PrototypeCycle)
  ));

  Ok(())
}
