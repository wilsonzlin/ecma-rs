use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Value, VmError,
  MAX_PROTOTYPE_CHAIN,
};

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
fn prototype_chain_traversal_is_bounded() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(32 * 1024 * 1024, 32 * 1024 * 1024));
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

  Ok(())
}

