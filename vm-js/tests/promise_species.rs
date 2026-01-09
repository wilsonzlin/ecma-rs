use vm_js::{Heap, HeapLimits, PropertyKey, PropertyKind, Realm, Value, Vm, VmError, VmOptions};

#[test]
fn promise_species_getter_returns_this() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let promise_ctor = realm.intrinsics().promise();
  let species_key = PropertyKey::from_symbol(realm.well_known_symbols().species);

  let desc = heap
    .object_get_own_property(promise_ctor, &species_key)?
    .expect("Promise[@@species] should be an own property");
  assert!(!desc.enumerable);
  assert!(desc.configurable);

  let (get, set) = match desc.kind {
    PropertyKind::Accessor { get, set } => (get, set),
    _ => panic!("Promise[@@species] should be an accessor property"),
  };
  assert_eq!(set, Value::Undefined);

  {
    let mut scope = heap.scope();

    // The getter is specified as `return this`.
    let result = vm.call(&mut scope, get, Value::Object(promise_ctor), &[])?;
    assert_eq!(result, Value::Object(promise_ctor));

    // It should return the exact receiver even when called with a different `this` value.
    let other_ctor = scope.alloc_object()?;
    scope
      .heap_mut()
      .object_set_prototype(other_ctor, Some(realm.intrinsics().function_prototype()))?;

    let result = vm.call(&mut scope, get, Value::Object(other_ctor), &[])?;
    assert_eq!(result, Value::Object(other_ctor));
  }

  realm.teardown(&mut heap);
  Ok(())
}
