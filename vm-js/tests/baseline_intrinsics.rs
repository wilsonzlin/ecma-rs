use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Realm, Scope, Value,
  Vm, VmError, VmOptions,
};

fn get_own_data_property(
  heap: &mut Heap,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let mut scope = heap.scope();
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  scope
    .heap()
    .object_get_own_data_property_value(obj, &key)
}

fn define_enumerable_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  value: Value,
) -> Result<(), VmError> {
  scope.define_property(
    obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value,
        writable: true,
      },
    },
  )
}

#[test]
fn realm_installs_baseline_globals_and_intrinsic_graph() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let global = realm.global_object();
  let intr = *realm.intrinsics();

  // --- Global bindings ---
  assert_eq!(
    get_own_data_property(&mut heap, global, "globalThis")?,
    Some(Value::Object(global))
  );
  assert_eq!(
    get_own_data_property(&mut heap, global, "Object")?,
    Some(Value::Object(intr.object_constructor()))
  );
  assert_eq!(
    get_own_data_property(&mut heap, global, "Function")?,
    Some(Value::Object(intr.function_constructor()))
  );
  assert_eq!(
    get_own_data_property(&mut heap, global, "Array")?,
    Some(Value::Object(intr.array_constructor()))
  );

  // --- Prototype wiring ---
  assert_eq!(heap.object_prototype(intr.object_prototype())?, None);
  assert_eq!(
    heap.object_prototype(intr.function_prototype())?,
    Some(intr.object_prototype())
  );
  assert_eq!(
    heap.object_prototype(intr.array_prototype())?,
    Some(intr.object_prototype())
  );

  assert_eq!(
    heap.object_prototype(intr.object_constructor())?,
    Some(intr.function_prototype())
  );
  assert_eq!(
    heap.object_prototype(intr.function_constructor())?,
    Some(intr.function_prototype())
  );
  assert_eq!(
    heap.object_prototype(intr.array_constructor())?,
    Some(intr.function_prototype())
  );

  // `constructor.prototype` and `prototype.constructor` links.
  assert_eq!(
    get_own_data_property(&mut heap, intr.object_constructor(), "prototype")?,
    Some(Value::Object(intr.object_prototype()))
  );
  assert_eq!(
    get_own_data_property(&mut heap, intr.object_prototype(), "constructor")?,
    Some(Value::Object(intr.object_constructor()))
  );

  assert_eq!(
    get_own_data_property(&mut heap, intr.function_constructor(), "prototype")?,
    Some(Value::Object(intr.function_prototype()))
  );
  assert_eq!(
    get_own_data_property(&mut heap, intr.function_prototype(), "constructor")?,
    Some(Value::Object(intr.function_constructor()))
  );

  assert_eq!(
    get_own_data_property(&mut heap, intr.array_constructor(), "prototype")?,
    Some(Value::Object(intr.array_prototype()))
  );
  assert_eq!(
    get_own_data_property(&mut heap, intr.array_prototype(), "constructor")?,
    Some(Value::Object(intr.array_constructor()))
  );

  // Avoid leaking persistent roots (and tripping the Realm drop assertion).
  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn object_and_array_constructors_are_callable_and_constructable() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut realm = Realm::new(&mut vm, &mut heap)?;
  let intr = *realm.intrinsics();

  {
    let mut scope = heap.scope();

    // `%Object%` call
    let obj_value = vm.call_without_host(
      &mut scope,
      Value::Object(intr.object_constructor()),
      Value::Undefined,
      &[],
    )?;
    let Value::Object(obj) = obj_value else {
      panic!("Object() should return an object");
    };
    scope.push_root(Value::Object(obj))?;
    assert_eq!(scope.heap().object_prototype(obj)?, Some(intr.object_prototype()));

    // `%Object%` construct
    let obj_value = vm.construct_without_host(
      &mut scope,
      Value::Object(intr.object_constructor()),
      &[],
      Value::Object(intr.object_constructor()),
    )?;
    let Value::Object(obj2) = obj_value else {
      panic!("new Object() should return an object");
    };
    scope.push_root(Value::Object(obj2))?;
    assert_eq!(scope.heap().object_prototype(obj2)?, Some(intr.object_prototype()));

    // `%Object%` called with an object returns the same object.
    let arg_obj = scope.alloc_object()?;
    scope.push_root(Value::Object(arg_obj))?;
    let out = vm.call_without_host(
      &mut scope,
      Value::Object(intr.object_constructor()),
      Value::Undefined,
      &[Value::Object(arg_obj)],
    )?;
    assert_eq!(out, Value::Object(arg_obj));

    // `%Object%` called with a primitive returns a boxed wrapper object.
    let out = vm.call_without_host(
      &mut scope,
      Value::Object(intr.object_constructor()),
      Value::Undefined,
      &[Value::Number(1.0)],
    )?;
    let Value::Object(boxed) = out else {
      panic!("Object(1) should return an object wrapper");
    };
    scope.push_root(Value::Object(boxed))?;
    assert_eq!(
      scope.heap().object_prototype(boxed)?,
      Some(intr.number_prototype())
    );

    // `%Array%` call
    let arr_value = vm.call_without_host(
      &mut scope,
      Value::Object(intr.array_constructor()),
      Value::Undefined,
      &[],
    )?;
    let Value::Object(arr) = arr_value else {
      panic!("Array() should return an object");
    };
    scope.push_root(Value::Object(arr))?;
    assert_eq!(scope.heap().object_prototype(arr)?, Some(intr.array_prototype()));

    // `%Array%` construct
    let arr_value = vm.construct_without_host(
      &mut scope,
      Value::Object(intr.array_constructor()),
      &[],
      Value::Object(intr.array_constructor()),
    )?;
    let Value::Object(arr2) = arr_value else {
      panic!("new Array() should return an object");
    };
    scope.push_root(Value::Object(arr2))?;
    assert_eq!(scope.heap().object_prototype(arr2)?, Some(intr.array_prototype()));
  }

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn array_get_and_own_property_keys_are_sufficient_for_webidl_sequences() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut realm = Realm::new(&mut vm, &mut heap)?;
  let intr = *realm.intrinsics();

  {
    let mut scope = heap.scope();

    // Create an array of length 3 (minimal `Array(len)` support).
    let arr_value = vm.call_without_host(
      &mut scope,
      Value::Object(intr.array_constructor()),
      Value::Undefined,
      &[Value::Number(3.0)],
    )?;
    let Value::Object(arr) = arr_value else {
      panic!("Array(len) should return an object");
    };
    scope.push_root(Value::Object(arr))?;

    // Define elements 0..2 in the way WebIDL `sequence_to_js_array` expects (CreateDataPropertyOrThrow).
    for (i, v) in [10.0, 20.0, 30.0].into_iter().enumerate() {
      let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
      define_enumerable_data_property(&mut scope, arr, key, Value::Number(v))?;
    }

    // OwnPropertyKeys: indices in ascending order, then "length".
    let keys = scope.heap().own_property_keys(arr)?;
    let keys_as_utf8: Vec<String> = keys
      .iter()
      .map(|k| match k {
        PropertyKey::String(s) => scope.heap().get_string(*s).unwrap().to_utf8_lossy(),
        PropertyKey::Symbol(_) => "<symbol>".to_string(),
      })
      .collect();

    let expected_keys: Vec<String> = ["0", "1", "2", "length"]
      .into_iter()
      .map(|s| s.to_string())
      .collect();
    assert_eq!(keys_as_utf8, expected_keys);

    // Get element values + length.
    for (i, expected) in [10.0, 20.0, 30.0].into_iter().enumerate() {
      let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
      assert_eq!(scope.heap().get(arr, &key)?, Value::Number(expected));
    }
    let length_key = PropertyKey::from_string(scope.alloc_string("length")?);
    assert_eq!(scope.heap().get(arr, &length_key)?, Value::Number(3.0));
  }

  realm.teardown(&mut heap);
  Ok(())
}
