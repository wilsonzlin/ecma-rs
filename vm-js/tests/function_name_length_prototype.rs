use vm_js::{
  set_function_name, Heap, HeapLimits, NativeConstructId, NativeFunctionId, PropertyKey,
  PropertyKind, Realm, Value, Vm, VmError, VmOptions,
};

#[test]
fn native_function_allocation_defines_name_and_length_properties() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let name = scope.alloc_string("foo")?;
  let func = scope.alloc_native_function(NativeFunctionId(0), None, name, 2)?;

  // F.name
  let key = PropertyKey::from_string(scope.alloc_string("name")?);
  let desc = scope
    .heap()
    .get_own_property(func, key)?
    .expect("function should have an own `name` property");

  assert!(!desc.enumerable);
  assert!(desc.configurable);
  let PropertyKind::Data { value, writable } = desc.kind else {
    panic!("name should be a data property");
  };
  assert!(!writable);
  let Value::String(s) = value else {
    panic!("name value should be a string");
  };
  assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "foo");

  // F.length
  let key = PropertyKey::from_string(scope.alloc_string("length")?);
  let desc = scope
    .heap()
    .get_own_property(func, key)?
    .expect("function should have an own `length` property");

  assert!(!desc.enumerable);
  assert!(desc.configurable);
  let PropertyKind::Data { value, writable } = desc.kind else {
    panic!("length should be a data property");
  };
  assert!(!writable);
  assert_eq!(value, Value::Number(2.0));

  Ok(())
}

#[test]
fn set_function_name_formats_symbol_and_prefix() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let init_name = scope.alloc_string("init")?;
  let func = scope.alloc_native_function(NativeFunctionId(0), None, init_name, 0)?;
  let sym = scope.alloc_symbol(Some("sym"))?;
  set_function_name(&mut scope, func, PropertyKey::from_symbol(sym), Some("get"))?;

  let key = PropertyKey::from_string(scope.alloc_string("name")?);
  let desc = scope.heap().get_own_property(func, key)?.unwrap();
  let PropertyKind::Data { value, .. } = desc.kind else {
    panic!("name should be a data property");
  };
  let Value::String(s) = value else {
    panic!("name value should be a string");
  };
  assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "get [sym]");

  Ok(())
}

#[test]
fn constructible_native_function_gets_prototype_and_constructor_properties() -> Result<(), VmError>
{
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let ctor_name = scope.alloc_string("Ctor")?;
  let func = scope.alloc_native_function(
    NativeFunctionId(0),
    Some(NativeConstructId(0)),
    ctor_name,
    0,
  )?;

  // F.prototype
  let prototype_key = PropertyKey::from_string(scope.alloc_string("prototype")?);
  let desc = scope
    .heap()
    .get_own_property(func, prototype_key)?
    .expect("constructor should have a `prototype` property");

  assert!(!desc.enumerable);
  assert!(!desc.configurable);
  let PropertyKind::Data { value, writable } = desc.kind else {
    panic!("prototype should be a data property");
  };
  assert!(writable);
  let Value::Object(prototype) = value else {
    panic!("prototype value should be an object");
  };

  // F.prototype.constructor
  let constructor_key = PropertyKey::from_string(scope.alloc_string("constructor")?);
  let desc = scope
    .heap()
    .get_own_property(prototype, constructor_key)?
    .expect("prototype should have a `constructor` property");

  assert!(!desc.enumerable);
  assert!(desc.configurable);
  let PropertyKind::Data { value, writable } = desc.kind else {
    panic!("constructor should be a data property");
  };
  assert!(writable);
  assert_eq!(value, Value::Object(func));

  Ok(())
}

#[test]
fn intrinsic_error_constructor_prototype_property_is_writable() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let error = realm.intrinsics().error();
  let error_prototype = realm.intrinsics().error_prototype();

  {
    let mut scope = heap.scope();

    // %Error%.prototype
    let prototype_key = PropertyKey::from_string(scope.alloc_string("prototype")?);
    let desc = scope
      .heap()
      .get_own_property(error, prototype_key)?
      .expect("%Error% should have a `prototype` own property");
    assert!(!desc.enumerable);
    assert!(!desc.configurable);
    let PropertyKind::Data { value, writable } = desc.kind else {
      panic!("prototype should be a data property");
    };
    assert!(writable);
    assert_eq!(value, Value::Object(error_prototype));

    // %Error.prototype%.constructor
    let constructor_key = PropertyKey::from_string(scope.alloc_string("constructor")?);
    let desc = scope
      .heap()
      .get_own_property(error_prototype, constructor_key)?
      .expect("%Error.prototype% should have a `constructor` own property");
    assert!(!desc.enumerable);
    assert!(desc.configurable);
    let PropertyKind::Data { value, writable } = desc.kind else {
      panic!("constructor should be a data property");
    };
    assert!(writable);
    assert_eq!(value, Value::Object(error));
  }

  realm.teardown(&mut heap);
  Ok(())
}
