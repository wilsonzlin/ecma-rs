use vm_js::{GcObject, Heap, HeapLimits, PropertyKey, Realm, Value, Vm, VmError, VmOptions};

struct TestRealm {
  heap: Heap,
  vm: Vm,
  realm: Realm,
}

impl TestRealm {
  fn new(limits: HeapLimits) -> Result<Self, VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(limits);
    let realm = Realm::new(&mut vm, &mut heap)?;
    Ok(Self { heap, vm, realm })
  }
}

impl Drop for TestRealm {
  fn drop(&mut self) {
    self.realm.teardown(&mut self.heap);
  }
}

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

#[test]
fn error_subclass_intrinsics_exist_and_are_wired_correctly() -> Result<(), VmError> {
  let mut rt = TestRealm::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;

  let intr = *rt.realm.intrinsics();
  let global = rt.realm.global_object();

  let type_error = intr.type_error();
  let type_error_prototype = intr.type_error_prototype();
  let range_error = intr.range_error();
  let range_error_prototype = intr.range_error_prototype();
  let reference_error = intr.reference_error();
  let reference_error_prototype = intr.reference_error_prototype();
  let syntax_error = intr.syntax_error();
  let syntax_error_prototype = intr.syntax_error_prototype();
  let error = intr.error();
  let error_prototype = intr.error_prototype();
  let object_prototype = intr.object_prototype();
  let function_prototype = intr.function_prototype();

  // --- Global bindings ---
  assert_eq!(
    get_own_data_property(&mut rt.heap, global, "TypeError")?,
    Some(Value::Object(type_error))
  );
  assert_eq!(
    get_own_data_property(&mut rt.heap, global, "RangeError")?,
    Some(Value::Object(range_error))
  );
  assert_eq!(
    get_own_data_property(&mut rt.heap, global, "ReferenceError")?,
    Some(Value::Object(reference_error))
  );
  assert_eq!(
    get_own_data_property(&mut rt.heap, global, "SyntaxError")?,
    Some(Value::Object(syntax_error))
  );

  // --- Call / construct behaviour ---
  {
    let mut scope = rt.heap.scope();
    let message = scope.alloc_string("boom")?;
    let result = rt.vm.call(
      &mut scope,
      Value::Object(error),
      Value::Undefined,
      &[Value::String(message)],
    )?;
    let Value::Object(obj) = result else {
      panic!("Error() should return an object");
    };
    scope.push_root(Value::Object(obj))?;

    assert_eq!(scope.heap().object_prototype(obj)?, Some(error_prototype));

    let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
    let name_value = scope
      .heap()
      .object_get_own_data_property_value(obj, &name_key)?
      .expect("Error object should have own 'name' property");
    let Value::String(name_string) = name_value else {
      panic!("Error object 'name' should be a string");
    };
    assert_eq!(scope.heap().get_string(name_string)?.to_utf8_lossy(), "Error");

    let message_key = PropertyKey::from_string(scope.alloc_string("message")?);
    let message_value = scope
      .heap()
      .object_get_own_data_property_value(obj, &message_key)?
      .expect("Error object should have own 'message' property");
    let Value::String(message_string) = message_value else {
      panic!("Error object 'message' should be a string");
    };
    assert_eq!(
      scope.heap().get_string(message_string)?.to_utf8_lossy(),
      "boom"
    );
  }

  {
    let mut scope = rt.heap.scope();
    let message = scope.alloc_string("bad")?;
    let result = rt.vm.construct(
      &mut scope,
      Value::Object(type_error),
      &[Value::String(message)],
      Value::Object(type_error),
    )?;
    let Value::Object(obj) = result else {
      panic!("new TypeError() should return an object");
    };
    scope.push_root(Value::Object(obj))?;

    assert_eq!(
      scope.heap().object_prototype(obj)?,
      Some(type_error_prototype)
    );

    let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
    let name_value = scope
      .heap()
      .object_get_own_data_property_value(obj, &name_key)?
      .expect("TypeError object should have own 'name' property");
    let Value::String(name_string) = name_value else {
      panic!("TypeError object 'name' should be a string");
    };
    assert_eq!(
      scope.heap().get_string(name_string)?.to_utf8_lossy(),
      "TypeError"
    );
  }

  // --- Prototype chain ---
  assert_eq!(
    rt.heap.object_prototype(type_error_prototype)?,
    Some(error_prototype)
  );
  assert_eq!(
    rt.heap.object_prototype(range_error_prototype)?,
    Some(error_prototype)
  );
  assert_eq!(
    rt.heap.object_prototype(reference_error_prototype)?,
    Some(error_prototype)
  );
  assert_eq!(
    rt.heap.object_prototype(syntax_error_prototype)?,
    Some(error_prototype)
  );
  assert_eq!(rt.heap.object_prototype(error_prototype)?, Some(object_prototype));

  // Constructors are function objects (at least by prototype chain).
  assert_eq!(rt.heap.object_prototype(type_error)?, Some(function_prototype));
  assert_eq!(rt.heap.object_prototype(error)?, Some(function_prototype));

  // --- constructor/prototype wiring ---
  assert_eq!(
    get_own_data_property(&mut rt.heap, type_error, "prototype")?,
    Some(Value::Object(type_error_prototype))
  );
  assert_eq!(
    get_own_data_property(&mut rt.heap, type_error_prototype, "constructor")?,
    Some(Value::Object(type_error))
  );

  // --- GC rooting ---
  rt.heap.collect_garbage();

  assert!(rt.heap.is_valid_object(type_error));
  assert!(rt.heap.is_valid_object(type_error_prototype));
  assert!(rt.heap.is_valid_object(error));
  assert!(rt.heap.is_valid_object(error_prototype));

  // Re-check a couple of links after GC to ensure handles remain valid.
  assert_eq!(
    get_own_data_property(&mut rt.heap, global, "TypeError")?,
    Some(Value::Object(type_error))
  );
  assert_eq!(
    rt.heap.object_prototype(type_error_prototype)?,
    Some(error_prototype)
  );

  Ok(())
}
