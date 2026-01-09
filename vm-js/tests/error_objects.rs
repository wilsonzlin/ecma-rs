use vm_js::{
  new_type_error, Heap, HeapLimits, JsRuntime, PropertyKey, Realm, Value, Vm, VmError, VmOptions,
};

struct TestRealm {
  _vm: Vm,
  heap: Heap,
  realm: Realm,
}

impl TestRealm {
  fn new(limits: HeapLimits) -> Result<Self, VmError> {
    let mut heap = Heap::new(limits);
    let mut vm = Vm::new(VmOptions::default());
    let realm = Realm::new(&mut vm, &mut heap)?;
    Ok(Self {
      _vm: vm,
      heap,
      realm,
    })
  }
}

impl Drop for TestRealm {
  fn drop(&mut self) {
    self.realm.teardown(&mut self.heap);
  }
}

#[test]
fn type_error_instance_has_correct_prototype() -> Result<(), VmError> {
  let mut rt = TestRealm::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;

  let mut scope = rt.heap.scope();
  let value = new_type_error(&mut scope, *rt.realm.intrinsics(), "boom")?;
  let Value::Object(obj) = value else {
    panic!("expected error object, got {value:?}");
  };

  // Root the value while allocating property keys below.
  scope.push_root(value)?;

  assert_eq!(
    scope.heap().object_prototype(obj)?,
    Some(rt.realm.intrinsics().type_error_prototype())
  );

  let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
  let message_key = PropertyKey::from_string(scope.alloc_string("message")?);

  let name = scope
    .heap()
    .object_get_own_data_property_value(obj, &name_key)?
    .expect("expected own name property");
  let message = scope
    .heap()
    .object_get_own_data_property_value(obj, &message_key)?
    .expect("expected own message property");

  assert!(matches!(name, Value::String(_)));
  assert!(matches!(message, Value::String(_)));
  Ok(())
}

#[test]
fn thrown_type_error_is_catchable_from_script() {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut rt = JsRuntime::new(vm, heap).unwrap();

  let caught = rt
    .exec_script(r#"try { const x = 1; x = 2; } catch(e) { e }"#)
    .unwrap();

  let Value::Object(obj) = caught else {
    panic!("expected caught object, got {caught:?}");
  };

  let type_error_prototype = rt.realm().intrinsics().type_error_prototype();

  let mut scope = rt.heap_mut().scope();
  scope.push_root(caught).unwrap();

  assert_eq!(scope.heap().object_prototype(obj).unwrap(), Some(type_error_prototype));

  let name_key = PropertyKey::from_string(scope.alloc_string("name").unwrap());
  let message_key = PropertyKey::from_string(scope.alloc_string("message").unwrap());

  let name = scope
    .heap()
    .object_get_own_data_property_value(obj, &name_key)
    .unwrap()
    .expect("expected own name property");
  let message = scope
    .heap()
    .object_get_own_data_property_value(obj, &message_key)
    .unwrap()
    .expect("expected own message property");

  assert!(matches!(name, Value::String(_)));
  assert!(matches!(message, Value::String(_)));
}
