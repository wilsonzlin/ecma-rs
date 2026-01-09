use vm_js::{
  new_syntax_error_object, new_type_error_object, GcObject, Heap, HeapLimits, PropertyKey,
  PropertyKind, Realm, Scope, Value, Vm, VmError, VmOptions,
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
    Ok(Self { _vm: vm, heap, realm })
  }
}

impl Drop for TestRealm {
  fn drop(&mut self) {
    self.realm.teardown(&mut self.heap);
  }
}

fn assert_own_non_enumerable_string_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: &str,
  expected: &str,
) -> Result<(), VmError> {
  let key_s = scope.alloc_string(key)?;
  let key = PropertyKey::from_string(key_s);
  let desc = scope
    .heap()
    .object_get_own_property(obj, &key)?
    .unwrap_or_else(|| panic!("missing own property {key:?}"));

  assert!(!desc.enumerable, "expected {key:?} to be non-enumerable");
  assert!(desc.configurable, "expected {key:?} to be configurable");

  let PropertyKind::Data { value, writable } = desc.kind else {
    panic!("expected {key:?} to be a data property");
  };
  assert!(writable, "expected {key:?} to be writable");

  let Value::String(s) = value else {
    panic!("expected {key:?} value to be a string");
  };
  let actual = scope.heap().get_string(s)?.to_utf8_lossy();
  assert_eq!(actual, expected);
  Ok(())
}

#[test]
fn new_type_error_creates_error_instance_with_correct_proto_and_properties() -> Result<(), VmError> {
  let mut rt = TestRealm::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;

  {
    let mut scope = rt.heap.scope();
    let err = new_type_error_object(&mut scope, rt.realm.intrinsics(), "bad dynamic import")?;
    let Value::Object(err) = err else {
      panic!("new_type_error should return an object");
    };

    // Root the returned object before any further allocations.
    scope.push_root(Value::Object(err))?;

    assert_eq!(
      scope.heap().object_prototype(err)?,
      Some(rt.realm.intrinsics().type_error_prototype())
    );

    assert_own_non_enumerable_string_data_property(&mut scope, err, "name", "TypeError")?;
    assert_own_non_enumerable_string_data_property(
      &mut scope,
      err,
      "message",
      "bad dynamic import",
    )?;
  }

  Ok(())
}

#[test]
fn new_syntax_error_creates_error_instance_with_correct_proto_and_properties() -> Result<(), VmError> {
  let mut rt = TestRealm::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;

  {
    let mut scope = rt.heap.scope();
    let err = new_syntax_error_object(
      &mut scope,
      rt.realm.intrinsics(),
      "import attributes not supported",
    )?;
    let Value::Object(err) = err else {
      panic!("new_syntax_error should return an object");
    };

    // Root the returned object before any further allocations.
    scope.push_root(Value::Object(err))?;

    assert_eq!(
      scope.heap().object_prototype(err)?,
      Some(rt.realm.intrinsics().syntax_error_prototype())
    );

    assert_own_non_enumerable_string_data_property(&mut scope, err, "name", "SyntaxError")?;
    assert_own_non_enumerable_string_data_property(
      &mut scope,
      err,
      "message",
      "import attributes not supported",
    )?;
  }

  Ok(())
}
