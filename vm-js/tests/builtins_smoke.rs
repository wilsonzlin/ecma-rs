use vm_js::{GcObject, Heap, HeapLimits, PropertyKey, PropertyKind, Realm, Scope, Value, Vm, VmError, VmOptions};

struct TestRt {
  vm: Vm,
  heap: Heap,
  realm: Realm,
}

impl TestRt {
  fn new(limits: HeapLimits) -> Result<Self, VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(limits);
    let realm = Realm::new(&mut vm, &mut heap)?;
    Ok(Self { vm, heap, realm })
  }
}

impl Drop for TestRt {
  fn drop(&mut self) {
    self.realm.teardown(&mut self.heap);
  }
}

fn get_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  let Some(desc) = scope.heap().get_property(obj, &key)? else {
    return Ok(None);
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(Some(value)),
    PropertyKind::Accessor { .. } => Err(VmError::PropertyNotData),
  }
}

#[test]
fn array_map_join_and_string_conversion_work() -> Result<(), VmError> {
  let mut rt = TestRt::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;
  let intr = *rt.realm.intrinsics();

  let mut scope = rt.heap.scope();

  // new Array(1, 2)
  let array_ctor = Value::Object(intr.array_constructor());
  let array = rt
    .vm
    .construct(&mut scope, array_ctor, &[Value::Number(1.0), Value::Number(2.0)], array_ctor)?;
  let Value::Object(array_obj) = array else {
    return Err(VmError::Unimplemented("Array constructor did not return object"));
  };

  // array.map(String)
  let map = get_data_property(&mut scope, array_obj, "map")?.unwrap();
  let string_ctor = Value::Object(intr.string_constructor());
  let mapped = rt.vm.call(&mut scope, map, array, &[string_ctor])?;
  let Value::Object(mapped_obj) = mapped else {
    return Err(VmError::Unimplemented("Array.prototype.map did not return object"));
  };

  // mapped.join(',')
  let join = get_data_property(&mut scope, mapped_obj, "join")?.unwrap();
  let comma = Value::String(scope.alloc_string(",")?);
  let joined = rt.vm.call(&mut scope, join, mapped, &[comma])?;
  let Value::String(s) = joined else {
    return Err(VmError::Unimplemented("Array.prototype.join did not return string"));
  };
  assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "1,2");
  Ok(())
}

#[test]
fn object_prototype_to_string_works_via_function_call() -> Result<(), VmError> {
  let mut rt = TestRt::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;
  let intr = *rt.realm.intrinsics();

  let mut scope = rt.heap.scope();

  let object_proto = intr.object_prototype();
  let to_string = get_data_property(&mut scope, object_proto, "toString")?.unwrap();

  let function_proto = intr.function_prototype();
  let call = get_data_property(&mut scope, function_proto, "call")?.unwrap();
  let out = rt
    .vm
    .call(&mut scope, call, to_string, &[Value::Number(1.0)])?;
  let Value::String(s) = out else {
    return Err(VmError::Unimplemented("Object.prototype.toString.call did not return string"));
  };
  assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "[object Number]");
  Ok(())
}

#[test]
fn error_construction_sets_message() -> Result<(), VmError> {
  let mut rt = TestRt::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;
  let intr = *rt.realm.intrinsics();

  let mut scope = rt.heap.scope();
  let error_ctor = Value::Object(intr.error());
  let msg = Value::String(scope.alloc_string("x")?);
  let err = rt
    .vm
    .construct(&mut scope, error_ctor, &[msg], error_ctor)?;
  let Value::Object(err_obj) = err else {
    return Err(VmError::Unimplemented("Error constructor did not return object"));
  };
  let message = get_data_property(&mut scope, err_obj, "message")?.unwrap();
  let Value::String(s) = message else {
    return Err(VmError::Unimplemented("Error.message was not a string"));
  };
  assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "x");
  Ok(())
}

#[test]
fn json_stringify_string_does_not_crash() -> Result<(), VmError> {
  let mut rt = TestRt::new(HeapLimits::new(1024 * 1024, 1024 * 1024))?;
  let intr = *rt.realm.intrinsics();

  let json = intr.json();
  let mut scope = rt.heap.scope();
  let stringify = get_data_property(&mut scope, json, "stringify")?.unwrap();
  let x = Value::String(scope.alloc_string("x")?);
  let out = rt.vm.call(&mut scope, stringify, Value::Object(json), &[x])?;
  let Value::String(s) = out else {
    return Err(VmError::Unimplemented("JSON.stringify did not return string"));
  };
  assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "\"x\"");
  Ok(())
}
