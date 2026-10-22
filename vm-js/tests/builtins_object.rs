use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Realm, Scope, Value,
  Vm, VmError, VmHost, VmHostHooks, VmOptions,
};

struct TestRealm {
  vm: Vm,
  heap: Heap,
  realm: Realm,
}

impl TestRealm {
  fn new() -> Result<Self, VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let realm = Realm::new(&mut vm, &mut heap)?;
    Ok(Self { vm, heap, realm })
  }
}

impl Drop for TestRealm {
  fn drop(&mut self) {
    self.realm.teardown(&mut self.heap);
  }
}

fn get_own_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj))?;
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  scope.heap().object_get_own_data_property_value(obj, &key)
}

fn define_enumerable_data_property(
  scope: &mut Scope<'_>,
  obj: GcObject,
  name: &str,
  value: Value,
) -> Result<(), VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj))?;
  scope.push_root(value)?;
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  let desc = PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  };
  scope.define_property(obj, key, desc)
}

fn return_two_native(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(2.0))
}

#[test]
fn object_constructor_is_callable() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;

  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  // Global binding exists.
  assert_eq!(
    get_own_data_property(&mut scope, rt.realm.global_object(), "Object")?,
    Some(Value::Object(object))
  );

  // `typeof Object === "function"` (approximated by "call doesn't error").
  let _ = rt
    .vm
    .call_without_host(&mut scope, Value::Object(object), Value::Undefined, &[])?;

  Ok(())
}

#[test]
fn object_define_property_defines_value() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let define_property = get_own_data_property(&mut scope, object, "defineProperty")?
    .expect("Object.defineProperty should exist");
  let Value::Object(define_property) = define_property else {
    panic!("Object.defineProperty should be a function object");
  };

  let o = scope.alloc_object()?;
  scope.push_root(Value::Object(o))?;

  // { value: 1 }
  let desc = scope.alloc_object()?;
  scope.push_root(Value::Object(desc))?;
  define_enumerable_data_property(&mut scope, desc, "value", Value::Number(1.0))?;

  let x = scope.alloc_string("x")?;
  let args = [Value::Object(o), Value::String(x), Value::Object(desc)];

  let _ = rt.vm.call_without_host(
    &mut scope,
    Value::Object(define_property),
    Value::Object(object),
    &args,
  )?;

  let x_key = PropertyKey::from_string(x);
  assert_eq!(
    scope.heap().object_get_own_data_property_value(o, &x_key)?,
    Some(Value::Number(1.0))
  );

  Ok(())
}

#[test]
fn object_define_properties_defines_data_and_accessor() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let define_properties = get_own_data_property(&mut scope, object, "defineProperties")?
    .expect("Object.defineProperties should exist");
  let Value::Object(define_properties) = define_properties else {
    panic!("Object.defineProperties should be a function object");
  };

  let o = scope.alloc_object()?;
  scope.push_root(Value::Object(o))?;

  let props = scope.alloc_object()?;
  scope.push_root(Value::Object(props))?;

  // x: { value: 1 }
  let x_desc = scope.alloc_object()?;
  scope.push_root(Value::Object(x_desc))?;
  define_enumerable_data_property(&mut scope, x_desc, "value", Value::Number(1.0))?;
  define_enumerable_data_property(&mut scope, props, "x", Value::Object(x_desc))?;

  // y: { get: function() { return 2; } }
  let y_desc = scope.alloc_object()?;
  scope.push_root(Value::Object(y_desc))?;
  let getter_id = rt.vm.register_native_call(return_two_native)?;
  let getter_name = scope.alloc_string("")?;
  let getter = scope.alloc_native_function(getter_id, None, getter_name, 0)?;
  scope.push_root(Value::Object(getter))?;
  define_enumerable_data_property(&mut scope, y_desc, "get", Value::Object(getter))?;
  define_enumerable_data_property(&mut scope, props, "y", Value::Object(y_desc))?;

  let args = [Value::Object(o), Value::Object(props)];
  let _ = rt.vm.call_without_host(
    &mut scope,
    Value::Object(define_properties),
    Value::Object(object),
    &args,
  )?;

  let x = scope.alloc_string("x")?;
  let x_key = PropertyKey::from_string(x);
  assert_eq!(
    scope.heap().object_get_own_data_property_value(o, &x_key)?,
    Some(Value::Number(1.0))
  );

  let y = scope.alloc_string("y")?;
  let y_val = rt.vm.get(&mut scope, o, PropertyKey::from_string(y))?;
  assert_eq!(y_val, Value::Number(2.0));

  Ok(())
}

#[test]
fn object_create_with_properties_object() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let create = get_own_data_property(&mut scope, object, "create")?.expect("Object.create exists");
  let Value::Object(create) = create else {
    panic!("Object.create should be a function object");
  };

  let props = scope.alloc_object()?;
  scope.push_root(Value::Object(props))?;
  let a_desc = scope.alloc_object()?;
  scope.push_root(Value::Object(a_desc))?;
  define_enumerable_data_property(&mut scope, a_desc, "value", Value::Number(7.0))?;
  define_enumerable_data_property(&mut scope, a_desc, "writable", Value::Bool(true))?;
  define_enumerable_data_property(&mut scope, a_desc, "enumerable", Value::Bool(true))?;
  define_enumerable_data_property(&mut scope, a_desc, "configurable", Value::Bool(true))?;
  define_enumerable_data_property(&mut scope, props, "a", Value::Object(a_desc))?;

  let args = [Value::Null, Value::Object(props)];
  let o = rt.vm.call_without_host(
    &mut scope,
    Value::Object(create),
    Value::Object(object),
    &args,
  )?;
  let Value::Object(o) = o else {
    panic!("Object.create should return an object");
  };

  let a = scope.alloc_string("a")?;
  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(o, &PropertyKey::from_string(a))?,
    Some(Value::Number(7.0))
  );

  Ok(())
}

#[test]
fn object_create_sets_prototype() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let create = get_own_data_property(&mut scope, object, "create")?.expect("Object.create exists");
  let Value::Object(create) = create else {
    panic!("Object.create should be a function object");
  };

  // { y: 2 }
  let p = scope.alloc_object()?;
  scope.push_root(Value::Object(p))?;
  define_enumerable_data_property(&mut scope, p, "y", Value::Number(2.0))?;

  let y_key = PropertyKey::from_string(scope.alloc_string("y")?);

  let args = [Value::Object(p)];
  let o = rt.vm.call_without_host(
    &mut scope,
    Value::Object(create),
    Value::Object(object),
    &args,
  )?;
  let Value::Object(o) = o else {
    panic!("Object.create should return an object");
  };
  let desc = scope
    .heap()
    .get_property(o, &y_key)?
    .expect("property should be found via prototype");
  let PropertyKind::Data { value, .. } = desc.kind else {
    panic!("expected data property");
  };
  assert_eq!(value, Value::Number(2.0));

  Ok(())
}

#[test]
fn object_keys_returns_enumerable_string_keys() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let keys = get_own_data_property(&mut scope, object, "keys")?.expect("Object.keys exists");
  let Value::Object(keys) = keys else {
    panic!("Object.keys should be a function object");
  };

  // { a: 1, b: 2 }
  let o = scope.alloc_object()?;
  scope.push_root(Value::Object(o))?;
  define_enumerable_data_property(&mut scope, o, "a", Value::Number(1.0))?;
  define_enumerable_data_property(&mut scope, o, "b", Value::Number(2.0))?;

  let args = [Value::Object(o)];
  let result = rt.vm.call_without_host(
    &mut scope,
    Value::Object(keys),
    Value::Object(object),
    &args,
  )?;
  let Value::Object(arr) = result else {
    panic!("Object.keys should return an object");
  };

  let length = get_own_data_property(&mut scope, arr, "length")?.expect("length exists");
  assert_eq!(length, Value::Number(2.0));

  Ok(())
}

#[test]
fn object_assign_copies_enumerable_properties_and_invokes_getters() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let assign = get_own_data_property(&mut scope, object, "assign")?.expect("Object.assign exists");
  let Value::Object(assign) = assign else {
    panic!("Object.assign should be a function object");
  };

  let target = scope.alloc_object()?;
  scope.push_root(Value::Object(target))?;
  let source = scope.alloc_object()?;
  scope.push_root(Value::Object(source))?;

  // Enumerable data property.
  define_enumerable_data_property(&mut scope, source, "a", Value::Number(1.0))?;

  // Enumerable accessor property whose getter returns 2.
  let getter_id = rt.vm.register_native_call(return_two_native)?;
  let getter_name = scope.alloc_string("")?;
  let getter = scope.alloc_native_function(getter_id, None, getter_name, 0)?;
  scope.push_root(Value::Object(getter))?;

  let key_b = PropertyKey::from_string(scope.alloc_string("b")?);
  scope.define_property(
    source,
    key_b,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Accessor {
        get: Value::Object(getter),
        set: Value::Undefined,
      },
    },
  )?;

  let args = [Value::Object(target), Value::Object(source)];
  let out = rt.vm.call_without_host(
    &mut scope,
    Value::Object(assign),
    Value::Object(object),
    &args,
  )?;
  assert_eq!(out, Value::Object(target));

  assert_eq!(
    get_own_data_property(&mut scope, target, "a")?,
    Some(Value::Number(1.0))
  );
  assert_eq!(
    get_own_data_property(&mut scope, target, "b")?,
    Some(Value::Number(2.0))
  );

  Ok(())
}

#[test]
fn object_assign_throws_when_setting_non_writable_target_property() -> Result<(), VmError> {
  let mut rt = TestRealm::new()?;
  let object = rt.realm.intrinsics().object_constructor();

  let mut scope = rt.heap.scope();

  let assign = get_own_data_property(&mut scope, object, "assign")?.expect("Object.assign exists");
  let Value::Object(assign) = assign else {
    panic!("Object.assign should be a function object");
  };

  let target = scope.alloc_object()?;
  scope.push_root(Value::Object(target))?;
  let source = scope.alloc_object()?;
  scope.push_root(Value::Object(source))?;

  // target.x is non-writable.
  let key_x = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    target,
    key_x,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(1.0),
        writable: false,
      },
    },
  )?;

  // source.x = 2 (enumerable).
  define_enumerable_data_property(&mut scope, source, "x", Value::Number(2.0))?;

  let args = [Value::Object(target), Value::Object(source)];
  let err = rt
    .vm
    .call_without_host(
      &mut scope,
      Value::Object(assign),
      Value::Object(object),
      &args,
    )
    .unwrap_err();
  assert!(matches!(err, VmError::TypeError(_)));

  Ok(())
}
