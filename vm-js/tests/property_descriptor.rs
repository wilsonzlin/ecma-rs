use vm_js::{
  GcObject, Heap, HeapLimits, PropertyDescriptor, PropertyDescriptorPatch, PropertyKey,
  PropertyKind, Scope, Value, Vm, VmError, VmHostHooks, VmOptions,
};

fn return_undefined(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

#[test]
fn property_descriptor_patch_validation_rejects_mixing_data_and_accessor_fields() {
  // value + get
  let patch = PropertyDescriptorPatch {
    value: Some(Value::Undefined),
    get: Some(Value::Undefined),
    ..Default::default()
  };
  assert!(matches!(
    patch.validate(),
    Err(VmError::InvalidPropertyDescriptorPatch)
  ));

  // writable + set
  let patch = PropertyDescriptorPatch {
    writable: Some(true),
    set: Some(Value::Undefined),
    ..Default::default()
  };
  assert!(matches!(
    patch.validate(),
    Err(VmError::InvalidPropertyDescriptorPatch)
  ));
}

#[test]
fn property_descriptor_patch_validation_accepts_data_or_accessor_only() {
  let patch = PropertyDescriptorPatch {
    value: Some(Value::Null),
    writable: Some(false),
    ..Default::default()
  };
  assert!(patch.validate().is_ok());

  let patch = PropertyDescriptorPatch {
    get: Some(Value::Undefined),
    set: Some(Value::Undefined),
    ..Default::default()
  };
  assert!(patch.validate().is_ok());

  let patch = PropertyDescriptorPatch {
    enumerable: Some(true),
    configurable: Some(false),
    ..Default::default()
  };
  assert!(patch.validate().is_ok());
}

#[test]
fn object_property_tracing_keeps_referenced_objects_alive() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let child;
  let dead;
  let owner;
  {
    let mut scope = heap.scope();

    // Child object referenced through a property descriptor.
    child = scope.alloc_object()?;

    // An unrelated object that should be collected.
    dead = scope.alloc_object()?;

    // Property key that should be kept alive by object tracing.
    let key_str = scope.alloc_string("x")?;
    let key = PropertyKey::from_string(key_str);

    let desc = PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Object(child),
        writable: true,
      },
    };

    owner = scope.alloc_object_with_properties(None, &[(key, desc)])?;
    scope.push_root(Value::Object(owner))?;

    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_object(owner));
    assert!(scope.heap().is_valid_string(key_str));
    assert!(
      scope.heap().is_valid_object(child),
      "child should survive via property"
    );
    assert!(!scope.heap().is_valid_object(dead), "dead should be collected");
  }

  Ok(())
}

#[test]
fn property_key_equality_uses_string_code_units_or_symbol_identity() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let mut scope = heap.scope();

  let s1 = scope.alloc_string("abc")?;
  let s2 = scope.alloc_string("abc")?;

  let k1 = PropertyKey::from_string(s1);
  let k2 = PropertyKey::from_string(s2);
  assert!(scope.heap().property_key_eq(&k1, &k2));

  let sym1 = scope.alloc_symbol(None)?;
  let sym2 = scope.alloc_symbol(None)?;
  let k1 = PropertyKey::from_symbol(sym1);
  let k2 = PropertyKey::from_symbol(sym2);
  assert!(!scope.heap().property_key_eq(&k1, &k2));
  assert!(scope.heap().property_key_eq(&k1, &k1));

  Ok(())
}

#[test]
fn define_property_works_on_native_function_objects() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let call_id = vm.register_native_call(return_undefined)?;
  let mut scope = heap.scope();

  let name = scope.alloc_string("f")?;
  let func = scope.alloc_native_function(call_id, None, name, 0)?;
  scope.push_root(Value::Object(func))?;

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
  scope.define_property(func, key, desc)?;

  // Ensure the function traces its property table (and the property key) across GC.
  scope.heap_mut().collect_garbage();
  assert!(scope.heap().is_valid_string(key_str));

  let got = scope
    .heap()
    .object_get_own_property(func, &key)?
    .expect("property should exist on function object");
  assert!(got.enumerable);
  assert!(got.configurable);
  match got.kind {
    PropertyKind::Data { value, writable } => {
      assert!(writable);
      assert!(matches!(value, Value::Number(n) if n == 123.0));
    }
    PropertyKind::Accessor { .. } => panic!("expected data descriptor"),
  }

  Ok(())
}
