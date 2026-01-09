use vm_js::{Heap, HeapLimits, PropertyDescriptorPatch, PropertyKey, Value, Vm, VmError, VmOptions};

#[test]
fn define_own_property_respects_extensible() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;

  let k_a = PropertyKey::String(scope.alloc_string("a")?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_a,
    PropertyDescriptorPatch {
      value: Some(Value::Number(1.0)),
      writable: Some(true),
      enumerable: Some(true),
      configurable: Some(true),
      ..Default::default()
    }
  )?);

  scope.object_prevent_extensions(obj)?;

  let k_b = PropertyKey::String(scope.alloc_string("b")?);
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_b,
    PropertyDescriptorPatch {
      value: Some(Value::Number(2.0)),
      ..Default::default()
    }
  )?);

  // Defining an existing property is still allowed on non-extensible objects.
  assert!(scope.ordinary_define_own_property(
    obj,
    k_a,
    PropertyDescriptorPatch {
      value: Some(Value::Number(3.0)),
      ..Default::default()
    }
  )?);

  Ok(())
}

#[test]
fn non_configurable_invariants_and_same_value() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  let k_x = PropertyKey::String(scope.alloc_string("x")?);

  assert!(scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      value: Some(Value::Number(1.0)),
      writable: Some(true),
      enumerable: Some(true),
      configurable: Some(false),
      ..Default::default()
    }
  )?);

  // Non-configurable: cannot flip configurable/enumerable.
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      configurable: Some(true),
      ..Default::default()
    }
  )?);
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      enumerable: Some(false),
      ..Default::default()
    }
  )?);

  // Writable + non-configurable: value changes are still allowed.
  assert!(scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      value: Some(Value::Number(2.0)),
      ..Default::default()
    }
  )?);

  // Transition to non-writable is allowed.
  assert!(scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      writable: Some(false),
      ..Default::default()
    }
  )?);

  // Non-writable + non-configurable: cannot make writable, and value changes require SameValue.
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      writable: Some(true),
      ..Default::default()
    }
  )?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      value: Some(Value::Number(2.0)),
      ..Default::default()
    }
  )?);
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      value: Some(Value::Number(3.0)),
      ..Default::default()
    }
  )?);

  // NaN is SameValue(NaN, NaN).
  let k_nan = PropertyKey::String(scope.alloc_string("nan")?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_nan,
    PropertyDescriptorPatch {
      value: Some(Value::Number(f64::NAN)),
      writable: Some(false),
      configurable: Some(false),
      ..Default::default()
    }
  )?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_nan,
    PropertyDescriptorPatch {
      value: Some(Value::Number(f64::NAN)),
      ..Default::default()
    }
  )?);

  // +0 and -0 are distinct in SameValue.
  let k_zero = PropertyKey::String(scope.alloc_string("zero")?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_zero,
    PropertyDescriptorPatch {
      value: Some(Value::Number(0.0)),
      writable: Some(false),
      configurable: Some(false),
      ..Default::default()
    }
  )?);
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_zero,
    PropertyDescriptorPatch {
      value: Some(Value::Number(-0.0)),
      ..Default::default()
    }
  )?);

  Ok(())
}

#[test]
fn data_accessor_conversion_requires_configurable() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;

  let k_nc = PropertyKey::String(scope.alloc_string("non_configurable")?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_nc,
    PropertyDescriptorPatch {
      value: Some(Value::Undefined),
      configurable: Some(false),
      ..Default::default()
    }
  )?);
  assert!(!scope.ordinary_define_own_property(
    obj,
    k_nc,
    PropertyDescriptorPatch {
      get: Some(Value::Undefined),
      set: Some(Value::Undefined),
      ..Default::default()
    }
  )?);

  let k_c = PropertyKey::String(scope.alloc_string("configurable")?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_c,
    PropertyDescriptorPatch {
      value: Some(Value::Undefined),
      configurable: Some(true),
      ..Default::default()
    }
  )?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_c,
    PropertyDescriptorPatch {
      get: Some(Value::Undefined),
      set: Some(Value::Undefined),
      ..Default::default()
    }
  )?);

  Ok(())
}

#[test]
fn ordinary_get_traverses_prototype_chain() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut scope = heap.scope();

  let parent = scope.alloc_object()?;
  let child = scope.alloc_object()?;

  let k_p = PropertyKey::String(scope.alloc_string("p")?);
  assert!(scope.create_data_property(parent, k_p, Value::Number(42.0))?);

  scope.object_set_prototype(child, Some(parent))?;

  assert!(scope.ordinary_has_property(child, k_p)?);
  let v = scope.ordinary_get(&mut vm, child, k_p, Value::Object(child))?;
  assert_eq!(v, Value::Number(42.0));

  Ok(())
}

#[test]
fn ordinary_set_creates_own_property_on_receiver_when_writable_in_prototype() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());
  let mut scope = heap.scope();

  let parent = scope.alloc_object()?;
  let child = scope.alloc_object()?;

  let k_x = PropertyKey::String(scope.alloc_string("x")?);
  assert!(scope.ordinary_define_own_property(
    parent,
    k_x,
    PropertyDescriptorPatch {
      value: Some(Value::Number(1.0)),
      writable: Some(true),
      enumerable: Some(true),
      configurable: Some(true),
      ..Default::default()
    }
  )?);

  scope.object_set_prototype(child, Some(parent))?;

  assert!(scope.ordinary_set(
    &mut vm,
    child,
    k_x,
    Value::Number(2.0),
    Value::Object(child)
  )?);

  assert_eq!(
    scope.ordinary_get(&mut vm, child, k_x, Value::Object(child))?,
    Value::Number(2.0)
  );
  assert_eq!(
    scope.ordinary_get(&mut vm, parent, k_x, Value::Object(parent))?,
    Value::Number(1.0)
  );

  Ok(())
}

#[test]
fn ordinary_delete_rejects_non_configurable() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;

  let k_x = PropertyKey::String(scope.alloc_string("x")?);
  assert!(scope.ordinary_define_own_property(
    obj,
    k_x,
    PropertyDescriptorPatch {
      value: Some(Value::Undefined),
      configurable: Some(false),
      ..Default::default()
    }
  )?);
  assert!(!scope.ordinary_delete(obj, k_x)?);

  let k_y = PropertyKey::String(scope.alloc_string("y")?);
  assert!(scope.create_data_property(obj, k_y, Value::Undefined)?);
  assert!(scope.ordinary_delete(obj, k_y)?);

  Ok(())
}

#[test]
fn ordinary_own_property_keys_orders_indices_then_strings_then_symbols() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;

  let k_b = PropertyKey::String(scope.alloc_string("b")?);
  let k_2 = PropertyKey::String(scope.alloc_string("2")?);
  let sym1 = scope.alloc_symbol(None)?;
  let k_sym1 = PropertyKey::Symbol(sym1);
  let k_a = PropertyKey::String(scope.alloc_string("a")?);
  let k_1 = PropertyKey::String(scope.alloc_string("1")?);
  let sym2 = scope.alloc_symbol(None)?;
  let k_sym2 = PropertyKey::Symbol(sym2);
  let k_10 = PropertyKey::String(scope.alloc_string("10")?);

  assert!(scope.create_data_property(obj, k_b, Value::Undefined)?);
  assert!(scope.create_data_property(obj, k_2, Value::Undefined)?);
  assert!(scope.create_data_property(obj, k_sym1, Value::Undefined)?);
  assert!(scope.create_data_property(obj, k_a, Value::Undefined)?);
  assert!(scope.create_data_property(obj, k_1, Value::Undefined)?);
  assert!(scope.create_data_property(obj, k_sym2, Value::Undefined)?);
  assert!(scope.create_data_property(obj, k_10, Value::Undefined)?);

  let keys = scope.ordinary_own_property_keys(obj)?;
  assert_eq!(keys, vec![k_1, k_2, k_10, k_b, k_a, k_sym1, k_sym2]);

  Ok(())
}
