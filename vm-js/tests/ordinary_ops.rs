use std::cell::Cell;
use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Scope, Value, Vm, VmError, VmOptions,
};

thread_local! {
  static GETTER_CALLS: Cell<u32> = const { Cell::new(0) };
  static EXPECTED_THIS: Cell<Option<vm_js::GcObject>> = const { Cell::new(None) };
}

fn getter(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: vm_js::GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  GETTER_CALLS.with(|c| c.set(c.get() + 1));

  let expected = EXPECTED_THIS
    .with(|t| t.get())
    .expect("EXPECTED_THIS should be set by the test");
  assert_eq!(this, Value::Object(expected), "`this` should be the receiver");

  // Force a GC to ensure `Vm::get` + `Vm::call` root the receiver correctly while invoking the
  // getter.
  scope.heap_mut().collect_garbage();
  assert!(
    scope.heap().is_valid_object(expected),
    "receiver should remain live across GC while in-call"
  );

  Ok(Value::Number(123.0))
}

#[test]
fn get_invokes_accessor_getter_once_with_receiver() -> Result<(), VmError> {
  GETTER_CALLS.with(|c| c.set(0));

  // Force GC before every allocation to stress rooting.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();

  let call_id = vm.register_native_call(getter)?;
  let name = scope.alloc_string("get")?;
  let getter_fn = scope.alloc_native_function(call_id, None, name, 0)?;
  // Root the getter function across subsequent allocations; GC is forced before every allocation in
  // this test.
  scope.push_root(Value::Object(getter_fn));

  let proto = scope.alloc_object()?;
  scope.push_root(Value::Object(proto));
  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));

  scope.heap_mut().object_set_prototype(obj, Some(proto))?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  let desc = PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Accessor {
      get: Value::Object(getter_fn),
      set: Value::Undefined,
    },
  };
  scope.define_property(proto, key, desc)?;

  EXPECTED_THIS.with(|t| t.set(Some(obj)));
  let value = vm.get(&mut scope, obj, key)?;
  assert_eq!(value, Value::Number(123.0));
  assert_eq!(GETTER_CALLS.with(|c| c.get()), 1);

  Ok(())
}

#[test]
fn own_property_keys_orders_indices_then_strings_then_symbols() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));

  // Insert properties in a deliberately mixed order.
  let k_b = PropertyKey::from_string(scope.alloc_string("b")?);
  let k_2 = PropertyKey::from_string(scope.alloc_string("2")?);
  let k_a = PropertyKey::from_string(scope.alloc_string("a")?);
  let k_1 = PropertyKey::from_string(scope.alloc_string("1")?);

  let sym1 = scope.alloc_symbol(Some("s1"))?;
  let sym2 = scope.alloc_symbol(Some("s2"))?;
  let k_sym1 = PropertyKey::from_symbol(sym1);
  let k_sym2 = PropertyKey::from_symbol(sym2);

  let data_desc = |value: Value| PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  };

  scope.define_property(obj, k_b, data_desc(Value::Number(1.0)))?;
  scope.define_property(obj, k_2, data_desc(Value::Number(2.0)))?;
  scope.define_property(obj, k_a, data_desc(Value::Number(3.0)))?;
  scope.define_property(obj, k_1, data_desc(Value::Number(4.0)))?;
  scope.define_property(obj, k_sym1, data_desc(Value::Number(5.0)))?;
  scope.define_property(obj, k_sym2, data_desc(Value::Number(6.0)))?;

  let keys = scope.heap().ordinary_own_property_keys(obj)?;
  let as_debug = keys
    .iter()
    .map(|&k| match k {
      PropertyKey::String(s) => scope.heap().get_string(s).unwrap().to_utf8_lossy(),
      PropertyKey::Symbol(sym) => format!("sym:{}", scope.heap().get_symbol_id(sym).unwrap()),
    })
    .collect::<Vec<_>>();

  // Array indices are returned first, sorted numerically.
  // Then other string keys in insertion order ("b", then "a").
  // Then symbols in insertion order.
  assert_eq!(
    as_debug,
    vec![
      "1".to_string(),
      "2".to_string(),
      "b".to_string(),
      "a".to_string(),
      format!("sym:{}", scope.heap().get_symbol_id(sym1).unwrap()),
      format!("sym:{}", scope.heap().get_symbol_id(sym2).unwrap()),
    ]
  );

  Ok(())
}

#[test]
fn to_string_and_to_number_cover_webidl_primitives() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let s = heap.to_string(Value::Undefined)?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "undefined");
  let s = heap.to_string(Value::Null)?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "null");
  let s = heap.to_string(Value::Bool(true))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "true");
  let s = heap.to_string(Value::Bool(false))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "false");
  let s = heap.to_string(Value::Number(42.0))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "42");
  let s = heap.to_string(Value::Number(-0.0))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "0");
  let s = heap.to_string(Value::Number(f64::INFINITY))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "Infinity");
  let s = heap.to_string(Value::Number(f64::NEG_INFINITY))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "-Infinity");
  let s = heap.to_string(Value::Number(f64::NAN))?;
  assert_eq!(heap.get_string(s)?.to_utf8_lossy(), "NaN");

  assert!(heap.to_number(Value::Undefined)?.is_nan());
  assert_eq!(heap.to_number(Value::Null)?, 0.0);
  assert_eq!(heap.to_number(Value::Bool(true))?, 1.0);
  assert_eq!(heap.to_number(Value::Bool(false))?, 0.0);

  let mut scope = heap.scope();
  let s = scope.alloc_string("  123  ")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, 123.0);
  let s = scope.alloc_string("")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, 0.0);
  let s = scope.alloc_string("   ")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, 0.0);
  let s = scope.alloc_string("Infinity")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, f64::INFINITY);
  let s = scope.alloc_string("+Infinity")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, f64::INFINITY);
  let s = scope.alloc_string("-Infinity")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, f64::NEG_INFINITY);
  let s = scope.alloc_string("NaN")?;
  assert!(scope.heap_mut().to_number(Value::String(s))?.is_nan());
  let s = scope.alloc_string("0x10")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, 16.0);
  let s = scope.alloc_string("0b10")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, 2.0);
  let s = scope.alloc_string("0o10")?;
  assert_eq!(scope.heap_mut().to_number(Value::String(s))?, 8.0);

  Ok(())
}
