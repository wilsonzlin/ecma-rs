use vm_js::{Heap, HeapLimits, Value, Vm, VmOptions};
use webidl::{record_to_js_object, sequence_to_js_array, InterfaceId, JsRuntime, PropertyKey, WebIdlHooks, WebIdlLimits};
use webidl_vm_js::VmJsWebIdlCx;

struct NoHooks;

impl WebIdlHooks<Value> for NoHooks {
  fn is_platform_object(&self, _value: Value) -> bool {
    false
  }

  fn implements_interface(&self, _value: Value, _interface: InterfaceId) -> bool {
    false
  }
}

fn prop_key_str(cx: &mut VmJsWebIdlCx<'_>, s: &str) -> PropertyKey<vm_js::GcString, vm_js::GcSymbol> {
  let units: Vec<u16> = s.encode_utf16().collect();
  let handle = cx
    .alloc_string_from_code_units(&units)
    .expect("alloc string");
  PropertyKey::String(handle)
}

#[test]
fn sequence_to_js_array_and_record_to_js_object_work_under_gc() {
  let mut vm = Vm::new(VmOptions::default());
  // Force a GC cycle before every allocation to stress rooting inside the adapter.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));

  let hooks = NoHooks;
  let limits = WebIdlLimits::default();
  let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

  // --- sequence_to_js_array ---
  let seq = ["a", "b", "c"];
  let array = sequence_to_js_array(&mut cx, &limits, &seq).expect("sequence_to_js_array");

  for (i, expected) in seq.iter().enumerate() {
    let key = webidl::index_to_property_key(&mut cx, i).expect("index key");
    let v = cx.get(array, key).expect("Get(array, i)");
    let Value::String(s) = v else {
      panic!("expected string element");
    };
    assert_eq!(cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(), *expected);
  }

  let length_key = prop_key_str(&mut cx, "length");
  let length = cx.get(array, length_key).expect("Get(array, length)");
  assert_eq!(length, Value::Number(seq.len() as f64));

  let keys = cx.own_property_keys(array).expect("OwnPropertyKeys(array)");
  let keys = keys
    .into_iter()
    .map(|k| match k {
      PropertyKey::String(s) => cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(),
      PropertyKey::Symbol(sym) => format!("sym:{}", cx.scope.heap().get_symbol_id(sym).unwrap()),
    })
    .collect::<Vec<_>>();
  assert_eq!(
    keys,
    vec![
      "0".to_string(),
      "1".to_string(),
      "2".to_string(),
      "length".to_string()
    ]
  );

  // --- record_to_js_object ---
  let entries = [("b", "B"), ("a", "A")];
  let obj = record_to_js_object(&mut cx, &limits, &entries).expect("record_to_js_object");

  for (k, v_expected) in entries.iter() {
    let key = prop_key_str(&mut cx, k);
    let v = cx.get(obj, key).expect("Get(obj, key)");
    let Value::String(s) = v else {
      panic!("expected string value");
    };
    assert_eq!(
      cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(),
      *v_expected
    );
  }

  let keys = cx.own_property_keys(obj).expect("OwnPropertyKeys(obj)");
  let keys = keys
    .into_iter()
    .map(|k| match k {
      PropertyKey::String(s) => cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(),
      PropertyKey::Symbol(sym) => format!("sym:{}", cx.scope.heap().get_symbol_id(sym).unwrap()),
    })
    .collect::<Vec<_>>();
  assert_eq!(keys, vec!["b".to_string(), "a".to_string()]);
}

