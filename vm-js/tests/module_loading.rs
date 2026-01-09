use vm_js::import_attributes_from_options;
use vm_js::module_requests_equal;
use vm_js::ImportAttribute;
use vm_js::ModuleLoadPayload;
use vm_js::ModuleRequest;
use vm_js::PropertyDescriptor;
use vm_js::PropertyKey;
use vm_js::PropertyKind;
use vm_js::Value;
use vm_js::{Heap, HeapLimits, Vm, VmOptions};

fn data_desc(value: Value, enumerable: bool) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

#[test]
fn module_requests_equal_ignores_attribute_order() {
  let a_type = ImportAttribute::new("type", "json");
  let a_mode = ImportAttribute::new("mode", "strict");

  let left = ModuleRequest::new("./foo.mjs", vec![a_type.clone(), a_mode.clone()]);
  let right = ModuleRequest::new("./foo.mjs", vec![a_mode, a_type]);

  assert!(module_requests_equal(&left, &right));
}

#[test]
fn module_requests_equal_checks_specifier_and_attributes() {
  let a_type_json = ImportAttribute::new("type", "json");
  let a_type_css = ImportAttribute::new("type", "css");

  let left = ModuleRequest::new("./foo.mjs", vec![a_type_json.clone()]);

  // Different specifier => not equal.
  let different_specifier = ModuleRequest::new("./bar.mjs", vec![a_type_json.clone()]);
  assert!(!module_requests_equal(&left, &different_specifier));

  // Different attributes => not equal.
  let different_attrs = ModuleRequest::new("./foo.mjs", vec![a_type_css]);
  assert!(!module_requests_equal(&left, &different_attrs));

  // Different attribute count => not equal.
  let extra_attr =
    ModuleRequest::new("./foo.mjs", vec![a_type_json, ImportAttribute::new("mode", "strict")]);
  assert!(!module_requests_equal(&left, &extra_attr));
}

#[test]
fn module_load_payload_is_clone() {
  fn assert_clone<T: Clone>() {}
  assert_clone::<ModuleLoadPayload>();
}

#[test]
fn import_attributes_from_options_sorts_by_utf16_code_unit_order() {
  // ECMA-262 sorts attribute keys by UTF-16 code units; for non-BMP characters this differs from
  // Rust's `str` ordering (UTF-8 bytes).
  //
  // U+1F600 (😀) encodes to UTF-16 `[0xD83D, 0xDE00]` which sorts before U+E000 (`[0xE000]`).
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();
  let mut vm = Vm::new(VmOptions::default());

  let options = scope.alloc_object().unwrap();
  let attributes = scope.alloc_object().unwrap();

  let k_with = scope.alloc_string("with").unwrap();
  let k_emoji = scope.alloc_string("😀").unwrap();
  let k_private_use = scope.alloc_string("\u{E000}").unwrap();
  let v_1 = scope.alloc_string("1").unwrap();
  let v_2 = scope.alloc_string("2").unwrap();

  // Define in a non-sorted order to ensure we exercise the sort.
  scope
    .define_property(
      attributes,
      PropertyKey::String(k_private_use),
      data_desc(Value::String(v_2), true),
    )
    .unwrap();
  scope
    .define_property(
      attributes,
      PropertyKey::String(k_emoji),
      data_desc(Value::String(v_1), true),
    )
    .unwrap();

  scope
    .define_property(
      options,
      PropertyKey::String(k_with),
      data_desc(Value::Object(attributes), true),
    )
    .unwrap();

  let supported = ["😀", "\u{E000}"];
  let attrs =
    import_attributes_from_options(&mut vm, &mut scope, Value::Object(options), &supported)
      .unwrap();

  let keys: Vec<&str> = attrs.iter().map(|a| a.key.as_str()).collect();
  assert_eq!(keys, vec!["😀", "\u{E000}"]);
}
