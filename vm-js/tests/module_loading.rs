use std::sync::Arc;

use vm_js::module_requests_equal;
use vm_js::ImportAttribute;
use vm_js::ModuleLoadPayload;
use vm_js::ModuleRequest;

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
  let extra_attr = ModuleRequest {
    specifier: Arc::from("./foo.mjs"),
    attributes: vec![a_type_json, ImportAttribute::new("mode", "strict")],
  };
  assert!(!module_requests_equal(&left, &extra_attr));
}

#[test]
fn module_load_payload_is_clone() {
  fn assert_clone<T: Clone>() {}
  assert_clone::<ModuleLoadPayload>();
}

