use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn default_parameter_initializer_is_used_when_arg_is_undefined() {
  let mut rt = new_runtime();
  let value = rt.exec_script("function f(a=2){ return a; } f()").unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn default_parameter_initializer_can_reference_previous_params() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function f(a=1,b=a){ return b; } f(undefined, undefined)")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn rest_parameter_collects_remaining_args_into_array() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function f(...r){ return r.length; } f(1,2,3)")
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn arguments_object_has_indices_and_length() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function f(){ return arguments[1]; } f(1,2,3)")
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn arguments_object_is_visible_to_default_parameter_initializers() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script("function f(a = arguments[1]){ return a; } f(undefined, 2)")
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn function_length_excludes_default_and_rest_parameters() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      "function f(a,b=2,c){}; function g(a,...r){}; function h(a=1,b){}; f.length===1 && g.length===1 && h.length===0",
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn default_parameter_initializer_cannot_reference_itself() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      "try { function f(a = a) { return a; } f(); false } catch (e) { e.name === 'ReferenceError' }",
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

