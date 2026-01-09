use vm_js::{Heap, HeapLimits, JsRuntime, RootId, Value, Vm, VmError, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn strict_directive_makes_unbound_assignment_throw_reference_error() {
  let mut rt = new_runtime();
  let err = rt.exec_script(r#""use strict"; x = 1;"#).unwrap_err();

  let VmError::Throw(thrown) = err else {
    panic!("expected VmError::Throw, got {err:?}");
  };

  // Root the thrown value across any subsequent allocations / script runs.
  let root: RootId = rt
    .heap_mut()
    .add_root(thrown)
    .expect("root thrown value");

  let Value::Object(thrown_obj) = thrown else {
    panic!("expected thrown value to be an object, got {thrown:?}");
  };

  // Obtain the intrinsic %ReferenceError.prototype% via the global bindings:
  // globalThis.ReferenceError.prototype
  let reference_error_proto = rt
    .exec_script("globalThis.ReferenceError.prototype")
    .expect("evaluate ReferenceError.prototype");
  let Value::Object(reference_error_proto) = reference_error_proto else {
    panic!("expected ReferenceError.prototype to be an object");
  };

  let thrown_proto = rt
    .heap()
    .object_prototype(thrown_obj)
    .expect("get thrown prototype");
  assert_eq!(thrown_proto, Some(reference_error_proto));

  rt.heap_mut().remove_root(root);
}

#[test]
fn non_strict_keeps_sloppy_global_creation_behaviour() {
  let mut rt = new_runtime();
  let value = rt.exec_script("x = 1; globalThis.x === 1").unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn strict_function_plain_call_has_undefined_this() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function f(){ "use strict"; return this === undefined; } f()"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
