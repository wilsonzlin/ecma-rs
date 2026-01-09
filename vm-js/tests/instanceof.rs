use vm_js::{Heap, HeapLimits, JsRuntime, RootId, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn ordinary_instanceof_true_for_constructed_object() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function C(){}; var o=new C(); o instanceof C === true"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn ordinary_instanceof_false_for_other_object() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"function C(){}; ({} instanceof C) === false"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn instanceof_throws_type_error_when_prototype_is_not_object() {
  let mut rt = new_runtime();
  let err = rt
    .exec_script(r#"function C(){}; C.prototype = 1; ({} instanceof C)"#)
    .unwrap_err();

  let thrown = err
    .thrown_value()
    .unwrap_or_else(|| panic!("expected thrown exception, got {err:?}"));

  // Root the thrown value across any subsequent allocations / script runs.
  let root: RootId = rt.heap_mut().add_root(thrown).expect("root thrown value");

  let Value::Object(thrown_obj) = thrown else {
    panic!("expected thrown value to be an object, got {thrown:?}");
  };

  let type_error_proto = rt
    .exec_script("globalThis.TypeError.prototype")
    .expect("evaluate TypeError.prototype");
  let Value::Object(type_error_proto) = type_error_proto else {
    panic!("expected TypeError.prototype to be an object");
  };

  let thrown_proto = rt
    .heap()
    .object_prototype(thrown_obj)
    .expect("get thrown prototype");
  assert_eq!(thrown_proto, Some(type_error_proto));

  rt.heap_mut().remove_root(root);
}

#[test]
fn has_instance_override_is_called() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"function C(){}; C[Symbol.hasInstance] = function(){ return true; }; ({} instanceof C) === true"#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
