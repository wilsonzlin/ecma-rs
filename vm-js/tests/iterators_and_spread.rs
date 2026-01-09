use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn for_of_over_array() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var s=0; for (var x of [1,2,3]) { s = s + x; } s"#)
    .unwrap();
  assert_eq!(value, Value::Number(6.0));
}

#[test]
fn array_spread() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var a=[1,2]; var b=[0,...a,3]; b.length === 4 && b[1]===1 && b[3]===3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn call_spread() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"function add(a,b,c){ return a+b+c; } add(...[1,2,3])"#)
    .unwrap();
  assert_eq!(value, Value::Number(6.0));
}
