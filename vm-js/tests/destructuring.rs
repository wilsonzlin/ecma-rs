use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn object_destructuring_binds_properties() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var {a,b} = {a:1,b:2}; a+b === 3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_supports_renaming() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var {a:x} = {a:5}; x === 5"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_supports_defaults() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var {a=1} = {}; a === 1"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_supports_rest() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var {a,...r} = {a:1,b:2}; r.b === 2 && r.a === undefined"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_binds_elements_and_holes() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var [x,,y] = [1,2,3]; x===1 && y===3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_supports_defaults() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var [x=1] = []; x===1"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_supports_rest() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var [x,...r] = [1,2,3]; r.length===2"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_assignment_binds_properties() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var a; var b; ({a,b} = {a:1,b:2}); a+b === 3"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn object_destructuring_assignment_can_assign_to_member() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = {}; ({a:o.x} = {a:1}); o.x === 1"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn array_destructuring_assignment_supports_holes_and_rest() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var x; var y; var r; ([x,,y,...r] = [1,2,3,4,5]); x===1 && y===3 && r.length===2 && r[0]===4"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn catch_param_supports_destructuring() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"try { throw {x:1}; } catch({x}) { x }"#)
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}
