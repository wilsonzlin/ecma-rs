use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn shorthand_and_computed_keys() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var x=1; var k='y'; var o={x,[k]:2}; o.x===1 && o.y===2"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn spread_copies_enumerable_own_properties() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var a={x:1}; var b={...a,y:2}; b.x===1 && b.y===2"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn getter_and_setter_definition() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"var v=0; var o={ get x(){return v;}, set x(n){v=n;} }; o.x===0; o.x=3; o.x===3"#,
    )
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn method_definition_binds_this() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o={ m(){ return this; } }; o.m()===o"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn numeric_literal_keys_match_computed_access() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o={0.000001:1,1e21:2}; o[0.000001]===1 && o[1e21]===2"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}
