use vm_js::{Heap, HeapLimits, JsRuntime, Value, Vm, VmOptions};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn switch_fallthrough_and_break() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"var y=0; switch(2){ case 1: y=1; break; case 2: y=2; /*fall*/ case 3: y=y+1; } y"#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn labelled_break_out_of_nested_loop() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"outer: while(true){ while(true){ break outer; } } 1"#)
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn labelled_continue_targets_outer_loop() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(
      r#"var n=0; outer: for(var i=0;i<3;i=i+1){ for(var j=0;j<3;j=j+1){ n=n+1; continue outer; } } n"#,
    )
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}
