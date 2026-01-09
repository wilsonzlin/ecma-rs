use vm_js::{Heap, HeapLimits, JsRuntime, TerminationReason, Value, Vm, VmError, VmOptions};

fn new_runtime_with_vm(vm: Vm) -> JsRuntime {
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

#[test]
fn function_decl_and_call() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt.exec_script("function f(){ return 1; } f()").unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn closure_capture() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt
    .exec_script("function make(){ let x = 2; return function(){ return x; } } make()()")
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn constructor_new_sets_this_property() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt
    .exec_script("function C(){ this.x = 3; } let o = new C(); o.x")
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn recursion_triggers_stack_overflow_termination() {
  let mut opts = VmOptions::default();
  opts.max_stack_depth = 8;
  let vm = Vm::new(opts);
  let mut rt = new_runtime_with_vm(vm);

  let err = rt
    .exec_script("function recurse(){ return recurse(); } recurse();")
    .unwrap_err();

  let VmError::Termination(term) = err else {
    panic!("expected termination, got {err:?}");
  };
  assert_eq!(term.reason, TerminationReason::StackOverflow);
  assert_eq!(term.stack.len(), 8);
  assert!(
    term
      .stack
      .iter()
      .any(|f| f.function.as_deref() == Some("recurse") && f.source.as_ref() == "<inline>"),
    "termination stack should include interpreted call frames"
  );
}
