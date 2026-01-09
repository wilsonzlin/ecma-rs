use vm_js::{
  GcObject, Heap, HeapLimits, JsRuntime, Scope, TerminationReason, Value, Vm, VmError, VmHostHooks,
  VmHost, VmOptions,
};

fn new_runtime_with_vm(vm: Vm) -> JsRuntime {
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn host_add(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let a = match args.get(0).copied().unwrap_or(Value::Undefined) {
    Value::Number(n) => n,
    _ => return Err(VmError::Unimplemented("host_add arg0 not number")),
  };
  let b = match args.get(1).copied().unwrap_or(Value::Undefined) {
    Value::Number(n) => n,
    _ => return Err(VmError::Unimplemented("host_add arg1 not number")),
  };
  Ok(Value::Number(a + b))
}

fn host_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let callee = args.get(0).copied().unwrap_or(Value::Undefined);
  let x = args.get(1).copied().unwrap_or(Value::Undefined);
  vm.call_with_host(scope, hooks, callee, Value::Undefined, &[x])
}

#[test]
fn function_decl_and_call() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt.exec_script("function f(){ return 1; } f()").unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn function_decl_with_param_and_call() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt.exec_script("function f(x){ return x; } f(3)").unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn closure_capture() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt
    .exec_script("function make(){ let x = 1; return function(){ return x; } } make()()")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn member_access_dot_and_bracket() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let v1 = rt.exec_script("var o={a:1}; o.a").unwrap();
  assert_eq!(v1, Value::Number(1.0));
  let v2 = rt.exec_script("var o={a:1}; o['a']").unwrap();
  assert_eq!(v2, Value::Number(1.0));
}

#[test]
fn method_call_sets_this() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  let value = rt
    .exec_script("var o={x:1, f:function(){return this.x;}}; o.f()")
    .unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn native_function_call_from_script() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  rt
    .register_global_native_function("__host_add", host_add, 2)
    .unwrap();
  let value = rt.exec_script("__host_add(1,2)").unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn native_can_call_ecma_callback_via_vm_call() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);
  rt
    .register_global_native_function("__host_call", host_call, 2)
    .unwrap();

  let value = rt
    .exec_script("function id(x){ return x; } __host_call(id, 3)")
    .unwrap();
  assert_eq!(value, Value::Number(3.0));
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
fn promise_then_handler_runs_in_microtask_checkpoint() {
  let vm = Vm::new(VmOptions::default());
  let mut rt = new_runtime_with_vm(vm);

  // `then` schedules the handler as a microtask, so the initial script evaluation should see the
  // old value.
  let value = rt
    .exec_script(
      "var result = 0; Promise.resolve(1).then(function(x){ result = x; }); result",
    )
    .unwrap();
  assert_eq!(value, Value::Number(0.0));

  rt.vm.perform_microtask_checkpoint(&mut rt.heap).unwrap();

  let value = rt.exec_script("result").unwrap();
  assert_eq!(value, Value::Number(1.0));
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
