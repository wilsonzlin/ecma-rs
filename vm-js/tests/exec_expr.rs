use vm_js::{GcObject, Heap, HeapLimits, JsRuntime, Scope, Value, Vm, VmError, VmOptions, PropertyKey};

fn new_runtime() -> JsRuntime {
  let vm = Vm::new(VmOptions::default());
  let heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  JsRuntime::new(vm, heap).unwrap()
}

fn return_this(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(this)
}

fn return_arg_count(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(args.len() as f64))
}

#[test]
fn object_literal_member_get_set() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var o = {a: 1}; o.a === 1; o.a = 2; o.a"#)
    .unwrap();
  assert_eq!(value, Value::Number(2.0));
}

#[test]
fn computed_member_get_set() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var o = {}; o["x"] = 3; o.x"#).unwrap();
  assert_eq!(value, Value::Number(3.0));
}

#[test]
fn array_literal_index_get() {
  let mut rt = new_runtime();
  let value = rt
    .exec_script(r#"var a = [1,2]; (a[0] === 1) && (a[1] === 2)"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn arithmetic_precedence() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"1 + 2 * 3 === 7"#).unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn logical_ops() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"true && false"#).unwrap();
  assert_eq!(value, Value::Bool(false));

  let value = rt.exec_script(r#"false || true"#).unwrap();
  assert_eq!(value, Value::Bool(true));

  let value = rt.exec_script(r#"null ?? 5"#).unwrap();
  assert_eq!(value, Value::Number(5.0));
}

#[test]
fn cond_operator() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"true ? 1 : 2"#).unwrap();
  assert_eq!(value, Value::Number(1.0));
}

#[test]
fn delete_member() {
  let mut rt = new_runtime();
  let value = rt.exec_script(r#"var o = {a: 1}; delete o.a; o.a"#).unwrap();
  assert_eq!(value, Value::Undefined);
}

#[test]
fn call_expr_member_binds_this() {
  let mut rt = new_runtime();

  let call_id = rt.vm.register_native_call(return_this).unwrap();
  let global = rt.realm().global_object();
  let mut scope = rt.heap.scope();
  let name = scope.alloc_string("returnThis").unwrap();
  let func = scope.alloc_native_function(call_id, None, name, 0).unwrap();
  let ok = scope
    .create_data_property(global, PropertyKey::from_string(name), Value::Object(func))
    .unwrap();
  assert!(ok);
  drop(scope);

  let value = rt
    .exec_script(r#"var o = {}; o.f = returnThis; o.f() === o"#)
    .unwrap();
  assert_eq!(value, Value::Bool(true));
}

#[test]
fn call_expr_passes_arguments() {
  let mut rt = new_runtime();

  let call_id = rt.vm.register_native_call(return_arg_count).unwrap();
  let global = rt.realm().global_object();
  let mut scope = rt.heap.scope();
  let name = scope.alloc_string("argc").unwrap();
  let func = scope.alloc_native_function(call_id, None, name, 0).unwrap();
  let ok = scope
    .create_data_property(global, PropertyKey::from_string(name), Value::Object(func))
    .unwrap();
  assert!(ok);
  drop(scope);

  let value = rt.exec_script(r#"argc(1, 2, 3)"#).unwrap();
  assert_eq!(value, Value::Number(3.0));
}
