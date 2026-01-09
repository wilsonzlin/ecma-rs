use std::cell::Cell;
use vm_js::{GcObject, Heap, HeapLimits, Scope, Value, Vm, VmError, VmHost, VmHostHooks, VmOptions};

thread_local! {
  static LAST_THIS: Cell<Value> = Cell::new(Value::Undefined);
}

const MAGIC_SENTINEL: f64 = 9876.0;

fn observe_this_and_return_first_arg(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  LAST_THIS.with(|cell| cell.set(this));

  match args.get(0).copied() {
    Some(Value::Number(n)) if n == MAGIC_SENTINEL => Ok(this),
    Some(v) => Ok(v),
    None => Ok(Value::Undefined),
  }
}

fn return_undefined(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn return_new_target(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  Ok(new_target)
}

#[test]
fn bound_function_call_binds_this_and_prepends_args() -> Result<(), VmError> {
  LAST_THIS.with(|cell| cell.set(Value::Undefined));

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(observe_this_and_return_first_arg)?;
  let target_name = scope.alloc_string("target")?;
  let target = scope.alloc_native_function(call_id, None, target_name, 0)?;

  let obj_a = scope.alloc_object()?;
  let obj_b = scope.alloc_object()?;

  let bound_name = scope.alloc_string("bound")?;
  let bound = scope.alloc_bound_function(
    target,
    Value::Object(obj_a),
    &[Value::Number(1.0)],
    bound_name,
    0,
  )?;

  let result = vm.call_without_host(
    &mut scope,
    Value::Object(bound),
    Value::Object(obj_b),
    &[Value::Number(2.0)],
  )?;
  assert_eq!(result, Value::Number(1.0));
  assert_eq!(LAST_THIS.with(|cell| cell.get()), Value::Object(obj_a));
  Ok(())
}

#[test]
fn bound_function_construct_forwards_new_target() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(return_undefined)?;
  let construct_id = vm.register_native_construct(return_new_target)?;

  let target_name = scope.alloc_string("target")?;
  let target = scope.alloc_native_function(call_id, Some(construct_id), target_name, 0)?;

  let bound_name = scope.alloc_string("bound")?;
  let bound = scope.alloc_bound_function(target, Value::Undefined, &[], bound_name, 0)?;

  let result =
    vm.construct_without_host(&mut scope, Value::Object(bound), &[], Value::Object(bound))?;
  assert_eq!(result, Value::Object(target));
  Ok(())
}

#[test]
fn bound_function_gc_preserves_bound_slots() -> Result<(), VmError> {
  // Force a GC before each allocation so `alloc_bound_function` must root its GC inputs before
  // calling `ensure_can_allocate`.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let mut vm = Vm::new(VmOptions::default());

  let mut scope = heap.scope();
  let call_id = vm.register_native_call(return_undefined)?;

  let target_name = scope.alloc_string("target")?;
  let target = scope.alloc_native_function(call_id, None, target_name, 0)?;
  let target_root = scope.heap_mut().add_root(Value::Object(target))?;

  let bound_this = scope.alloc_object()?;
  let bound_this_root = scope.heap_mut().add_root(Value::Object(bound_this))?;

  let bound_arg = scope.alloc_object()?;
  let bound_arg_root = scope.heap_mut().add_root(Value::Object(bound_arg))?;

  // Allocate `bound_name` without rooting it. It must remain alive during `alloc_bound_function`.
  let bound_name = scope.alloc_string("bound")?;

  // Now remove persistent roots so `target`/`bound_this`/`bound_arg` are only referenced by locals.
  // If `alloc_bound_function` fails to root them internally, the GC run during allocation will
  // collect them and leave stale handles in the resulting function object.
  scope.heap_mut().remove_root(target_root);
  scope.heap_mut().remove_root(bound_this_root);
  scope.heap_mut().remove_root(bound_arg_root);

  let bound = scope.alloc_bound_function(
    target,
    Value::Object(bound_this),
    &[Value::Object(bound_arg)],
    bound_name,
    0,
  )?;

  // Root only the bound function and confirm its slots are traced.
  scope.push_root(Value::Object(bound))?;
  scope.heap_mut().collect_garbage();

  assert!(scope.heap().is_valid_object(target));
  assert!(scope.heap().is_valid_object(bound_this));
  assert!(scope.heap().is_valid_object(bound_arg));
  assert_eq!(scope.heap().get_string(bound_name)?.to_utf8_lossy(), "bound");
  Ok(())
}
