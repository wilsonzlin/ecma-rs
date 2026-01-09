use vm_js::{GcObject, Heap, HeapLimits, Scope, Value, Vm, VmError, VmHostHooks, VmOptions};

#[test]
fn user_data_set_get_smoke() {
  let mut vm = Vm::new(VmOptions::default());

  vm.set_user_data(123u32);
  assert_eq!(vm.user_data::<u32>().copied(), Some(123));

  *vm.user_data_mut::<u32>().unwrap() += 1;
  assert_eq!(vm.user_data::<u32>().copied(), Some(124));

  assert_eq!(vm.take_user_data::<u32>(), Some(124));
  assert!(vm.user_data::<u32>().is_none());
}

#[test]
fn user_data_wrong_type_returns_none() {
  let mut vm = Vm::new(VmOptions::default());

  vm.set_user_data(123u32);
  assert!(vm.user_data::<u64>().is_none());
  assert!(vm.user_data_mut::<u64>().is_none());
  assert!(vm.take_user_data::<u64>().is_none());

  // The stored data should be untouched after an incorrect `take_user_data`.
  assert_eq!(vm.user_data::<u32>().copied(), Some(123));
}

#[derive(Default)]
struct Counter(u32);

fn inc_counter(
  vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let counter = vm
    .user_data_mut::<Counter>()
    .ok_or(VmError::Unimplemented("missing Counter user data"))?;
  counter.0 += 1;
  Ok(Value::Undefined)
}

#[test]
fn native_call_can_mutate_user_data() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  vm.set_user_data(Counter::default());

  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(inc_counter)?;
    let name = scope.alloc_string("inc")?;
    let callee = scope.alloc_native_function(call_id, None, name, 0)?;

    vm.call(&mut scope, Value::Object(callee), Value::Undefined, &[])?;
    vm.call(&mut scope, Value::Object(callee), Value::Undefined, &[])?;
  }

  assert_eq!(vm.user_data::<Counter>().unwrap().0, 2);

  Ok(())
}

