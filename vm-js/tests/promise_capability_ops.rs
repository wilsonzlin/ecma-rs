use std::cell::Cell;

use vm_js::{
  new_promise_capability, perform_promise_then, promise_resolve, GcObject, Heap, HeapLimits, Realm,
  Scope, Value, Vm, VmError, VmHostHooks, VmJobContext, VmOptions,
};

thread_local! {
  static THEN_CALLED: Cell<bool> = const { Cell::new(false) };
}

fn then_handler(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  THEN_CALLED.with(|c| c.set(true));
  Ok(Value::Undefined)
}

struct TestCtx<'a> {
  vm: &'a mut Vm,
  heap: &'a mut Heap,
}

impl VmJobContext for TestCtx<'_> {
  fn call(
    &mut self,
    host: &mut dyn VmHostHooks,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let mut scope = self.heap.scope();
    self.vm.call_with_host(&mut scope, host, callee, this, args)
  }

  fn construct(
    &mut self,
    host: &mut dyn VmHostHooks,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let mut scope = self.heap.scope();
    self
      .vm
      .construct_with_host(&mut scope, host, callee, args, new_target)
  }

  fn add_root(&mut self, value: Value) -> Result<vm_js::RootId, VmError> {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: vm_js::RootId) {
    self.heap.remove_root(id);
  }
}

#[test]
fn promise_capability_resolve_runs_then_only_at_microtask_checkpoint() -> Result<(), VmError> {
  THEN_CALLED.with(|c| c.set(false));

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let mut host = vm_js::MicrotaskQueue::new();

  let capability = {
    let mut scope = heap.scope();
    new_promise_capability(&mut vm, &mut scope, &mut host)?
  };

  // Attach `then_handler` to the capability promise.
  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(then_handler)?;
    let name = scope.alloc_string("then_handler")?;
    let on_fulfilled = scope.alloc_native_function(call_id, None, name, 1)?;

    let _derived = perform_promise_then(
      &mut vm,
      &mut scope,
      &mut host,
      capability.promise,
      Some(Value::Object(on_fulfilled)),
      None,
    )?;
  }

  // Resolve the promise, which should enqueue a reaction job but not run it synchronously.
  {
    let mut scope = heap.scope();
    let _ = vm.call_with_host(
      &mut scope,
      &mut host,
      capability.resolve,
      Value::Undefined,
      &[Value::Undefined],
    )?;
  }

  assert!(
    !THEN_CALLED.with(|c| c.get()),
    "then handler should not run synchronously"
  );

  let mut ctx = TestCtx { vm: &mut vm, heap: &mut heap };
  host.perform_microtask_checkpoint(&mut ctx)?;

  assert!(THEN_CALLED.with(|c| c.get()));

  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn promise_resolve_helper_returns_promise_and_then_is_async() -> Result<(), VmError> {
  THEN_CALLED.with(|c| c.set(false));

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let mut host = vm_js::MicrotaskQueue::new();

  let promise = {
    let mut scope = heap.scope();
    promise_resolve(&mut vm, &mut scope, &mut host, Value::Undefined)?
  };

  // Attach a then-handler. Even though `promise` is already fulfilled, the handler must run via
  // the microtask queue.
  {
    let mut scope = heap.scope();
    let call_id = vm.register_native_call(then_handler)?;
    let name = scope.alloc_string("then_handler")?;
    let on_fulfilled = scope.alloc_native_function(call_id, None, name, 1)?;

    let _derived = perform_promise_then(
      &mut vm,
      &mut scope,
      &mut host,
      promise,
      Some(Value::Object(on_fulfilled)),
      None,
    )?;
  }

  assert!(
    !THEN_CALLED.with(|c| c.get()),
    "then handler should not run synchronously"
  );

  let mut ctx = TestCtx { vm: &mut vm, heap: &mut heap };
  host.perform_microtask_checkpoint(&mut ctx)?;

  assert!(THEN_CALLED.with(|c| c.get()));

  realm.teardown(&mut heap);
  Ok(())
}

