use vm_js::{
  Heap, HeapLimits, JobCallback, NativeFunctionId, PromiseReaction, PromiseReactionType, Value, VmError,
};

#[test]
fn promise_result_value_is_traced() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let promise;
  let result_string;
  {
    let mut scope = heap.scope();
    promise = scope.alloc_promise()?;
    scope.push_root(Value::Object(promise));

    result_string = scope.alloc_string("result")?;
    scope
      .heap_mut()
      .promise_fulfill(promise, Value::String(result_string))?;

    scope.heap_mut().collect_garbage();
    assert_eq!(scope.heap().get_string(result_string)?.to_utf8_lossy(), "result");
  }

  // Stack roots were removed when the scope was dropped.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(promise));
  assert!(matches!(heap.get_string(result_string), Err(VmError::InvalidHandle)));
  Ok(())
}

#[test]
fn promise_reaction_handler_traced_while_pending_and_collectable_after_settlement() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let promise;
  let handler;
  {
    let mut scope = heap.scope();

    promise = scope.alloc_promise()?;
    assert!(scope.heap().is_promise(promise));
    scope.push_root(Value::Object(promise));

    let handler_name = scope.alloc_string("handler")?;
    handler = scope.alloc_native_function(NativeFunctionId(1), None, handler_name, 0)?;

    scope.heap_mut().promise_push_fulfill_reaction(
      promise,
      PromiseReaction {
        capability: None,
        type_: PromiseReactionType::Fulfill,
        handler: Some(JobCallback::new(handler)),
      },
    )?;

    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_object(handler));

    // Settling clears reaction lists to `None`, allowing the handler to be collected if otherwise
    // unreachable.
    scope.heap_mut().promise_fulfill(promise, Value::Undefined)?;

    scope.heap_mut().collect_garbage();
    assert!(!scope.heap().is_valid_object(handler));
  }

  Ok(())
}

