use vm_js::{Heap, HeapLimits, JobCallback, PromiseReaction, PromiseReactionType, Value, VmError};

#[test]
fn gc_collects_unreachable_objects() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj;
  let s;
  let sym;
  {
    let mut scope = heap.scope();

    obj = scope.alloc_object()?;
    s = scope.alloc_string("hello")?;
    sym = scope.alloc_symbol(Some("desc"))?;

    assert!(scope.heap().is_valid_object(obj));
    assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "hello");
    let desc = scope
      .heap()
      .get_symbol_description(sym)?
      .expect("allocated symbols should have descriptions");
    assert_eq!(scope.heap().get_string(desc)?.to_utf8_lossy(), "desc");

    // Not rooted: everything allocated in this scope becomes unreachable once the scope ends.
    assert!(scope.heap().used_bytes() > 0);
  }

  heap.collect_garbage();
  assert_eq!(heap.used_bytes(), 0);

  assert!(!heap.is_valid_object(obj));
  assert!(matches!(heap.get_string(s), Err(VmError::InvalidHandle)));
  assert!(matches!(
    heap.get_symbol_description(sym),
    Err(VmError::InvalidHandle)
  ));

  Ok(())
}

#[test]
fn gc_preserves_stack_rooted_objects() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj;
  {
    let mut scope = heap.scope();
    obj = scope.alloc_object()?;
    scope.push_root(Value::Object(obj));

    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_object(obj));
  }

  // Stack roots were removed when the scope was dropped.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(obj));
  assert_eq!(heap.used_bytes(), 0);
  Ok(())
}

#[test]
fn persistent_roots_keep_objects_live() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let obj;
  let root;
  {
    let mut scope = heap.scope();
    obj = scope.alloc_object()?;
    root = scope.heap_mut().add_root(Value::Object(obj));
  }

  heap.collect_garbage();
  assert!(heap.is_valid_object(obj));

  heap.remove_root(root);
  heap.collect_garbage();
  assert!(!heap.is_valid_object(obj));
  Ok(())
}

#[test]
fn generations_change_when_slot_reused() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let first;
  {
    let mut scope = heap.scope();
    first = scope.alloc_object()?;
  }

  heap.collect_garbage();
  assert!(!heap.is_valid_object(first));

  let second;
  {
    let mut scope = heap.scope();
    second = scope.alloc_object()?;
  }

  assert_eq!(first.index(), second.index());
  assert_ne!(first.generation(), second.generation());

  // Stale handles are invalidated via the generation check.
  assert!(!heap.is_valid_object(first));
  assert!(heap.is_valid_object(second));

  Ok(())
}

#[test]
fn promise_slots_are_traced_by_gc() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let promise;
  let referenced;
  {
    let mut scope = heap.scope();

    promise = scope.alloc_promise()?;
    referenced = scope.alloc_object()?;
    scope
      .heap_mut()
      .promise_fulfill(promise, Value::Object(referenced))?;

    scope.push_root(Value::Object(promise));
    scope.heap_mut().collect_garbage();
    assert!(
      scope.heap().is_valid_object(referenced),
      "promise.[[PromiseResult]] should be traced"
    );
  }

  // Stack roots were removed when the scope was dropped.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(referenced));
  Ok(())
}

#[test]
fn promise_reaction_lists_are_cleared_on_settlement() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let handler;
  {
    let mut scope = heap.scope();

    let promise = scope.alloc_promise()?;
    handler = scope.alloc_object()?;

    scope.promise_append_fulfill_reaction(
      promise,
      PromiseReaction {
        capability: None,
        type_: PromiseReactionType::Fulfill,
        handler: Some(JobCallback::new(handler)),
      },
    )?;

    scope.push_root(Value::Object(promise));

    // While the promise is pending, its reaction lists keep handlers alive.
    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_object(handler));

    // Settlement clears the reaction lists so they do not keep handlers alive unnecessarily.
    scope.heap_mut().promise_fulfill(promise, Value::Undefined)?;
    scope.heap_mut().collect_garbage();
    assert!(!scope.heap().is_valid_object(handler));
  }

  Ok(())
}
