use vm_js::{Heap, HeapLimits, VmError};

#[test]
fn object_env_record_traces_binding_object() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let o = scope.alloc_object()?;
  let env = scope.alloc_object_env_record(o, None, false)?;

  // Root only the environment record; the binding object should be kept alive via tracing.
  scope.push_env_root(env)?;
  scope.heap_mut().collect_garbage();

  assert!(scope.heap().is_valid_env(env));
  assert!(scope.heap().is_valid_object(o));
  Ok(())
}

#[test]
fn object_env_record_traces_outer_env() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let outer = scope.alloc_declarative_env_record(None, &[])?;
  let o = scope.alloc_object()?;
  let env = scope.alloc_object_env_record(o, Some(outer), false)?;

  // Root only the inner environment; it should keep both itself and `outer` alive.
  scope.push_env_root(env)?;
  scope.heap_mut().collect_garbage();

  assert!(scope.heap().is_valid_env(env));
  assert!(scope.heap().is_valid_env(outer));
  Ok(())
}

#[test]
fn object_env_record_collected_when_unrooted() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let (o, env) = {
    let mut scope = heap.scope();
    let o = scope.alloc_object()?;
    let env = scope.alloc_object_env_record(o, None, false)?;
    (o, env)
  };

  heap.collect_garbage();
  assert!(!heap.is_valid_env(env));
  assert!(!heap.is_valid_object(o));
  Ok(())
}

#[test]
fn alloc_object_env_record_roots_outer_even_if_root_stack_growth_triggers_gc() -> Result<(), VmError> {
  // Determine a GC threshold that is high enough to allow allocating the inputs, but low enough
  // that growing the root stacks will trigger a GC cycle.
  let gc_threshold = {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    {
      let mut scope = heap.scope();
      scope.env_create(None)?;
      scope.alloc_object()?;
    }
    heap.estimated_total_bytes()
  };

  let mut heap = Heap::new(HeapLimits::new(gc_threshold + 1024 * 1024, gc_threshold));
  {
    let mut scope = heap.scope();
    let outer = scope.env_create(None)?;
    let o = scope.alloc_object()?;

    // Regression: if `alloc_object_env_record` grows the root stack and triggers a GC while only
    // `binding_object` is rooted (but `outer` isn't yet), `outer` can be collected and the
    // allocation fails with `InvalidHandle`.
    let env = scope.alloc_object_env_record(o, Some(outer), false)?;

    scope.push_env_root(env)?;
    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_env(env));
    assert!(scope.heap().is_valid_env(outer));
    assert!(scope.heap().is_valid_object(o));
  }

  Ok(())
}
