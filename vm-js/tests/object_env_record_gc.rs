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
