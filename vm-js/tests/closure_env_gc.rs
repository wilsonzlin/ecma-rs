use semantic_js::js::SymbolId;
use vm_js::{EnvBinding, Heap, HeapLimits, NativeFunctionId, Value, VmError};

#[test]
fn native_function_closure_env_keeps_env_and_bindings_alive_across_gc() -> Result<(), VmError> {
  // Use a tiny GC threshold to force GC during root-stack growth inside
  // `alloc_native_function_with_env`. This ensures the allocator treats `closure_env` as an extra
  // root while rooting its own inputs.
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));

  let func;
  let env;
  let captured;
  {
    let mut scope = heap.scope();

    let name = scope.alloc_string("f")?;
    // Root `name` across environment allocation in case it triggers a GC (forced by the tiny
    // threshold).
    scope.push_root(Value::String(name))?;

    captured = scope.alloc_string("hello")?;
    env = scope.alloc_env_record(
      None,
      &[EnvBinding {
        symbol: SymbolId::from_raw(1),
        name: None,
        value: Value::String(captured),
        initialized: true,
        mutable: true,
        strict: true,
      }],
    )?;

    func = scope.alloc_native_function_with_env(NativeFunctionId(1), None, name, 0, Some(env))?;

    // Only root the function; if it doesn't trace `closure_env`, `env` (and its binding value)
    // would be collected.
    scope.push_root(Value::Object(func))?;

    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_object(func));
    assert!(scope.heap().is_valid_env(env));
    assert_eq!(scope.heap().get_string(captured)?.to_utf8_lossy(), "hello");
  }

  // Stack roots were removed when the scope was dropped: all objects should now be collectable.
  heap.collect_garbage();
  assert!(!heap.is_valid_object(func));
  assert!(!heap.is_valid_env(env));
  assert!(matches!(heap.get_string(captured), Err(VmError::InvalidHandle)));
  Ok(())
}

#[test]
fn outer_env_kept_alive_via_closure_chain() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let env1;
  let env2;
  let func;
  {
    let mut scope = heap.scope();
    let name = scope.alloc_string("f")?;

    env1 = scope.alloc_env_record(None, &[])?;
    env2 = scope.alloc_env_record(Some(env1), &[])?;

    func = scope.alloc_native_function_with_env(NativeFunctionId(1), None, name, 0, Some(env2))?;

    // Root only the function object. The outer env record must remain alive via
    // `func.closure_env -> env2.outer`.
    scope.push_root(Value::Object(func))?;
    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_env(env2));
    assert!(scope.heap().is_valid_env(env1));
  }

  Ok(())
}

