use semantic_js::js::SymbolId;
use vm_js::{EnvBinding, Heap, HeapLimits, Value, VmError};

#[test]
fn env_record_is_collectible_when_unrooted() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let env;
  {
    let mut scope = heap.scope();
    env = scope.alloc_env_record(None, &[])?;
    assert!(scope.heap().is_valid_env(env));
  }

  heap.collect_garbage();
  assert!(!heap.is_valid_env(env));
  Ok(())
}

#[test]
fn env_record_survives_when_stack_rooted() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let env;
  {
    let mut scope = heap.scope();
    env = scope.alloc_env_record(None, &[])?;
    scope.push_env_root(env)?;

    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_env(env));
  }

  heap.collect_garbage();
  assert!(!heap.is_valid_env(env));
  Ok(())
}

#[test]
fn persistent_env_roots_keep_env_records_live() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let env;
  let root;
  {
    let mut scope = heap.scope();
    env = scope.alloc_env_record(None, &[])?;
    root = scope.heap_mut().add_env_root(env)?;
  }

  heap.collect_garbage();
  assert!(heap.is_valid_env(env));

  heap.remove_env_root(root);
  heap.collect_garbage();
  assert!(!heap.is_valid_env(env));
  Ok(())
}

#[test]
fn env_record_traces_outer_env_record() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let env1;
  let env2;
  {
    let mut scope = heap.scope();
    env1 = scope.alloc_env_record(None, &[])?;
    env2 = scope.alloc_env_record(Some(env1), &[])?;
    scope.push_env_root(env2)?;

    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_env(env2));
    assert!(
      scope.heap().is_valid_env(env1),
      "expected rooting env2 to keep env1 alive via env2.outer tracing"
    );
  }

  Ok(())
}

#[test]
fn env_record_traces_binding_values() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let env;
  let s;
  {
    let mut scope = heap.scope();
    s = scope.alloc_string("hello")?;

    let sym = SymbolId::from_raw(1);
    env = scope.alloc_env_record(
      None,
      &[EnvBinding {
        symbol: sym,
        name: None,
        value: Value::String(s),
        initialized: true,
        mutable: true,
        strict: true,
      }],
    )?;

    scope.push_env_root(env)?;
    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_env(env));
    assert!(
      scope.heap().is_valid_string(s),
      "expected env record to keep binding value alive"
    );
  }

  Ok(())
}

#[test]
fn alloc_env_record_roots_all_inputs_even_if_root_stack_growth_triggers_gc() -> Result<(), VmError> {
  // Determine a GC threshold that is high enough to allow allocating the inputs, but low enough
  // that growing the root stacks will trigger a GC cycle.
  let gc_threshold = {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    {
      let mut scope = heap.scope();
      scope.env_create(None)?;
      scope.alloc_string("a")?;
      scope.alloc_string("b")?;
    }
    heap.estimated_total_bytes()
  };

  let mut heap = Heap::new(HeapLimits::new(gc_threshold + 1024 * 1024, gc_threshold));
  let outer;
  let env;
  let a;
  let b;
  {
    let mut scope = heap.scope();
    outer = scope.env_create(None)?;
    a = scope.alloc_string("a")?;
    b = scope.alloc_string("b")?;

    env = scope.alloc_env_record(
      Some(outer),
      &[
        EnvBinding {
          symbol: SymbolId::from_raw(1),
          name: None,
          value: Value::String(a),
          initialized: true,
          mutable: true,
          strict: true,
        },
        EnvBinding {
          symbol: SymbolId::from_raw(2),
          name: None,
          value: Value::String(b),
          initialized: true,
          mutable: true,
          strict: true,
        },
      ],
    )?;

    // Root the resulting env record and ensure it keeps both strings and the outer env alive.
    scope.push_env_root(env)?;
    scope.heap_mut().collect_garbage();
    assert!(scope.heap().is_valid_env(env));
    assert!(scope.heap().is_valid_env(outer));
    assert!(scope.heap().is_valid_string(a));
    assert!(scope.heap().is_valid_string(b));
  }

  Ok(())
}
