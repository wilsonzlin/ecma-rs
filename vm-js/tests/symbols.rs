use vm_js::{Heap, HeapLimits, Value, VmError};

#[test]
fn symbols_with_same_description_are_not_equal() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let desc = scope.alloc_string("desc")?;
  let a = scope.new_symbol(Some(desc))?;
  let b = scope.new_symbol(Some(desc))?;

  assert_ne!(a, b);
  Ok(())
}

#[test]
fn symbol_description_is_traced_through_gc() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let sym;
  let desc_string;
  let garbage;
  {
    let mut scope = heap.scope();

    garbage = scope.alloc_string("garbage")?;
    desc_string = scope.alloc_string("hello")?;
    sym = scope.new_symbol(Some(desc_string))?;
    scope.push_root(Value::Symbol(sym))?;

    scope.heap_mut().collect_garbage();

    // Ensure unrelated garbage was collected, but the description survived.
    assert!(!scope.heap().is_valid_string(garbage));
    assert!(scope.heap().is_valid_string(desc_string));

    let got_desc = scope
      .heap()
      .get_symbol_description(sym)?
      .expect("symbol should have a description");
    assert_eq!(scope.heap().get_string(got_desc)?.to_utf8_lossy(), "hello");
  }

  // Dropping the scope removes the stack root, allowing the symbol to be collected.
  heap.collect_garbage();
  assert!(!heap.is_valid_symbol(sym));

  Ok(())
}

#[test]
fn symbol_for_returns_same_symbol_for_same_key() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let sym;
  let key_b;

  {
    let mut scope = heap.scope();
    let key_a = scope.alloc_string("registry-key")?;
    key_b = scope.alloc_string("registry-key")?;

    let sym_a = scope.heap_mut().symbol_for(key_a)?;
    let sym_b = scope.heap_mut().symbol_for(key_b)?;
    assert_eq!(sym_a, sym_b);
    sym = sym_a;
  }

  // Ensure the global registry roots the symbol (and thus its description) even
  // when no explicit roots are provided.
  heap.collect_garbage();
  assert!(heap.is_valid_symbol(sym));
  assert!(!heap.is_valid_string(key_b));

  let desc = heap
    .get_symbol_description(sym)?
    .expect("Symbol.for() symbols should have descriptions");
  assert_eq!(heap.get_string(desc)?.to_utf8_lossy(), "registry-key");

  Ok(())
}
