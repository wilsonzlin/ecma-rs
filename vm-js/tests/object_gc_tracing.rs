use vm_js::{Heap, HeapLimits, Value, VmError};

#[test]
fn object_prototype_tracing_keeps_prototype_alive() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  let proto;
  let child;
  let dead;
  {
    let mut scope = heap.scope();
    proto = scope.alloc_object()?;
    dead = scope.alloc_object()?;

    child = scope.alloc_object_with_properties(Some(proto), &[])?;
    scope.push_root(Value::Object(child))?;

    scope.heap_mut().collect_garbage();

    assert!(scope.heap().is_valid_object(child));
    assert!(
      scope.heap().is_valid_object(proto),
      "proto should survive via [[Prototype]]"
    );
    assert!(!scope.heap().is_valid_object(dead), "dead should be collected");
  }

  Ok(())
}
