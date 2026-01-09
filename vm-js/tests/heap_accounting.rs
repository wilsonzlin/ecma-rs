use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyKey, PropertyKind, Value, VmError,
};

#[test]
fn used_bytes_increases_when_adding_property() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  let desc = PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value: Value::Null,
      writable: true,
    },
  };

  let used_bytes_before = scope.heap().used_bytes();
  scope.define_property(obj, key, desc)?;
  let used_bytes_after = scope.heap().used_bytes();

  assert!(
    used_bytes_after > used_bytes_before,
    "expected used_bytes to increase after adding a new property (before={used_bytes_before}, after={used_bytes_after})"
  );
  Ok(())
}

#[test]
fn used_bytes_does_not_change_when_replacing_property() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let key = PropertyKey::from_string(scope.alloc_string("x")?);
  scope.define_property(
    obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Null,
        writable: true,
      },
    },
  )?;

  let used_bytes_before = scope.heap().used_bytes();
  scope.define_property(
    obj,
    key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Bool(true),
        writable: true,
      },
    },
  )?;
  let used_bytes_after = scope.heap().used_bytes();

  assert_eq!(
    used_bytes_after, used_bytes_before,
    "expected used_bytes unchanged when replacing an existing property"
  );
  Ok(())
}

#[test]
fn oom_limit_respected_after_growth() -> Result<(), VmError> {
  let max_bytes = 1024;
  let mut heap = Heap::new(HeapLimits::new(max_bytes, max_bytes / 2));
  let mut scope = heap.scope();

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;

  let mut saw_oom = false;
  for i in 0..10_000 {
    let key = match scope.alloc_string(&format!("k{i}")) {
      Ok(s) => PropertyKey::from_string(s),
      Err(VmError::OutOfMemory) => {
        saw_oom = true;
        break;
      }
      Err(e) => return Err(e),
    };

    let desc = PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Number(i as f64),
        writable: true,
      },
    };

    match scope.define_property(obj, key, desc) {
      Ok(()) => {}
      Err(VmError::OutOfMemory) => {
        saw_oom = true;
        break;
      }
      Err(e) => return Err(e),
    }
  }

  assert!(saw_oom, "expected heap growth to eventually hit VmError::OutOfMemory");
  let epsilon = 4096;
  assert!(
    scope.heap().estimated_total_bytes() <= max_bytes + epsilon,
    "heap.estimated_total_bytes should be bounded by max_bytes (max_bytes={max_bytes}, estimated_total_bytes={}, epsilon={epsilon})",
    scope.heap().estimated_total_bytes(),
  );
  Ok(())
}

#[test]
fn heap_limit_accounts_for_metadata_overhead() -> Result<(), VmError> {
  // A small limit: we should hit OOM due to heap metadata growth even though the allocated objects
  // have zero payload bytes.
  let max_bytes = 16 * 1024;
  let mut heap = Heap::new(HeapLimits::new(max_bytes, max_bytes / 2));
  let mut scope = heap.scope();

  let mut saw_oom = false;
  for _ in 0..1_000_000 {
    let obj = match scope.alloc_object() {
      Ok(obj) => obj,
      Err(VmError::OutOfMemory) => {
        saw_oom = true;
        break;
      }
      Err(e) => return Err(e),
    };

    match scope.push_root(Value::Object(obj)) {
      Ok(_) => {}
      Err(VmError::OutOfMemory) => {
        saw_oom = true;
        break;
      }
      Err(e) => return Err(e),
    }
  }

  assert!(saw_oom, "expected heap metadata growth to hit VmError::OutOfMemory");
  assert_eq!(
    scope.heap().used_bytes(),
    0,
    "empty objects should not contribute payload bytes"
  );

  let epsilon = 4096;
  assert!(
    scope.heap().estimated_total_bytes() <= max_bytes + epsilon,
    "heap.estimated_total_bytes should be bounded by max_bytes (max_bytes={max_bytes}, estimated_total_bytes={}, epsilon={epsilon})",
    scope.heap().estimated_total_bytes(),
  );
  Ok(())
}

#[test]
fn gc_frees_payload_bytes_and_allows_reallocation() -> Result<(), VmError> {
  let max_bytes = 64 * 1024;
  let mut heap = Heap::new(HeapLimits::new(max_bytes, max_bytes / 2));

  // Allocate an unrooted payload-heavy object (string). Dropping the scope should make it
  // unreachable so a GC cycle can reclaim its payload bytes.
  {
    let mut scope = heap.scope();
    let units = vec![0u16; 8 * 1024];
    scope.alloc_string_from_code_units(&units)?;
    assert!(scope.heap().used_bytes() > 0);
  }

  heap.collect_garbage();
  assert_eq!(heap.used_bytes(), 0);

  // The heap should allow further allocations after GC.
  {
    let mut scope = heap.scope();
    scope.alloc_string("hello")?;
  }

  Ok(())
}
