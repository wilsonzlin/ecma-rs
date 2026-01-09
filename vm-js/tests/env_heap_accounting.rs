use vm_js::{Heap, HeapLimits, VmError};

#[test]
fn env_record_used_bytes_only_counts_binding_table_payload() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let used_before = scope.heap().used_bytes();
  let _env_obj = scope.alloc_env_record(None)?;
  let used_after = scope.heap().used_bytes();
  assert_eq!(
    used_after, used_before,
    "empty env records should not contribute payload bytes"
  );

  let used_before = scope.heap().used_bytes();
  let _env = scope.env_create(None)?;
  let used_after = scope.heap().used_bytes();
  assert_eq!(
    used_after, used_before,
    "empty env records should not contribute payload bytes"
  );

  Ok(())
}
