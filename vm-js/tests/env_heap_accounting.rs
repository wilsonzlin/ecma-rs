use semantic_js::js::SymbolId;
use vm_js::{EnvBinding, Heap, HeapLimits, Value, VmError};

#[test]
fn env_record_used_bytes_only_counts_binding_table_payload() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let used_before = scope.heap().used_bytes();
  let _empty = scope.alloc_env_record(None, &[])?;
  let used_after = scope.heap().used_bytes();
  assert_eq!(
    used_after, used_before,
    "empty env records should not contribute payload bytes"
  );

  let bindings = [
    EnvBinding {
      symbol: SymbolId::from_raw(1),
      name: None,
      value: Value::Number(1.0),
      mutable: true,
      initialized: true,
      strict: true,
    },
    EnvBinding {
      symbol: SymbolId::from_raw(2),
      name: None,
      value: Value::Number(2.0),
      mutable: true,
      initialized: true,
      strict: true,
    },
    EnvBinding {
      symbol: SymbolId::from_raw(3),
      name: None,
      value: Value::Number(3.0),
      mutable: true,
      initialized: true,
      strict: true,
    },
  ];

  let used_before = scope.heap().used_bytes();
  let _with_bindings = scope.alloc_env_record(None, &bindings)?;
  let used_after = scope.heap().used_bytes();

  let expected = bindings
    .len()
    .checked_mul(core::mem::size_of::<EnvBinding>())
    .unwrap_or(usize::MAX);
  assert_eq!(
    used_after.saturating_sub(used_before),
    expected,
    "env record payload bytes should match its binding table size"
  );

  Ok(())
}

