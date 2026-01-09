use vm_js::{
  Heap, HeapLimits, ModuleGraph, PropertyKey, PropertyKind, Realm, SourceTextModuleRecord, Value,
  Vm, VmError, VmOptions,
};

#[test]
fn module_namespace_is_cached_and_spec_shaped() -> Result<(), VmError> {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut vm, &mut heap)?;

  let mut graph = ModuleGraph::new();
  let record = SourceTextModuleRecord::parse(
    r#"
      export const b = 1;
      export const a = 2;
    "#,
  )?;
  let module = graph.add_module(record);

  let mut scope = heap.scope();
  let ns1 = graph.get_module_namespace(module, &mut scope, &realm)?;
  let ns2 = graph.get_module_namespace(module, &mut scope, &realm)?;
  assert_eq!(ns1, ns2, "namespace object should be cached");

  let key = PropertyKey::Symbol(realm.well_known_symbols().to_string_tag);
  let desc = scope
    .heap()
    .object_get_own_property(ns1, &key)?
    .expect("%Symbol.toStringTag% should be defined");

  assert!(!desc.enumerable);
  assert!(!desc.configurable);
  match desc.kind {
    PropertyKind::Data {
      value: Value::String(s),
      writable,
    } => {
      assert!(!writable);
      assert_eq!(scope.heap().get_string(s)?.to_utf8_lossy(), "Module");
    }
    _ => panic!("%Symbol.toStringTag% must be a non-writable data property"),
  }

  assert_eq!(
    graph.module_namespace_exports(module).unwrap(),
    &["a".to_string(), "b".to_string()],
    "exports list should be sorted"
  );

  // Avoid leaking persistent roots (and tripping the Realm drop assertion).
  drop(scope);
  realm.teardown(&mut heap);
  Ok(())
}
