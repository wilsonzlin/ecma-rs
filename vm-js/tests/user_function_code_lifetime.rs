use std::sync::Arc;
use vm_js::{CompiledFunctionRef, CompiledScript, Heap, HeapLimits, Value, Vm, VmError, VmOptions};

#[test]
fn user_function_keeps_compiled_script_alive_and_releases_on_gc() -> Result<(), VmError> {
  let script = CompiledScript::compile_script("test.js", "function f() {}")?;

  let function_body = {
    let hir = script.hir.as_ref();
    hir.defs
      .iter()
      .filter_map(|def| def.body)
      .find_map(|body_id| {
        let idx = *hir.body_index.get(&body_id)?;
        let body = hir.bodies.get(idx)?;
        (body.kind == hir_js::BodyKind::Function).then_some(body_id)
      })
      .expect("expected at least one lowered function body")
  };

  let weak = Arc::downgrade(&script);

  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut vm = Vm::new(VmOptions::default());

  let func_obj;
  {
    let mut scope = heap.scope();
    let name = scope.alloc_string("f")?;
    func_obj = scope.alloc_user_function(
      CompiledFunctionRef {
        script,
        body: function_body,
      },
      name,
      0,
    )?;

    let root = scope.heap_mut().add_root(Value::Object(func_obj))?;
    assert!(weak.upgrade().is_some(), "function should keep script alive");

    match vm.call_without_host(&mut scope, Value::Object(func_obj), Value::Undefined, &[]) {
      Err(VmError::Unimplemented(msg)) => assert_eq!(msg, "user-defined function call"),
      other => panic!("expected unimplemented user-defined call, got {other:?}"),
    }

    scope.heap_mut().remove_root(root);
    scope.heap_mut().collect_garbage();
  }

  assert!(
    weak.upgrade().is_none(),
    "compiled script should be freed once function is collected"
  );
  assert!(
    !heap.is_valid_object(func_obj),
    "function object should be reclaimed by GC"
  );

  Ok(())
}
