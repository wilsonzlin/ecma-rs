use vm_js::{
  alloc_native_function_name, dispatch_native_call, dispatch_native_construct,
  native_function_meta, Heap, HeapLimits, NativeConstructId, NativeFunctionId, Value, Vm, VmError,
  VmOptions,
};

#[test]
fn registry_returns_correct_metadata() {
  let meta = native_function_meta(NativeFunctionId(0)).unwrap();
  assert_eq!(meta.name, "testCall");
  assert_eq!(meta.length, 0);
  assert!(meta.construct.is_none());

  let meta = native_function_meta(NativeFunctionId(1)).unwrap();
  assert_eq!(meta.name, "testConstruct");
  assert_eq!(meta.length, 2);
  assert!(meta.construct.is_some());
}

#[test]
fn dispatch_routes_to_rust_function() {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let out = dispatch_native_call(
    NativeFunctionId(0),
    &mut vm,
    &mut scope,
    Value::Undefined,
    &[],
  )
  .unwrap();
  assert_eq!(out, Value::Number(1.0));

  let out = dispatch_native_call(
    NativeFunctionId(1),
    &mut vm,
    &mut scope,
    Value::Null,
    &[],
  )
  .unwrap();
  assert_eq!(out, Value::Number(2.0));

  let out = dispatch_native_construct(
    NativeConstructId(1),
    &mut vm,
    &mut scope,
    &[Value::Undefined, Value::Null, Value::Bool(true)],
    Value::Undefined,
  )
  .unwrap();
  assert_eq!(out, Value::Number(3.0));

  let err = dispatch_native_construct(
    NativeConstructId(0),
    &mut vm,
    &mut scope,
    &[],
    Value::Undefined,
  )
  .unwrap_err();
  assert!(matches!(err, VmError::Unimplemented(_)));
}

#[test]
fn allocates_name_string() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut scope = heap.scope();

  let s = alloc_native_function_name(&mut scope, NativeFunctionId(0)).unwrap();
  let contents = scope.heap().get_string(s).unwrap();
  assert_eq!(contents.to_utf8_lossy(), "testCall");
}
