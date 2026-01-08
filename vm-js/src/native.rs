use crate::function::{NativeConstructId, NativeFunctionId};
use crate::{GcString, Scope, Value, Vm, VmError};

/// A native/builtin `[[Call]]` entrypoint implemented in Rust.
///
/// # GC / rooting expectations
///
/// The caller must treat `this` and `args` as rooted for the duration of the call.
///
/// Native functions may allocate through [`Scope`]. If a native function needs to store `this` or
/// any element of `args` across an allocation (e.g. for later use), it must push a stack root via
/// [`Scope::push_root`] before allocating.
pub type NativeCallFn = for<'scope> fn(
  &mut Vm,
  &mut Scope<'scope>,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError>;

/// A native/builtin `[[Construct]]` entrypoint implemented in Rust.
///
/// See [`NativeCallFn`] for the GC/rooting expectations.
pub type NativeConstructFn = for<'scope> fn(
  &mut Vm,
  &mut Scope<'scope>,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError>;

/// Registry metadata for a Rust-implemented native function.
///
/// This record is intentionally GC-handle-free; callers can allocate `name` into the heap when
/// instantiating a function object.
#[derive(Clone, Copy)]
pub struct NativeFunctionMeta {
  pub name: &'static str,
  pub length: u32,
  pub call: NativeCallFn,
  pub construct: Option<NativeConstructFn>,
}

const TEST_CALL_META: NativeFunctionMeta = NativeFunctionMeta {
  name: "testCall",
  length: 0,
  call: native_test_call,
  construct: None,
};

const TEST_CONSTRUCT_META: NativeFunctionMeta = NativeFunctionMeta {
  name: "testConstruct",
  length: 2,
  call: native_test_call2,
  construct: Some(native_test_construct),
};

/// Returns the registry metadata for `id`.
pub fn native_function_meta(id: NativeFunctionId) -> Option<&'static NativeFunctionMeta> {
  match id.0 {
    0 => Some(&TEST_CALL_META),
    1 => Some(&TEST_CONSTRUCT_META),
    _ => None,
  }
}

/// Dispatches a native `[[Call]]` by id.
#[inline]
pub fn dispatch_native_call(
  id: NativeFunctionId,
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let Some(meta) = native_function_meta(id) else {
    return Err(VmError::Unimplemented("unknown native function id"));
  };
  (meta.call)(vm, scope, this, args)
}

/// Dispatches a native `[[Construct]]` by id.
pub fn dispatch_native_construct(
  id: NativeConstructId,
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let Some(meta) = native_function_meta(NativeFunctionId(id.0)) else {
    return Err(VmError::Unimplemented("unknown native construct id"));
  };
  match meta.construct {
    Some(f) => f(vm, scope, args, new_target),
    None => Err(VmError::Unimplemented(
      "native function has no [[Construct]] entrypoint",
    )),
  }
}

/// Returns the `[[Construct]]` id for `id` if the native function is constructable.
///
/// Today, `vm-js` uses the convention that a constructable native function's call and construct ids
/// are the same numeric value (wrapped in different newtypes). If a future embedding wants separate
/// id spaces, it can bypass this helper and use its own dispatch table.
pub fn native_construct_id(id: NativeFunctionId) -> Option<NativeConstructId> {
  native_function_meta(id).and_then(|meta| meta.construct.map(|_| NativeConstructId(id.0)))
}

/// Allocates the `name` string for a native function into the heap.
///
/// This helper exists so callers constructing function objects can keep the native function
/// registry free of GC handles.
#[inline]
pub fn alloc_native_function_name(
  scope: &mut Scope<'_>,
  id: NativeFunctionId,
) -> Result<GcString, VmError> {
  let Some(meta) = native_function_meta(id) else {
    return Err(VmError::Unimplemented("unknown native function id"));
  };
  scope.alloc_string(meta.name)
}

fn native_test_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(1.0))
}

fn native_test_call2(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Number(2.0))
}

fn native_test_construct(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  Ok(Value::Number(args.len() as f64))
}
