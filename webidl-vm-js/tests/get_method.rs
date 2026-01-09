use std::cell::Cell;
use vm_js::{
  Heap, HeapLimits, PropertyDescriptor, PropertyKey as VmPropertyKey, PropertyKind, Scope, Value, Vm, VmError,
  VmHostHooks, VmOptions,
};
use webidl::{InterfaceId, JsRuntime, PropertyKey, WebIdlHooks, WebIdlLimits};
use webidl_vm_js::VmJsWebIdlCx;

struct NoHooks;

impl WebIdlHooks<Value> for NoHooks {
  fn is_platform_object(&self, _value: Value) -> bool {
    false
  }

  fn implements_interface(&self, _value: Value, _interface: InterfaceId) -> bool {
    false
  }
}

thread_local! {
  static GETTER_CALLS: Cell<u32> = const { Cell::new(0) };
  static EXPECTED_THIS: Cell<Option<vm_js::GcObject>> = const { Cell::new(None) };
  static METHOD_FN: Cell<Option<vm_js::GcObject>> = const { Cell::new(None) };
}

fn method(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: vm_js::GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn getter(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHostHooks,
  _callee: vm_js::GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  GETTER_CALLS.with(|c| c.set(c.get() + 1));

  let expected = EXPECTED_THIS
    .with(|t| t.get())
    .expect("EXPECTED_THIS should be set");
  assert_eq!(this, Value::Object(expected));

  // Force a GC during the getter call to ensure `get_method` roots correctly.
  scope.heap_mut().collect_garbage();

  let method = METHOD_FN.with(|m| m.get()).expect("METHOD_FN should be set");
  Ok(Value::Object(method))
}

#[test]
fn get_method_invokes_getter_once() -> Result<(), VmError> {
  GETTER_CALLS.with(|c| c.set(0));

  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
  let hooks = NoHooks;
  let limits = WebIdlLimits::default();
  let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

  let method_id = cx.vm.register_native_call(method)?;
  let getter_id = cx.vm.register_native_call(getter)?;

  let method_name = cx.scope.alloc_string("m")?;
  let method_fn = cx
    .scope
    .alloc_native_function(method_id, None, method_name, 0)?;
  cx.scope.push_root(Value::Object(method_fn))?;
  METHOD_FN.with(|m| m.set(Some(method_fn)));

  let getter_name = cx.scope.alloc_string("get")?;
  let getter_fn = cx
    .scope
    .alloc_native_function(getter_id, None, getter_name, 0)?;
  cx.scope.push_root(Value::Object(getter_fn))?;

  let obj = cx.scope.alloc_object()?;
  cx.scope.push_root(Value::Object(obj))?;

  let key_s = cx.scope.alloc_string("m")?;
  let key = VmPropertyKey::from_string(key_s);
  let desc = PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Accessor {
      get: Value::Object(getter_fn),
      set: Value::Undefined,
    },
  };
  cx.scope.define_property(obj, key, desc)?;

  EXPECTED_THIS.with(|t| t.set(Some(obj)));
  let got = cx.get_method(obj, PropertyKey::String(key_s))?;
  assert_eq!(got, Some(Value::Object(method_fn)));
  assert_eq!(GETTER_CALLS.with(|c| c.get()), 1);
  Ok(())
}
