use vm_js::create_import_meta_object;
use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::ImportMetaProperty;
use vm_js::ModuleId;
use vm_js::PropertyKey;
use vm_js::Scope;
use vm_js::Value;
use vm_js::Vm;
use vm_js::VmError;
use vm_js::VmImportMetaHostHooks;
use vm_js::VmOptions;

#[derive(Debug)]
struct TestHooks {
  url_key: PropertyKey,
  url_value: Value,
  finalize_calls: u32,
}

impl VmImportMetaHostHooks for TestHooks {
  fn host_get_import_meta_properties(
    &mut self,
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _module: ModuleId,
  ) -> Result<Vec<ImportMetaProperty>, VmError> {
    Ok(vec![ImportMetaProperty {
      key: self.url_key,
      value: self.url_value,
    }])
  }

  fn host_finalize_import_meta(
    &mut self,
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _import_meta: vm_js::GcObject,
    _module: ModuleId,
  ) -> Result<(), VmError> {
    self.finalize_calls += 1;
    Ok(())
  }
}

#[test]
fn import_meta_hooks_are_called_and_object_is_spec_shaped() {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 512 * 1024));
  let mut scope = heap.scope();

  let url_key_s = scope.alloc_string("url").unwrap();
  scope.push_root(Value::String(url_key_s)).unwrap();
  let url_value_s = scope
    .alloc_string("https://example.invalid/module.js")
    .unwrap();
  scope.push_root(Value::String(url_value_s)).unwrap();

  let mut hooks = TestHooks {
    url_key: PropertyKey::from_string(url_key_s),
    url_value: Value::String(url_value_s),
    finalize_calls: 0,
  };

  let mut vm = Vm::new(VmOptions::default());

  let module = ModuleId::from_raw(1);
  let import_meta =
    create_import_meta_object(&mut vm, &mut scope, &mut hooks, module).unwrap();

  assert_eq!(scope.heap().object_prototype(import_meta).unwrap(), None);

  assert_eq!(
    scope
      .heap()
      .object_get_own_data_property_value(import_meta, &hooks.url_key)
      .unwrap(),
    Some(hooks.url_value)
  );

  assert_eq!(hooks.finalize_calls, 1);
}
