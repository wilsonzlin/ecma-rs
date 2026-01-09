use std::collections::HashMap;

use vm_js::{
  finish_loading_imported_module, load_requested_modules, Heap, HeapLimits, HostDefined, ModuleCompletion,
  ImportAttribute, ModuleGraph, ModuleId, ModuleLoadPayload, ModuleLoaderHost, ModuleRequest, ModuleStatus,
  PromiseState, PropertyKey, PropertyKind, Realm, Scope, SourceTextModuleRecord, Value, Vm, VmError,
  VmOptions,
};

#[derive(Clone)]
enum PlannedLoad {
  Sync(ModuleCompletion),
  Async(ModuleCompletion),
}

struct PendingLoad {
  referrer: ModuleId,
  request: ModuleRequest,
  payload: ModuleLoadPayload,
  result: ModuleCompletion,
}

#[derive(Default)]
struct FakeHost {
  plan: HashMap<String, PlannedLoad>,
  pending: Vec<PendingLoad>,
}

impl FakeHost {
  fn plan_sync(&mut self, specifier: &str, result: ModuleCompletion) {
    self
      .plan
      .insert(specifier.to_string(), PlannedLoad::Sync(result));
  }

  fn plan_async(&mut self, specifier: &str, result: ModuleCompletion) {
    self
      .plan
      .insert(specifier.to_string(), PlannedLoad::Async(result));
  }

  fn complete_pending(
    &mut self,
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    modules: &mut ModuleGraph,
    index: usize,
  ) {
    let pending = self.pending.remove(index);
    finish_loading_imported_module(
      vm,
      scope,
      modules,
      self,
      pending.referrer,
      pending.request,
      pending.payload,
      pending.result,
    )
    .unwrap();
  }
}

impl ModuleLoaderHost for FakeHost {
  fn host_load_imported_module(
    &mut self,
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    modules: &mut ModuleGraph,
    referrer: ModuleId,
    request: ModuleRequest,
    _host_defined: HostDefined,
    payload: ModuleLoadPayload,
  ) -> Result<(), VmError> {
    let action = self
      .plan
      .get(request.specifier.as_str())
      .unwrap_or_else(|| panic!("unexpected module request {:?}", request.specifier))
      .clone();

    match action {
      PlannedLoad::Sync(result) => finish_loading_imported_module(
        vm,
        scope,
        modules,
        self,
        referrer,
        request,
        payload,
        result,
      ),
      PlannedLoad::Async(result) => {
        self.pending.push(PendingLoad {
          referrer,
          request,
          payload,
          result,
        });
        Ok(())
      }
    }
  }
}

fn req(specifier: &str) -> ModuleRequest {
  ModuleRequest::new(specifier, vec![])
}

fn req_with_attr(specifier: &str, key: &str, value: &str) -> ModuleRequest {
  ModuleRequest::new(specifier, vec![ImportAttribute::new(key, value)])
}

fn record(requested: Vec<ModuleRequest>) -> SourceTextModuleRecord {
  let mut record = SourceTextModuleRecord::default();
  record.requested_modules = requested;
  record
}

fn new_vm_and_heap() -> (Vm, Heap, Realm) {
  let mut vm = Vm::new(VmOptions::default());
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let realm = Realm::new(&mut vm, &mut heap).unwrap();
  (vm, heap, realm)
}

#[test]
fn simple_graph_resolves() {
  let mut modules = ModuleGraph::new();
  let b = modules.add_module(record(Vec::new()));
  let c = modules.add_module(record(Vec::new()));
  let a = modules.add_module(record(vec![req("B"), req("C")]));

  let (mut vm, mut heap, mut realm) = new_vm_and_heap();

  let mut host = FakeHost::default();
  host.plan_async("B", Ok(b));
  host.plan_async("C", Ok(c));

  {
    let mut scope = heap.scope();
    let promise =
      load_requested_modules(&mut vm, &mut scope, &mut modules, &mut host, a, HostDefined::default())
        .unwrap();
    scope.push_root(promise).unwrap();

    let Value::Object(promise_obj) = promise else {
      panic!("LoadRequestedModules should return a Promise object");
    };

    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Pending
    );
    assert_eq!(host.pending.len(), 2);

    // Complete out-of-order.
    host.complete_pending(&mut vm, &mut scope, &mut modules, 1);
    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Pending
    );
    host.complete_pending(&mut vm, &mut scope, &mut modules, 0);
    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Fulfilled
    );

    assert_eq!(modules.module(a).status, ModuleStatus::Unlinked);
    assert_eq!(modules.module(b).status, ModuleStatus::Unlinked);
    assert_eq!(modules.module(c).status, ModuleStatus::Unlinked);
  }

  realm.teardown(&mut heap);
}

#[test]
fn cycle_does_not_infinite_loop() {
  let mut modules = ModuleGraph::new();
  let a = modules.add_module(record(vec![req("B")]));
  let b = modules.add_module(record(vec![req("A")]));

  let (mut vm, mut heap, mut realm) = new_vm_and_heap();

  let mut host = FakeHost::default();
  host.plan_sync("A", Ok(a));
  host.plan_sync("B", Ok(b));

  {
    let mut scope = heap.scope();
    let promise =
      load_requested_modules(&mut vm, &mut scope, &mut modules, &mut host, a, HostDefined::default())
        .unwrap();
    scope.push_root(promise).unwrap();

    let Value::Object(promise_obj) = promise else {
      panic!("LoadRequestedModules should return a Promise object");
    };
    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Fulfilled
    );
    assert!(host.pending.is_empty());

    assert_eq!(modules.module(a).status, ModuleStatus::Unlinked);
    assert_eq!(modules.module(b).status, ModuleStatus::Unlinked);
  }

  realm.teardown(&mut heap);
}

#[test]
fn load_failure_rejects_and_freezes_state() {
  let mut modules = ModuleGraph::new();
  let b = modules.add_module(record(Vec::new()));
  let c = modules.add_module(record(Vec::new()));
  let a = modules.add_module(record(vec![req("B"), req("C")]));

  let (mut vm, mut heap, mut realm) = new_vm_and_heap();

  let mut host = FakeHost::default();
  host.plan_async("B", Ok(b));
  host.plan_sync("C", Err(VmError::Unimplemented("load failure")));

  {
    let mut scope = heap.scope();
    let promise =
      load_requested_modules(&mut vm, &mut scope, &mut modules, &mut host, a, HostDefined::default())
        .unwrap();
    scope.push_root(promise).unwrap();

    let Value::Object(promise_obj) = promise else {
      panic!("LoadRequestedModules should return a Promise object");
    };
    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Rejected
    );

    // Completion of unrelated outstanding loads should be ignored (no panics, no status changes).
    assert_eq!(host.pending.len(), 1);
    host.complete_pending(&mut vm, &mut scope, &mut modules, 0);
    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Rejected
    );

    assert_eq!(modules.module(a).status, ModuleStatus::New);
    assert_eq!(modules.module(b).status, ModuleStatus::New);
    assert_eq!(modules.module(c).status, ModuleStatus::New);
  }

  realm.teardown(&mut heap);
}

#[test]
fn unsupported_import_attributes_reject_with_syntax_error() {
  let mut modules = ModuleGraph::new();
  let b = modules.add_module(record(Vec::new()));
  let a = modules.add_module(record(vec![req_with_attr("B", "type", "json")]));

  let (mut vm, mut heap, mut realm) = new_vm_and_heap();
  let mut host = FakeHost::default();

  {
    let mut scope = heap.scope();
    let promise =
      load_requested_modules(&mut vm, &mut scope, &mut modules, &mut host, a, HostDefined::default())
        .unwrap();
    scope.push_root(promise).unwrap();

    let Value::Object(promise_obj) = promise else {
      panic!("LoadRequestedModules should return a Promise object");
    };

    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Rejected
    );
    assert!(host.pending.is_empty(), "host loader should not have been invoked");

    let Some(result) = scope.heap().promise_result(promise_obj).unwrap() else {
      panic!("expected rejected promise to have a result");
    };
    let Value::Object(err_obj) = result else {
      panic!("expected promise rejection result to be an object");
    };

    let name_key = PropertyKey::from_string(scope.alloc_string("name").unwrap());
    let Some(desc) = scope.heap().object_get_own_property(err_obj, &name_key).unwrap() else {
      panic!("expected SyntaxError object to have a 'name' property");
    };
    let PropertyKind::Data { value, .. } = desc.kind else {
      panic!("expected SyntaxError.name to be a data property");
    };
    let Value::String(name) = value else {
      panic!("expected SyntaxError.name to be a string");
    };
    assert_eq!(scope.heap().get_string(name).unwrap().to_utf8_lossy(), "SyntaxError");

    assert_eq!(modules.module(a).status, ModuleStatus::New);
    assert_eq!(modules.module(b).status, ModuleStatus::New);
  }

  realm.teardown(&mut heap);
}

struct HostSupportingType(FakeHost);

impl HostSupportingType {
  fn plan_sync(&mut self, specifier: &str, result: ModuleCompletion) {
    self.0.plan_sync(specifier, result);
  }
}

impl ModuleLoaderHost for HostSupportingType {
  fn host_load_imported_module(
    &mut self,
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    modules: &mut ModuleGraph,
    referrer: ModuleId,
    request: ModuleRequest,
    host_defined: HostDefined,
    payload: ModuleLoadPayload,
  ) -> Result<(), VmError> {
    self.0.host_load_imported_module(
      vm,
      scope,
      modules,
      referrer,
      request,
      host_defined,
      payload,
    )
  }

  fn host_get_supported_import_attributes(&self) -> &'static [&'static str] {
    static SUPPORTED: [&str; 1] = ["type"];
    &SUPPORTED
  }
}

#[test]
fn supported_import_attributes_allow_module_loading() {
  let mut modules = ModuleGraph::new();
  let b = modules.add_module(record(Vec::new()));
  let a = modules.add_module(record(vec![req_with_attr("B", "type", "json")]));

  let (mut vm, mut heap, mut realm) = new_vm_and_heap();

  let mut host = HostSupportingType(FakeHost::default());
  host.plan_sync("B", Ok(b));

  {
    let mut scope = heap.scope();
    let promise =
      load_requested_modules(&mut vm, &mut scope, &mut modules, &mut host, a, HostDefined::default())
        .unwrap();
    scope.push_root(promise).unwrap();

    let Value::Object(promise_obj) = promise else {
      panic!("LoadRequestedModules should return a Promise object");
    };
    assert_eq!(
      scope.heap().promise_state(promise_obj).unwrap(),
      PromiseState::Fulfilled
    );
    assert!(host.0.pending.is_empty());
  }

  realm.teardown(&mut heap);
}
