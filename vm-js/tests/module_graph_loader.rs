use std::collections::HashMap;

use vm_js::ModuleId;
use vm_js::VmError;
use vm_js::module_graph_loader::finish_loading_imported_module;
use vm_js::module_graph_loader::load_requested_modules;
use vm_js::module_graph_loader::CyclicModuleRecord;
use vm_js::module_graph_loader::HostDefined;
use vm_js::module_graph_loader::ModuleCompletion;
use vm_js::module_graph_loader::ModuleGraphLoadPromiseState;
use vm_js::module_graph_loader::ModuleLoadPayload;
use vm_js::module_graph_loader::ModuleLoaderHost;
use vm_js::module_graph_loader::ModuleRequest;
use vm_js::module_graph_loader::ModuleStatus;
use vm_js::module_graph_loader::ModuleStore;

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

  fn complete_pending(&mut self, modules: &mut ModuleStore, index: usize) {
    let pending = self.pending.remove(index);
    finish_loading_imported_module(
      modules,
      self,
      pending.referrer,
      pending.request,
      pending.payload,
      pending.result,
    );
  }
}

impl ModuleLoaderHost for FakeHost {
  fn host_load_imported_module(
    &mut self,
    modules: &mut ModuleStore,
    referrer: ModuleId,
    request: ModuleRequest,
    _host_defined: HostDefined,
    payload: ModuleLoadPayload,
  ) {
    let action = self
      .plan
      .get(request.specifier.as_str())
      .unwrap_or_else(|| panic!("unexpected module request {:?}", request.specifier))
      .clone();

    match action {
      PlannedLoad::Sync(result) => finish_loading_imported_module(
        modules,
        self,
        referrer,
        request,
        payload,
        result,
      ),
      PlannedLoad::Async(result) => self.pending.push(PendingLoad {
        referrer,
        request,
        payload,
        result,
      }),
    }
  }
}

#[test]
fn simple_graph_resolves() {
  let mut modules = ModuleStore::default();
  let b = modules
    .insert_cyclic(CyclicModuleRecord::new(Vec::new()))
    .unwrap();
  let c = modules
    .insert_cyclic(CyclicModuleRecord::new(Vec::new()))
    .unwrap();
  let a = modules.insert_cyclic(CyclicModuleRecord::new(vec![
    ModuleRequest::new("B", vec![]),
    ModuleRequest::new("C", vec![]),
  ]))
  .unwrap();

  let mut host = FakeHost::default();
  host.plan_async("B", Ok(b));
  host.plan_async("C", Ok(c));

  let promise = load_requested_modules(&mut modules, &mut host, a, HostDefined::default());
  assert_eq!(promise.state(), ModuleGraphLoadPromiseState::Pending);
  assert_eq!(host.pending.len(), 2);

  // Complete out-of-order.
  host.complete_pending(&mut modules, 1);
  assert_eq!(promise.state(), ModuleGraphLoadPromiseState::Pending);
  host.complete_pending(&mut modules, 0);
  assert_eq!(promise.state(), ModuleGraphLoadPromiseState::Fulfilled);

  assert_eq!(modules.get_cyclic(a).unwrap().status, ModuleStatus::Unlinked);
  assert_eq!(modules.get_cyclic(b).unwrap().status, ModuleStatus::Unlinked);
  assert_eq!(modules.get_cyclic(c).unwrap().status, ModuleStatus::Unlinked);
}

#[test]
fn cycle_does_not_infinite_loop() {
  let mut modules = ModuleStore::default();
  let a = modules
    .insert_cyclic(CyclicModuleRecord::new(vec![ModuleRequest::new("B", vec![])]))
    .unwrap();
  let b = modules
    .insert_cyclic(CyclicModuleRecord::new(vec![ModuleRequest::new("A", vec![])]))
    .unwrap();

  let mut host = FakeHost::default();
  host.plan_sync("A", Ok(a));
  host.plan_sync("B", Ok(b));

  let promise = load_requested_modules(&mut modules, &mut host, a, HostDefined::default());
  assert_eq!(promise.state(), ModuleGraphLoadPromiseState::Fulfilled);
  assert!(host.pending.is_empty());

  assert_eq!(modules.get_cyclic(a).unwrap().status, ModuleStatus::Unlinked);
  assert_eq!(modules.get_cyclic(b).unwrap().status, ModuleStatus::Unlinked);
}

#[test]
fn load_failure_rejects_and_freezes_state() {
  let mut modules = ModuleStore::default();
  let b = modules
    .insert_cyclic(CyclicModuleRecord::new(Vec::new()))
    .unwrap();
  let c = modules
    .insert_cyclic(CyclicModuleRecord::new(Vec::new()))
    .unwrap();
  let a = modules.insert_cyclic(CyclicModuleRecord::new(vec![
    ModuleRequest::new("B", vec![]),
    ModuleRequest::new("C", vec![]),
  ]))
  .unwrap();

  let mut host = FakeHost::default();
  host.plan_async("B", Ok(b));
  host.plan_sync("C", Err(VmError::Unimplemented("load failure")));

  let promise = load_requested_modules(&mut modules, &mut host, a, HostDefined::default());
  assert!(matches!(
    promise.state(),
    ModuleGraphLoadPromiseState::Rejected(_)
  ));

  // Completion of unrelated outstanding loads should be ignored (no panics, no status changes).
  assert_eq!(host.pending.len(), 1);
  host.complete_pending(&mut modules, 0);
  assert!(matches!(
    promise.state(),
    ModuleGraphLoadPromiseState::Rejected(_)
  ));

  assert_eq!(modules.get_cyclic(a).unwrap().status, ModuleStatus::New);
  assert_eq!(modules.get_cyclic(b).unwrap().status, ModuleStatus::New);
  assert_eq!(modules.get_cyclic(c).unwrap().status, ModuleStatus::New);
}
