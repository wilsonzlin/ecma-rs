use vm_js::ExecutionContext;
use vm_js::ModuleId;
use vm_js::RealmId;
use vm_js::ScriptId;
use vm_js::ScriptOrModule;
use vm_js::Vm;
use vm_js::VmOptions;

#[test]
fn empty_stack_has_no_active_script_or_module() {
  let vm = Vm::new(VmOptions::default());
  assert_eq!(vm.get_active_script_or_module(), None);
  assert_eq!(vm.current_realm(), None);
}

#[test]
fn contexts_with_none_script_or_module_are_skipped() {
  let mut vm = Vm::new(VmOptions::default());
  vm.push_execution_context(ExecutionContext {
    realm: RealmId::from_raw(1),
    script_or_module: None,
  });
  assert_eq!(vm.get_active_script_or_module(), None);
  assert_eq!(vm.current_realm(), Some(RealmId::from_raw(1)));
}

#[test]
fn nesting_scans_past_none_contexts() {
  let mut vm = Vm::new(VmOptions::default());

  let script_id = ScriptId::from_raw(10);
  let module_id = ModuleId::from_raw(20);

  vm.push_execution_context(ExecutionContext {
    realm: RealmId::from_raw(1),
    script_or_module: Some(ScriptOrModule::Script(script_id)),
  });

  vm.push_execution_context(ExecutionContext {
    realm: RealmId::from_raw(2),
    script_or_module: None,
  });

  vm.push_execution_context(ExecutionContext {
    realm: RealmId::from_raw(3),
    script_or_module: Some(ScriptOrModule::Module(module_id)),
  });

  assert_eq!(
    vm.get_active_script_or_module(),
    Some(ScriptOrModule::Module(module_id))
  );
  assert_eq!(vm.current_realm(), Some(RealmId::from_raw(3)));

  vm.pop_execution_context();

  assert_eq!(
    vm.get_active_script_or_module(),
    Some(ScriptOrModule::Script(script_id))
  );
  assert_eq!(vm.current_realm(), Some(RealmId::from_raw(2)));
}

#[test]
fn current_realm_tracks_top_of_stack() {
  let mut vm = Vm::new(VmOptions::default());

  vm.push_execution_context(ExecutionContext {
    realm: RealmId::from_raw(1),
    script_or_module: None,
  });
  assert_eq!(vm.current_realm(), Some(RealmId::from_raw(1)));

  vm.push_execution_context(ExecutionContext {
    realm: RealmId::from_raw(2),
    script_or_module: None,
  });
  assert_eq!(vm.current_realm(), Some(RealmId::from_raw(2)));

  vm.pop_execution_context();
  assert_eq!(vm.current_realm(), Some(RealmId::from_raw(1)));

  vm.pop_execution_context();
  assert_eq!(vm.current_realm(), None);
}

#[test]
fn execution_context_guard_pops_on_drop() {
  let mut vm = Vm::new(VmOptions::default());

  {
    let guard = vm.execution_context_guard(ExecutionContext {
      realm: RealmId::from_raw(1),
      script_or_module: None,
    });
    assert_eq!(guard.current_realm(), Some(RealmId::from_raw(1)));
  }

  assert_eq!(vm.current_realm(), None);
}
