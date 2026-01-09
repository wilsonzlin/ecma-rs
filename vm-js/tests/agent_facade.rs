use vm_js::{Agent, Budget, Heap, HeapLimits, PersistentRoot, TerminationReason, Value, VmError, VmOptions};

fn new_agent() -> Agent {
  Agent::with_options(
    VmOptions::default(),
    HeapLimits::new(1024 * 1024, 1024 * 1024),
  )
  .expect("create agent")
}

#[test]
fn agent_can_be_created_and_dropped_without_leaking_realm_roots() {
  // If `Agent` forgets to teardown the realm, `Realm`'s drop assertion will trip in debug builds.
  let agent = new_agent();
  drop(agent);
}

#[test]
fn persistent_root_raii_releases_root() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

  // Allocate a string so we can prove the root keeps it alive across GC.
  let s = {
    let mut scope = heap.scope();
    scope.alloc_string("x")?
  };

  {
    let mut root = PersistentRoot::new(&mut heap, Value::String(s))?;
    root.heap_mut().collect_garbage();
    assert!(root.heap().is_valid_string(s));
  }

  heap.collect_garbage();
  assert!(!heap.is_valid_string(s));
  Ok(())
}

#[test]
fn run_script_restores_budget_after_success_and_termination() {
  let mut agent = new_agent();

  // Start with a non-default budget so we can detect whether `run_script` restores it.
  let initial = Budget {
    fuel: Some(123),
    deadline: None,
    check_time_every: 7,
  };
  agent.vm_mut().set_budget(initial.clone());

  let run_budget = Budget {
    fuel: Some(10),
    deadline: None,
    check_time_every: 1,
  };
  let value = agent
    .run_script("ok.js", "1", run_budget, None)
    .expect("script should run");
  assert_eq!(value, Value::Number(1.0));
  assert_eq!(agent.vm().budget(), initial);

  // Termination should also restore the prior budget.
  let term_budget = Budget {
    fuel: Some(0),
    deadline: None,
    check_time_every: 1,
  };
  let err = agent
    .run_script("fuel.js", "1", term_budget, None)
    .unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::OutOfFuel),
    other => panic!("expected termination, got {other:?}"),
  }
  assert_eq!(agent.vm().budget(), initial);
}
