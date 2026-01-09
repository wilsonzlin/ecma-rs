use std::sync::atomic::AtomicBool;
use std::sync::atomic::Ordering;
use std::sync::Arc;
use std::thread;
use std::time::Duration;
use std::time::Instant;
use vm_js::Budget;
use vm_js::TerminationReason;
use vm_js::Vm;
use vm_js::VmError;
use vm_js::VmOptions;

#[test]
fn fuel_exhaustion_triggers_out_of_fuel_after_exact_tick_count() {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });

  vm.set_budget(Budget {
    fuel: Some(3),
    deadline: None,
    check_time_every: 1,
  });

  assert!(vm.tick().is_ok());
  assert!(vm.tick().is_ok());
  assert!(vm.tick().is_ok());

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::OutOfFuel),
    other => panic!("expected termination, got {other:?}"),
  }
}

#[test]
fn deadline_exhaustion_triggers_deadline_exceeded() {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });

  vm.set_budget(Budget {
    fuel: None,
    deadline: Some(Instant::now() - Duration::from_secs(1)),
    check_time_every: 1,
  });

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::DeadlineExceeded),
    other => panic!("expected termination, got {other:?}"),
  }
}

#[test]
fn interrupt_token_triggers_interrupted() {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });
  vm.set_budget(Budget::unlimited(1));

  let handle = vm.interrupt_handle();
  handle.interrupt();

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::Interrupted),
    other => panic!("expected termination, got {other:?}"),
  }
}

#[test]
fn shared_interrupt_flag_triggers_interrupted() {
  let flag = Arc::new(AtomicBool::new(false));
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: Some(flag.clone()),
  });
  vm.set_budget(Budget::unlimited(1));

  flag.store(true, Ordering::Relaxed);

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::Interrupted),
    other => panic!("expected termination, got {other:?}"),
  }
}

#[test]
fn shared_interrupt_flag_is_toggled_by_vm_interrupt_handle() {
  let flag = Arc::new(AtomicBool::new(false));
  let vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: Some(flag.clone()),
  });

  vm.interrupt_handle().interrupt();
  assert!(flag.load(Ordering::Relaxed));
}

#[test]
fn interrupt_handle_can_be_reset_to_reuse_vm() {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });
  vm.set_budget(Budget::unlimited(1));

  let handle = vm.interrupt_handle();
  handle.interrupt();

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::Interrupted),
    other => panic!("expected termination, got {other:?}"),
  }

  vm.reset_interrupt();
  assert!(vm.tick().is_ok());
}

#[test]
fn vm_reset_interrupt_clears_shared_interrupt_flag() {
  let flag = Arc::new(AtomicBool::new(false));
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: Some(flag.clone()),
  });
  vm.set_budget(Budget::unlimited(1));

  flag.store(true, Ordering::Relaxed);

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::Interrupted),
    other => panic!("expected termination, got {other:?}"),
  }

  vm.reset_interrupt();
  assert!(!flag.load(Ordering::Relaxed));
  assert!(vm.tick().is_ok());
}

#[test]
fn reset_budget_to_default_recomputes_deadline_relative_to_now() {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: Some(Duration::from_millis(50)),
    check_time_every: 1,
    interrupt_flag: None,
  });

  thread::sleep(Duration::from_millis(100));

  let err = vm.tick().unwrap_err();
  match err {
    VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::DeadlineExceeded),
    other => panic!("expected termination, got {other:?}"),
  }

  vm.reset_budget_to_default();
  assert!(vm.tick().is_ok());
}

#[test]
fn budget_guard_restores_previous_budget_state() {
  let mut vm = Vm::new(VmOptions {
    max_stack_depth: 16,
    default_fuel: None,
    default_deadline: None,
    check_time_every: 1,
    interrupt_flag: None,
  });

  vm.set_budget(Budget::unlimited(1));

  {
    let mut vm = vm.push_budget(Budget {
      fuel: Some(1),
      deadline: None,
      check_time_every: 1,
    });

    assert!(vm.tick().is_ok());

    let err = vm.tick().unwrap_err();
    match err {
      VmError::Termination(term) => assert_eq!(term.reason, TerminationReason::OutOfFuel),
      other => panic!("expected termination, got {other:?}"),
    }
  }

  assert!(vm.tick().is_ok());
}
