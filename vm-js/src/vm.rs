use crate::error::Termination;
use crate::error::TerminationReason;
use crate::error::VmError;
use crate::function::NativeConstructId;
use crate::function::NativeFunctionId;
use crate::interrupt::InterruptHandle;
use crate::interrupt::InterruptToken;
use crate::source::StackFrame;
use crate::Scope;
use crate::Value;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;

/// A native (host-implemented) function call handler.
pub type NativeCall =
  for<'a> fn(&mut Vm, &mut Scope<'a>, this: Value, args: &[Value]) -> Result<Value, VmError>;

/// A native (host-implemented) function constructor handler.
pub type NativeConstruct = for<'a> fn(
  &mut Vm,
  &mut Scope<'a>,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError>;

/// Construction-time VM options.
#[derive(Debug, Clone)]
pub struct VmOptions {
  pub max_stack_depth: usize,
  pub default_fuel: Option<u64>,
  pub default_deadline: Option<Duration>,
  pub check_time_every: u32,
  /// Optional shared interrupt flag to observe for cooperative cancellation.
  ///
  /// If provided, the VM will use this flag for its interrupt token so hosts can cancel execution
  /// by setting the flag to `true`.
  pub interrupt_flag: Option<Arc<AtomicBool>>,
}

impl Default for VmOptions {
  fn default() -> Self {
    Self {
      max_stack_depth: 1024,
      default_fuel: None,
      default_deadline: None,
      check_time_every: 100,
      interrupt_flag: None,
    }
  }
}

/// Per-run execution budget.
#[derive(Debug, Clone)]
pub struct Budget {
  pub fuel: Option<u64>,
  pub deadline: Option<Instant>,
  pub check_time_every: u32,
}

impl Budget {
  pub fn unlimited(check_time_every: u32) -> Self {
    Self {
      fuel: None,
      deadline: None,
      check_time_every,
    }
  }
}

#[derive(Debug, Clone)]
struct BudgetState {
  budget: Budget,
  ticks: u64,
}

impl BudgetState {
  fn new(budget: Budget) -> Self {
    Self { budget, ticks: 0 }
  }
}

/// VM execution state shell.
#[derive(Debug)]
pub struct Vm {
  options: VmOptions,
  interrupt: InterruptToken,
  interrupt_handle: InterruptHandle,
  budget: BudgetState,
  stack: Vec<StackFrame>,
  native_calls: Vec<NativeCall>,
  native_constructs: Vec<NativeConstruct>,
}

impl Vm {
  pub fn new(options: VmOptions) -> Self {
    let (interrupt, interrupt_handle) = match &options.interrupt_flag {
      Some(flag) => InterruptToken::from_shared_flag(flag.clone()),
      None => InterruptToken::new(),
    };
    let deadline = options
      .default_deadline
      .and_then(|duration| Instant::now().checked_add(duration));
    let budget = Budget {
      fuel: options.default_fuel,
      deadline,
      check_time_every: options.check_time_every,
    };

    Self {
      options,
      interrupt,
      interrupt_handle,
      budget: BudgetState::new(budget),
      stack: Vec::new(),
      native_calls: Vec::new(),
      native_constructs: Vec::new(),
    }
  }

  pub fn interrupt_handle(&self) -> InterruptHandle {
    self.interrupt_handle.clone()
  }

  pub fn set_budget(&mut self, budget: Budget) {
    self.budget = BudgetState::new(budget);
  }

  pub fn register_native_call(&mut self, f: NativeCall) -> NativeFunctionId {
    let idx = u32::try_from(self.native_calls.len())
      .expect("too many native call handlers registered");
    self.native_calls.push(f);
    NativeFunctionId(idx)
  }

  pub fn register_native_construct(&mut self, f: NativeConstruct) -> NativeConstructId {
    let idx = u32::try_from(self.native_constructs.len())
      .expect("too many native construct handlers registered");
    self.native_constructs.push(f);
    NativeConstructId(idx)
  }

  pub fn push_frame(&mut self, frame: StackFrame) -> Result<(), VmError> {
    if self.stack.len() >= self.options.max_stack_depth {
      return Err(self.terminate(TerminationReason::StackOverflow));
    }
    self.stack.push(frame);
    Ok(())
  }

  pub fn pop_frame(&mut self) {
    self.stack.pop();
  }

  pub fn capture_stack(&self) -> Vec<StackFrame> {
    self.stack.clone()
  }

  fn terminate(&self, reason: TerminationReason) -> VmError {
    VmError::Termination(Termination::new(reason, self.capture_stack()))
  }

  /// Consume one VM "tick": checks fuel/deadline/interrupt state.
  pub fn tick(&mut self) -> Result<(), VmError> {
    if let Some(fuel) = &mut self.budget.budget.fuel {
      if *fuel == 0 {
        return Err(self.terminate(TerminationReason::OutOfFuel));
      }
      *fuel -= 1;
    }

    self.budget.ticks = self.budget.ticks.wrapping_add(1);

    if self.interrupt.is_interrupted() {
      return Err(self.terminate(TerminationReason::Interrupted));
    }

    if let Some(deadline) = self.budget.budget.deadline {
      let interval = self.budget.budget.check_time_every.max(1) as u64;
      if self.budget.ticks % interval == 0 && Instant::now() >= deadline {
        return Err(self.terminate(TerminationReason::DeadlineExceeded));
      }
    }

    Ok(())
  }

  /// Calls `callee` with the provided `this` value and arguments.
  ///
  /// # Rooting
  ///
  /// The returned [`Value`] is **not automatically rooted**. If the caller will perform any
  /// additional allocations that could trigger GC, it must root the returned value itself (for
  /// example with [`Scope::push_root`]).
  ///
  /// This method roots `callee`, `this`, and `args` for the duration of the call using a temporary
  /// child [`Scope`].
  pub fn call(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let mut scope = scope.reborrow();
    scope.push_root(callee);
    scope.push_root(this);
    for arg in args {
      scope.push_root(*arg);
    }

    let callee_obj = match callee {
      Value::Object(obj) => obj,
      _ => return Err(VmError::NotCallable),
    };
    let call_id = { scope.heap().get_function_call_id(callee_obj)? };
    let f = self
      .native_calls
      .get(call_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native function id"))?;

    let result = f(self, &mut scope, this, args)?;
    Ok(result)
  }

  /// Constructs `callee` with the provided arguments and `new_target`.
  ///
  /// # Rooting
  ///
  /// The returned [`Value`] is **not automatically rooted**. If the caller will perform any
  /// additional allocations that could trigger GC, it must root the returned value itself (for
  /// example with [`Scope::push_root`]).
  ///
  /// This method roots `callee`, `new_target`, and `args` for the duration of construction using a
  /// temporary child [`Scope`].
  pub fn construct(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let mut scope = scope.reborrow();
    scope.push_root(callee);
    scope.push_root(new_target);
    for arg in args {
      scope.push_root(*arg);
    }

    let callee_obj = match callee {
      Value::Object(obj) => obj,
      _ => return Err(VmError::NotConstructable),
    };
    let construct_id = { scope.heap().get_function_construct_id(callee_obj)? }
      .ok_or(VmError::NotConstructable)?;
    let construct = self
      .native_constructs
      .get(construct_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native constructor id"))?;

    let result = construct(self, &mut scope, args, new_target)?;
    Ok(result)
  }
}
