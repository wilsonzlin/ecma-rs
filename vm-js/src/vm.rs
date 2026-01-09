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
use std::{mem, ops};

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
  /// Default wall-clock execution budget applied when a VM budget is (re)initialized.
  ///
  /// Note: this is stored as a [`Duration`] and is converted into an [`Instant`] relative to the
  /// time the budget is initialized/reset (for example via [`Vm::reset_budget_to_default`]).
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

/// RAII guard returned by [`Vm::push_budget`].
///
/// Dropping the guard restores the previous VM budget state, including its tick counter.
pub struct BudgetGuard<'a> {
  vm: &'a mut Vm,
  previous: Option<BudgetState>,
}

impl<'a> ops::Deref for BudgetGuard<'a> {
  type Target = Vm;

  fn deref(&self) -> &Self::Target {
    &*self.vm
  }
}

impl<'a> ops::DerefMut for BudgetGuard<'a> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut *self.vm
  }
}

impl Drop for BudgetGuard<'_> {
  fn drop(&mut self) {
    if let Some(previous) = self.previous.take() {
      self.vm.budget = previous;
    }
  }
}

impl Vm {
  pub fn new(options: VmOptions) -> Self {
    let (interrupt, interrupt_handle) = match &options.interrupt_flag {
      Some(flag) => InterruptToken::from_shared_flag(flag.clone()),
      None => InterruptToken::new(),
    };
    let check_time_every = options.check_time_every;
    let mut vm = Self {
      options,
      interrupt,
      interrupt_handle,
      // Placeholder; immediately overwritten by `reset_budget_to_default`.
      budget: BudgetState::new(Budget::unlimited(check_time_every)),
      stack: Vec::new(),
      native_calls: Vec::new(),
      native_constructs: Vec::new(),
    };
    vm.reset_budget_to_default();
    vm
  }

  pub fn interrupt_handle(&self) -> InterruptHandle {
    self.interrupt_handle.clone()
  }

  pub fn set_budget(&mut self, budget: Budget) {
    self.budget = BudgetState::new(budget);
  }

  /// Reset this VM's execution budget to its construction defaults.
  ///
  /// This is intended for long-lived VM embeddings: call once per task/script/job to apply fresh
  /// fuel/deadline limits relative to "now".
  pub fn reset_budget_to_default(&mut self) {
    let deadline = self
      .options
      .default_deadline
      .and_then(|duration| Instant::now().checked_add(duration));
    let budget = Budget {
      fuel: self.options.default_fuel,
      deadline,
      check_time_every: self.options.check_time_every,
    };
    self.set_budget(budget);
  }

  /// Temporarily replace the VM budget, restoring the previous budget when the returned guard is
  /// dropped.
  ///
  /// The previous budget's tick counter is also restored on drop so nested budget scopes do not
  /// affect each other's deadline checking cadence.
  pub fn push_budget(&mut self, budget: Budget) -> BudgetGuard<'_> {
    let previous = mem::replace(&mut self.budget, BudgetState::new(budget));
    BudgetGuard {
      vm: self,
      previous: Some(previous),
    }
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

  fn dispatch_native_call(
    &mut self,
    call_id: NativeFunctionId,
    scope: &mut Scope<'_>,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let f = self
      .native_calls
      .get(call_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native function id"))?;
    f(self, scope, this, args)
  }

  fn dispatch_native_construct(
    &mut self,
    construct_id: NativeConstructId,
    scope: &mut Scope<'_>,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let construct = self
      .native_constructs
      .get(construct_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native constructor id"))?;
    construct(self, scope, args, new_target)
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
  ///
  /// ## Tick policy
  ///
  /// `Vm` itself does not prescribe what a tick means; ticks are an execution-engine-defined unit
  /// of work.
  ///
  /// The current AST evaluator (`exec.rs`) charges **one tick** at the start of every statement and
  /// expression evaluation. Additional ticks are charged in a few internal loops that may
  /// otherwise run without evaluating any statements/expressions (e.g. `for(;;){}` with an empty
  /// body), and when entering [`Vm::call`] / [`Vm::construct`].
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
  /// example with `scope.push_root(result)`.
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
    let callee = scope.push_root(callee);
    let this = scope.push_root(this);
    for &arg in args {
      scope.push_root(arg);
    }

    let callee_obj = match callee {
      Value::Object(obj) => obj,
      _ => return Err(VmError::NotCallable),
    };

    let call_id = scope.heap().get_function_call_id(callee_obj)?;
    let function_name = {
      let name = scope
        .heap()
        .get_string(scope.heap().get_function_name(callee_obj)?)?
        .to_utf8_lossy();
      Some(Arc::<str>::from(name))
    };
    let frame = StackFrame {
      function: function_name,
      source: Arc::<str>::from("<native>"),
      line: 0,
      col: 0,
    };

    self.push_frame(frame)?;
    let _guard = FrameGuard::new(self);
    // Budget/interrupt check for host-initiated calls that may not pass through the evaluator.
    self.tick()?;

    self.dispatch_native_call(call_id, &mut scope, this, args)
  }

  /// Constructs `callee` with the provided arguments and `new_target`.
  ///
  /// # Rooting
  ///
  /// The returned [`Value`] is **not automatically rooted**. If the caller will perform any
  /// additional allocations that could trigger GC, it must root the returned value itself (for
  /// example with `scope.push_root(result)`.
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
    let callee = scope.push_root(callee);
    let new_target = scope.push_root(new_target);
    for &arg in args {
      scope.push_root(arg);
    }

    let callee_obj = match callee {
      Value::Object(obj) => obj,
      _ => return Err(VmError::NotConstructable),
    };

    let Some(construct_id) = scope.heap().get_function_construct_id(callee_obj)? else {
      return Err(VmError::NotConstructable);
    };
    let function_name = {
      let name = scope
        .heap()
        .get_string(scope.heap().get_function_name(callee_obj)?)?
        .to_utf8_lossy();
      Some(Arc::<str>::from(name))
    };
    let frame = StackFrame {
      function: function_name,
      source: Arc::<str>::from("<native>"),
      line: 0,
      col: 0,
    };

    self.push_frame(frame)?;
    let _guard = FrameGuard::new(self);
    // Budget/interrupt check for host-initiated construction that may not pass through the
    // evaluator.
    self.tick()?;

    self.dispatch_native_construct(construct_id, &mut scope, args, new_target)
  }
}

struct FrameGuard {
  vm: *mut Vm,
}

impl FrameGuard {
  fn new(vm: &mut Vm) -> Self {
    Self { vm: vm as *mut Vm }
  }
}

impl Drop for FrameGuard {
  fn drop(&mut self) {
    unsafe { (&mut *self.vm).pop_frame() };
  }
}
