use crate::error::Termination;
use crate::error::TerminationReason;
use crate::error::VmError;
use crate::execution_context::ExecutionContext;
use crate::execution_context::ScriptOrModule;
use crate::function::{CallHandler, ConstructHandler, NativeConstructId, NativeFunctionId};
use crate::GcObject;
use crate::Heap;
use crate::interrupt::InterruptHandle;
use crate::interrupt::InterruptToken;
use crate::jobs::VmJobContext;
use crate::jobs::VmHostHooks;
use crate::microtasks::MicrotaskQueue;
use crate::RootId;
use crate::source::StackFrame;
use crate::Intrinsics;
use crate::PropertyKey;
use crate::RealmId;
use crate::Scope;
use crate::Value;
use std::collections::VecDeque;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;
use std::{mem, ops};

/// A native (host-implemented) function call handler.
pub type NativeCall =
  for<'a> fn(
    &mut Vm,
    &mut Scope<'a>,
    host: &mut dyn VmHostHooks,
    callee: GcObject,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError>;

/// A native (host-implemented) function constructor handler.
pub type NativeConstruct = for<'a> fn(
  &mut Vm,
  &mut Scope<'a>,
  host: &mut dyn VmHostHooks,
  callee: GcObject,
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
pub(crate) struct BudgetState {
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
  execution_context_stack: Vec<ExecutionContext>,
  native_calls: Vec<NativeCall>,
  native_constructs: Vec<NativeConstruct>,
  microtasks: MicrotaskQueue,
  // Per-realm intrinsic graph used by built-in native function implementations.
  //
  // For now `vm-js` assumes a single active realm per `Vm`. When multiple realms are supported,
  // this will likely become realm-indexed state.
  intrinsics: Option<Intrinsics>,
  #[cfg(test)]
  native_calls_len_override: Option<usize>,
  #[cfg(test)]
  native_constructs_len_override: Option<usize>,
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

/// RAII helper that pushes an [`ExecutionContext`] on creation and pops it on drop.
///
/// This is intended to prevent mismatched `push_execution_context` / `pop_execution_context`
/// sequences when running nested evaluator/host work.
#[derive(Debug)]
#[must_use = "dropping the guard pops the execution context; bind it to keep the context active"]
pub struct ExecutionContextGuard<'vm> {
  vm: &'vm mut Vm,
  ctx: ExecutionContext,
  expected_len: usize,
}

impl<'vm> ExecutionContextGuard<'vm> {
  fn new(vm: &'vm mut Vm, ctx: ExecutionContext) -> Self {
    vm.push_execution_context(ctx);
    let expected_len = vm.execution_context_stack.len();
    Self { vm, ctx, expected_len }
  }
}

impl ops::Deref for ExecutionContextGuard<'_> {
  type Target = Vm;

  fn deref(&self) -> &Self::Target {
    &*self.vm
  }
}

impl ops::DerefMut for ExecutionContextGuard<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut *self.vm
  }
}

impl Drop for ExecutionContextGuard<'_> {
  fn drop(&mut self) {
    debug_assert_eq!(
      self.vm.execution_context_stack.len(),
      self.expected_len,
      "ExecutionContextGuard dropped after stack length changed (did you manually pop?)"
    );
    let popped = self.vm.pop_execution_context();
    debug_assert_eq!(
      popped,
      Some(self.ctx),
      "ExecutionContextGuard popped a different execution context than it pushed"
    );
    debug_assert!(
      popped.is_some(),
      "ExecutionContextGuard dropped with empty execution context stack"
    );
  }
}

/// RAII helper that pushes a [`StackFrame`] on creation and pops it on drop.
///
/// This is intended to prevent mismatched `push_frame` / `pop_frame` sequences when running nested
/// evaluator/host work, and ensures VM stack frames are popped even when unwinding through `?`.
#[derive(Debug)]
pub struct VmFrameGuard<'vm> {
  vm: &'vm mut Vm,
  expected_len: usize,
}

impl<'vm> VmFrameGuard<'vm> {
  fn new(vm: &'vm mut Vm, frame: StackFrame) -> Result<Self, VmError> {
    vm.push_frame(frame)?;
    let expected_len = vm.stack.len();
    Ok(Self { vm, expected_len })
  }
}

impl ops::Deref for VmFrameGuard<'_> {
  type Target = Vm;

  fn deref(&self) -> &Self::Target {
    &*self.vm
  }
}

impl ops::DerefMut for VmFrameGuard<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut *self.vm
  }
}

impl Drop for VmFrameGuard<'_> {
  fn drop(&mut self) {
    debug_assert_eq!(
      self.vm.stack.len(),
      self.expected_len,
      "VmFrameGuard dropped after stack length changed (did you manually pop?)"
    );
    debug_assert!(
      !self.vm.stack.is_empty(),
      "VmFrameGuard dropped with empty VM stack"
    );
    self.vm.pop_frame();
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
      execution_context_stack: Vec::new(),
      native_calls: Vec::new(),
      native_constructs: Vec::new(),
      microtasks: MicrotaskQueue::new(),
      intrinsics: None,
      #[cfg(test)]
      native_calls_len_override: None,
      #[cfg(test)]
      native_constructs_len_override: None,
    };
    vm.reset_budget_to_default();
    vm
  }

  /// Returns the VM-owned microtask queue.
  ///
  /// Promise built-ins enqueue Promise jobs onto this queue.
  #[inline]
  pub fn microtask_queue(&self) -> &MicrotaskQueue {
    &self.microtasks
  }

  /// Borrows the VM-owned microtask queue mutably.
  #[inline]
  pub fn microtask_queue_mut(&mut self) -> &mut MicrotaskQueue {
    &mut self.microtasks
  }

  /// Performs a microtask checkpoint, draining the VM's microtask queue.
  pub fn perform_microtask_checkpoint(&mut self, heap: &mut Heap) -> Result<(), VmError> {
    struct Ctx<'a> {
      vm: &'a mut Vm,
      heap: &'a mut Heap,
    }

    impl VmJobContext for Ctx<'_> {
      fn call(
        &mut self,
        host: &mut dyn VmHostHooks,
        callee: Value,
        this: Value,
        args: &[Value],
      ) -> Result<Value, VmError> {
        let mut scope = self.heap.scope();
        self.vm.call_with_host(&mut scope, host, callee, this, args)
      }

      fn construct(
        &mut self,
        host: &mut dyn VmHostHooks,
        callee: Value,
        args: &[Value],
        new_target: Value,
      ) -> Result<Value, VmError> {
        let mut scope = self.heap.scope();
        self
          .vm
          .construct_with_host(&mut scope, host, callee, args, new_target)
      }

      fn add_root(&mut self, value: Value) -> Result<RootId, VmError> {
        self.heap.add_root(value)
      }

      fn remove_root(&mut self, id: RootId) {
        self.heap.remove_root(id)
      }
    }

    struct LocalHost {
      pending: VecDeque<(Option<RealmId>, crate::Job)>,
    }

    impl LocalHost {
      fn new() -> Self {
        Self {
          pending: VecDeque::new(),
        }
      }

      fn drain_into(&mut self, queue: &mut MicrotaskQueue) {
        while let Some((realm, job)) = self.pending.pop_front() {
          queue.enqueue_promise_job(job, realm);
        }
      }
    }

    impl VmHostHooks for LocalHost {
      fn host_enqueue_promise_job(&mut self, job: crate::Job, realm: Option<RealmId>) {
        self.pending.push_back((realm, job));
      }

      fn host_call_job_callback(
        &mut self,
        ctx: &mut dyn VmJobContext,
        callback: &crate::JobCallback,
        this_argument: Value,
        arguments: &[Value],
      ) -> Result<Value, VmError> {
        ctx.call(
          self,
          Value::Object(callback.callback_object()),
          this_argument,
          arguments,
        )
      }

      fn as_any_mut(&mut self) -> Option<&mut dyn std::any::Any> {
        Some(self)
      }
    }

    if !self.microtasks.begin_checkpoint() {
      return Ok(());
    }

    // Keep running jobs until the queue becomes empty, capturing the first error but continuing to
    // drain so we don't leak job roots on drop.
    let mut first_err: Option<VmError> = None;

    loop {
      let Some((_realm, job)) = self.microtasks.pop_front() else {
        break;
      };

      let mut ctx = Ctx { vm: self, heap };
      let mut host = LocalHost::new();

      let job_result = job.run(&mut ctx, &mut host);

      // Some job types may schedule new Promise jobs via `VmHostHooks`; enqueue them into the VM's
      // microtask queue before proceeding.
      host.drain_into(&mut ctx.vm.microtasks);

      if first_err.is_none() {
        if let Err(e) = job_result {
          first_err = Some(e);
        }
      }
    }

    self.microtasks.end_checkpoint();

    match first_err {
      None => Ok(()),
      Some(e) => Err(e),
    }
  }

  pub(crate) fn set_intrinsics(&mut self, intrinsics: Intrinsics) {
    self.intrinsics = Some(intrinsics);
  }

  /// Returns the VM's initialized intrinsics, if any.
  ///
  /// Intrinsics are installed when creating a [`crate::Realm`]. Some host operations (e.g. WebIDL
  /// conversions or native builtins) may require access to well-known symbols or prototypes, and
  /// should treat `None` as "realm not initialized".
  pub fn intrinsics(&self) -> Option<Intrinsics> {
    self.intrinsics
  }

  pub fn interrupt_handle(&self) -> InterruptHandle {
    self.interrupt_handle.clone()
  }

  /// Clear the interrupt flag back to `false`.
  pub fn reset_interrupt(&self) {
    self.interrupt_handle.reset();
  }

  /// Returns the current execution budget (including remaining fuel/deadline).
  #[inline]
  pub fn budget(&self) -> Budget {
    self.budget.budget.clone()
  }

  pub fn set_budget(&mut self, budget: Budget) {
    self.budget = BudgetState::new(budget);
  }

  pub(crate) fn swap_budget_state(&mut self, budget: Budget) -> BudgetState {
    mem::replace(&mut self.budget, BudgetState::new(budget))
  }

  pub(crate) fn restore_budget_state(&mut self, state: BudgetState) {
    self.budget = state;
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

  pub fn register_native_call(&mut self, f: NativeCall) -> Result<NativeFunctionId, VmError> {
    let len = self.native_calls.len();
    #[cfg(test)]
    let len = self.native_calls_len_override.unwrap_or(len);
    let idx = u32::try_from(len)
      .map_err(|_| VmError::LimitExceeded("too many native call handlers registered"))?;

    // Fallible growth so hostile/buggy embeddings can't abort the process on allocator OOM.
    self
      .native_calls
      .try_reserve(1)
      .map_err(|_| VmError::OutOfMemory)?;
    self.native_calls.push(f);
    Ok(NativeFunctionId(idx))
  }

  pub fn register_native_construct(
    &mut self,
    f: NativeConstruct,
  ) -> Result<NativeConstructId, VmError> {
    let len = self.native_constructs.len();
    #[cfg(test)]
    let len = self.native_constructs_len_override.unwrap_or(len);
    let idx = u32::try_from(len)
      .map_err(|_| VmError::LimitExceeded("too many native construct handlers registered"))?;

    self
      .native_constructs
      .try_reserve(1)
      .map_err(|_| VmError::OutOfMemory)?;
    self.native_constructs.push(f);
    Ok(NativeConstructId(idx))
  }

  fn dispatch_native_call(
    &mut self,
    call_id: NativeFunctionId,
    scope: &mut Scope<'_>,
    host: &mut dyn VmHostHooks,
    callee: GcObject,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let f = self
      .native_calls
      .get(call_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native function id"))?;
    f(self, scope, host, callee, this, args)
  }

  fn dispatch_native_construct(
    &mut self,
    construct_id: NativeConstructId,
    scope: &mut Scope<'_>,
    host: &mut dyn VmHostHooks,
    callee: GcObject,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let construct = self
      .native_constructs
      .get(construct_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native constructor id"))?;
    construct(self, scope, host, callee, args, new_target)
  }

  /// Pushes a stack frame and returns an RAII guard that will pop it on drop.
  pub fn enter_frame(&mut self, frame: StackFrame) -> Result<VmFrameGuard<'_>, VmError> {
    VmFrameGuard::new(self, frame)
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

  /// Pushes an [`ExecutionContext`] onto the execution context stack.
  pub fn push_execution_context(&mut self, ctx: ExecutionContext) {
    self.execution_context_stack.push(ctx);
  }

  /// Pops the top [`ExecutionContext`] from the execution context stack.
  pub fn pop_execution_context(&mut self) -> Option<ExecutionContext> {
    self.execution_context_stack.pop()
  }

  /// Pushes an [`ExecutionContext`] and returns an RAII guard that will pop it on drop.
  pub fn execution_context_guard(&mut self, ctx: ExecutionContext) -> ExecutionContextGuard<'_> {
    ExecutionContextGuard::new(self, ctx)
  }

  /// Returns the active script or module, if any.
  ///
  /// This implements ECMA-262's
  /// [`GetActiveScriptOrModule`](https://tc39.es/ecma262/#sec-getactivescriptormodule) abstract
  /// operation.
  ///
  /// FastRender also vendors an offline copy of the spec at:
  /// [`specs/tc39-ecma262/spec.html#sec-getactivescriptormodule`](specs/tc39-ecma262/spec.html#sec-getactivescriptormodule)
  ///
  /// The scan skips execution contexts whose `script_or_module` is `None` (for example, host work
  /// such as Promise jobs or embedder callbacks).
  ///
  /// This will be used by module features such as `import.meta` and dynamic `import()` once the
  /// module system is implemented.
  pub fn get_active_script_or_module(&self) -> Option<ScriptOrModule> {
    self
      .execution_context_stack
      .iter()
      .rev()
      .find_map(|ctx| ctx.script_or_module)
  }

  /// Returns the realm of the currently-running execution context, if any.
  pub fn current_realm(&self) -> Option<RealmId> {
    self.execution_context_stack.last().map(|ctx| ctx.realm)
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
    // `call_with_host` requires `&mut self` plus an independent `&mut host`, but `Vm` stores a
    // default microtask queue inside itself. Temporarily move it out so it can serve as the host
    // hook implementation for this call.
    let mut host = mem::take(&mut self.microtasks);
    let result = self.call_with_host(scope, &mut host, callee, this, args);
    self.microtasks = host;
    result
  }

  /// Calls `callee` with the provided `this` value and arguments, using a custom host hook
  /// implementation.
  pub fn call_with_host(
    &mut self,
    scope: &mut Scope<'_>,
    host: &mut dyn VmHostHooks,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let mut scope = scope.reborrow();
    // Root all inputs in a way that is robust against GC triggering while we grow the root stack.
    //
    // `push_root`/`push_roots` can trigger GC when growing `root_stack`, so ensure any not-yet-pushed
    // values are treated as extra roots during that operation.
    let roots = [callee, this];
    scope.push_roots_with_extra_roots(&roots, args, &[])?;
    scope.push_roots(args)?;

    let callee_obj = match callee {
      Value::Object(obj) => obj,
      _ => return Err(VmError::NotCallable),
    };

    // Bound function dispatch: if the callee has `[[BoundTargetFunction]]`, forward the call to
    // the target with the bound `this` and arguments.
    if let Ok(func) = scope.heap().get_function(callee_obj) {
      if let Some(bound_target) = func.bound_target {
        let bound_this = func.bound_this.unwrap_or(Value::Undefined);
        let bound_args = func.bound_args.as_deref().unwrap_or(&[]);

        let total_len = bound_args
          .len()
          .checked_add(args.len())
          .ok_or(VmError::OutOfMemory)?;
        let mut combined: Vec<Value> = Vec::new();
        combined
          .try_reserve_exact(total_len)
          .map_err(|_| VmError::OutOfMemory)?;
        combined.extend_from_slice(bound_args);
        combined.extend_from_slice(args);

        return self.call(&mut scope, Value::Object(bound_target), bound_this, &combined);
      }
    }
    let call_handler = scope.heap().get_function_call_handler(callee_obj)?;

    let function_name = scope
      .heap()
      .get_function_name(callee_obj)
      .ok()
      .and_then(|name| scope.heap().get_string(name).ok())
      .map(|name| name.to_utf8_lossy())
      .filter(|name| !name.is_empty())
      .map(Arc::<str>::from);

    let source = match call_handler {
      CallHandler::Native(_) => Arc::<str>::from("<native>"),
      CallHandler::Ecma(_) => Arc::<str>::from("<call>"),
    };
    let frame = StackFrame {
      function: function_name,
      source,
      line: 0,
      col: 0,
    };

    let mut vm = self.enter_frame(frame)?;
    // Budget/interrupt check for host-initiated calls that may not pass through the evaluator.
    vm.tick()?;

    match call_handler {
      CallHandler::Native(call_id) => {
        vm.dispatch_native_call(call_id, &mut scope, host, callee_obj, this, args)
      }
      CallHandler::Ecma(_) => vm.call_ecma_function(&mut scope, callee_obj, this, args),
    }
  }

  /// ECMAScript `Get(O, P)` for ordinary objects.
  pub fn get(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    key: PropertyKey,
  ) -> Result<Value, VmError> {
    // Delegate to the ordinary object internal-method implementation. `Get(O, P)` uses
    // `receiver = O`.
    scope.ordinary_get(self, obj, key, Value::Object(obj))
  }

  /// ECMAScript `GetMethod(O, P)` for ordinary objects.
  pub fn get_method(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    key: PropertyKey,
  ) -> Result<Option<Value>, VmError> {
    let value = self.get(scope, obj, key)?;
    if matches!(value, Value::Undefined | Value::Null) {
      return Ok(None);
    }

    let Value::Object(func) = value else {
      return Err(VmError::NotCallable);
    };
    // Validate callability. `get_function_call_handler` returns `VmError::NotCallable` if not
    // callable.
    let _ = scope.heap().get_function_call_handler(func)?;
    Ok(Some(value))
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
    let mut host = mem::take(&mut self.microtasks);
    let result = self.construct_with_host(scope, &mut host, callee, args, new_target);
    self.microtasks = host;
    result
  }

  /// Constructs `callee` with the provided arguments and `new_target`, using a custom host hook
  /// implementation.
  pub fn construct_with_host(
    &mut self,
    scope: &mut Scope<'_>,
    host: &mut dyn VmHostHooks,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let mut scope = scope.reborrow();
    // Root all inputs robustly; see `Vm::call` for rationale.
    let roots = [callee, new_target];
    scope.push_roots_with_extra_roots(&roots, args, &[])?;
    scope.push_roots(args)?;

    let callee_obj = match callee {
      Value::Object(obj) => obj,
      _ => return Err(VmError::NotConstructable),
    };

    // Bound function dispatch: if the callee has `[[BoundTargetFunction]]`, forward construction to
    // the target with concatenated arguments.
    if let Ok(func) = scope.heap().get_function(callee_obj) {
      if let Some(bound_target) = func.bound_target {
        let bound_args = func.bound_args.as_deref().unwrap_or(&[]);

        let total_len = bound_args
          .len()
          .checked_add(args.len())
          .ok_or(VmError::OutOfMemory)?;
        let mut combined: Vec<Value> = Vec::new();
        combined
          .try_reserve_exact(total_len)
          .map_err(|_| VmError::OutOfMemory)?;
        combined.extend_from_slice(bound_args);
        combined.extend_from_slice(args);

        return self.construct(&mut scope, Value::Object(bound_target), &combined, new_target);
      }
    }
    let construct_handler = scope
      .heap()
      .get_function_construct_handler(callee_obj)?
      .ok_or(VmError::NotConstructable)?;

    let function_name = scope
      .heap()
      .get_function_name(callee_obj)
      .ok()
      .and_then(|name| scope.heap().get_string(name).ok())
      .map(|name| name.to_utf8_lossy())
      .filter(|name| !name.is_empty())
      .map(Arc::<str>::from);

    let source = match construct_handler {
      ConstructHandler::Native(_) => Arc::<str>::from("<native>"),
      ConstructHandler::Ecma(_) => Arc::<str>::from("<call>"),
    };
    let frame = StackFrame {
      function: function_name,
      source,
      line: 0,
      col: 0,
    };

    let mut vm = self.enter_frame(frame)?;
    // Budget/interrupt check for host-initiated construction that may not pass through the
    // evaluator.
    vm.tick()?;

    match construct_handler {
      ConstructHandler::Native(construct_id) => {
        vm.dispatch_native_construct(construct_id, &mut scope, host, callee_obj, args, new_target)
      }
      ConstructHandler::Ecma(_) => {
        vm.construct_ecma_function(&mut scope, callee_obj, args, new_target)
      }
    }
  }

  fn call_ecma_function(
    &mut self,
    _scope: &mut Scope<'_>,
    _callee: crate::GcObject,
    _this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented(
      "calling ECMAScript functions (interpreter/bytecode not wired yet)",
    ))
  }

  fn construct_ecma_function(
    &mut self,
    _scope: &mut Scope<'_>,
    _callee: crate::GcObject,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented(
      "constructing ECMAScript functions (interpreter/bytecode not wired yet)",
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn noop_call(
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _host: &mut dyn VmHostHooks,
    _callee: GcObject,
    _this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    Ok(Value::Undefined)
  }

  fn noop_construct(
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _host: &mut dyn VmHostHooks,
    _callee: GcObject,
    _args: &[Value],
    _new_target: Value,
  ) -> Result<Value, VmError> {
    Ok(Value::Undefined)
  }

  #[test]
  fn registering_too_many_native_handlers_returns_error_instead_of_panicking() {
    // Only meaningful on platforms where `usize` can exceed `u32::MAX`.
    if usize::BITS <= 32 {
      return;
    }

    let mut vm = Vm::new(VmOptions::default());
    // Avoid allocating huge vectors; this only affects the `u32::try_from(len)` conversion.
    vm.native_calls_len_override = Some((u32::MAX as usize) + 1);
    vm.native_constructs_len_override = Some((u32::MAX as usize) + 1);

    let err = vm.register_native_call(noop_call).unwrap_err();
    assert!(matches!(err, VmError::LimitExceeded(_)));

    let err = vm.register_native_construct(noop_construct).unwrap_err();
    assert!(matches!(err, VmError::LimitExceeded(_)));

    // Ensure no handlers were recorded.
    assert_eq!(vm.native_calls.len(), 0);
    assert_eq!(vm.native_constructs.len(), 0);
  }
}
