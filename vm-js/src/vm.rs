use crate::error::Termination;
use crate::error::TerminationReason;
use crate::error::VmError;
use crate::exec::RuntimeEnv;
use crate::execution_context::ExecutionContext;
use crate::execution_context::ScriptOrModule;
use crate::function::{
  CallHandler, ConstructHandler, EcmaFunctionId, NativeConstructId, NativeFunctionId, ThisMode,
};
use crate::interrupt::InterruptHandle;
use crate::interrupt::InterruptToken;
use crate::jobs::VmHost;
use crate::jobs::VmHostHooks;
use crate::jobs::VmJobContext;
use crate::microtasks::MicrotaskQueue;
use crate::source::SourceText;
use crate::source::StackFrame;
use crate::EnvRootId;
use crate::GcEnv;
use crate::GcObject;
use crate::Heap;
use crate::Intrinsics;
use crate::PropertyKey;
use crate::Realm;
use crate::RealmId;
use crate::RootId;
use crate::Scope;
use crate::Value;
use parse_js::ast::func::Func;
use parse_js::ast::node::Node;
use parse_js::ast::stx::TopLevel;
use std::any::Any;
use std::collections::{HashMap, VecDeque};
use std::ptr::NonNull;
use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;
use std::time::Instant;
use std::{mem, ops};

/// A native (host-implemented) function call handler.
pub type NativeCall = for<'a> fn(
  &mut Vm,
  &mut Scope<'a>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError>;

/// A native (host-implemented) function constructor handler.
pub type NativeConstruct = for<'a> fn(
  &mut Vm,
  &mut Scope<'a>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError>;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum EcmaFunctionKind {
  /// A `function f() {}` declaration statement.
  Decl,
  /// A function or arrow function expression (`function() {}` / `() => {}`).
  Expr,
  /// An object literal method/getter/setter definition (e.g. `f() {}` / `get x() {}`).
  ObjectMember,
}

/// Owns a parsed program AST (classic script or `eval` input).
///
/// Function objects retain an [`Arc`] of this so their bodies stay valid after the originating
/// `exec_script` / `eval` returns. Call-time re-parsing of source snippets is intentionally
/// avoided: a top-level re-parse would lose function-code context (`new.target`, `super`,
/// strictness) that the original tree already has.
#[derive(Debug)]
pub(crate) struct ParsedProgram {
  pub(crate) top: Node<TopLevel>,
}

#[derive(Debug)]
pub(crate) struct EcmaFunctionCode {
  pub(crate) source: Arc<SourceText>,
  /// Inclusive start of the function's source span (cache key / diagnostics).
  pub(crate) span_start: u32,
  /// Exclusive end of the function's source span (cache key / diagnostics).
  #[allow(dead_code)]
  pub(crate) span_end: u32,
  /// Declaration shape used in the registration cache key.
  #[allow(dead_code)]
  pub(crate) kind: EcmaFunctionKind,
  /// Always `0` for retained ASTs: `Loc` values are absolute offsets in [`Self::source`].
  /// Kept so call sites can keep passing a uniform `(base_offset, prefix_len)` pair into
  /// `run_ecma_function` (historically non-zero when snippets were re-parsed with wraps).
  #[allow(dead_code)]
  pub(crate) prefix_len: u32,
  /// Keeps [`Self::func`] valid for the lifetime of this code entry.
  program: Arc<ParsedProgram>,
  /// Points into [`Self::program`]'s tree (the `Node<Func>` registered at closure creation).
  func: NonNull<Node<Func>>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct EcmaFunctionKey {
  source: *const SourceText,
  span_start: u32,
  span_end: u32,
  kind: EcmaFunctionKind,
}

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
pub struct Vm {
  options: VmOptions,
  interrupt: InterruptToken,
  interrupt_handle: InterruptHandle,
  budget: BudgetState,
  stack: Vec<StackFrame>,
  execution_context_stack: Vec<ExecutionContext>,
  native_calls: Vec<NativeCall>,
  native_constructs: Vec<NativeConstruct>,
  /// Optional host/embedding state associated with this VM.
  ///
  /// Native (host-implemented) call/construct handlers are expected to downcast this to their
  /// embedding-specific type via [`Vm::user_data`] / [`Vm::user_data_mut`].
  user_data: Option<Box<dyn Any>>,
  microtasks: MicrotaskQueue,
  /// Optional host hook override used by embedding entry points such as
  /// [`crate::JsRuntime::exec_script_source_with_host`].
  ///
  /// When set, [`Vm::call`] / [`Vm::construct`] will route through this host hook implementation
  /// instead of the VM-owned [`MicrotaskQueue`].
  ///
  /// ## Safety contract
  ///
  /// This raw pointer is written by:
  /// - [`Vm::with_host_hooks_override`]
  /// - [`Vm::push_active_host_hooks`] / [`Vm::pop_active_host_hooks`]
  /// - [`Vm::call_with_host`] / [`Vm::construct_with_host`] (for the duration of the call)
  ///
  /// Each of these APIs borrows the host hook implementation mutably for the duration in which the
  /// pointer may be dereferenced, and treats it as a reborrow of the original `&mut dyn
  /// VmHostHooks`.
  host_hooks_override: Option<*mut (dyn VmHostHooks + 'static)>,
  ecma_functions: Vec<EcmaFunctionCode>,
  ecma_function_cache: HashMap<EcmaFunctionKey, EcmaFunctionId>,
  /// Stack of parsed programs currently being evaluated (script / `eval` / function body).
  ///
  /// [`Vm::register_ecma_function`] captures the top entry together with a pointer into that
  /// program's AST so call-time execution does not re-parse.
  program_stack: Vec<Arc<ParsedProgram>>,
  // Active-realm intrinsic graph used by built-in native function implementations.
  //
  // Secondary realms created via `$262.createRealm` (or [`Vm::create_realm`]) keep their own
  // [`Intrinsics`] in [`Vm::realm_table`]; switch the active set when entering foreign-realm
  // `eval` / jobs.
  intrinsics: Option<Intrinsics>,
  /// Per-global-object realm records (primary + `$262.createRealm` secondaries).
  realm_table: HashMap<u64, RealmTableEntry>,
  /// Owned secondary realms (teardown on [`crate::JsRuntime`] drop).
  secondary_realms: Vec<Realm>,
  #[cfg(test)]
  native_calls_len_override: Option<usize>,
  #[cfg(test)]
  native_constructs_len_override: Option<usize>,
}

/// Lookup record for a realm keyed by its global object's [`HeapId`](crate::HeapId) bits.
#[derive(Debug, Clone, Copy)]
pub(crate) struct RealmTableEntry {
  pub global: GcObject,
  pub id: RealmId,
  pub intrinsics: Intrinsics,
  pub global_lexical_env: GcEnv,
  /// Persistent root for `global_lexical_env` when this entry owns it (secondary realms).
  pub global_lex_root: Option<EnvRootId>,
}

impl std::fmt::Debug for Vm {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    let mut ds = f.debug_struct("Vm");
    ds.field("options", &self.options);
    ds.field("interrupt", &self.interrupt);
    ds.field("interrupt_handle", &self.interrupt_handle);
    ds.field("budget", &self.budget);
    ds.field("stack", &self.stack);
    ds.field("execution_context_stack", &self.execution_context_stack);
    ds.field("native_calls", &self.native_calls.len());
    ds.field("native_constructs", &self.native_constructs.len());
    ds.field("user_data", &self.user_data.as_ref().map(|_| "<opaque>"));
    ds.field("microtasks", &self.microtasks);
    ds.field("host_hooks_override", &self.host_hooks_override.is_some());
    ds.field("ecma_functions", &self.ecma_functions.len());
    ds.field("ecma_function_cache", &self.ecma_function_cache.len());
    ds.field("program_stack", &self.program_stack.len());
    ds.field("intrinsics", &self.intrinsics);
    ds.field("realm_table", &self.realm_table.len());
    ds.field("secondary_realms", &self.secondary_realms.len());
    #[cfg(test)]
    {
      ds.field("native_calls_len_override", &self.native_calls_len_override);
      ds.field(
        "native_constructs_len_override",
        &self.native_constructs_len_override,
      );
    }
    ds.finish()
  }
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
    Self {
      vm,
      ctx,
      expected_len,
    }
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

/// RAII helper that pushes a [`ParsedProgram`] on creation and pops it on drop.
#[derive(Debug)]
#[must_use = "dropping the guard pops the parsed program; bind it to keep the program active"]
pub(crate) struct ProgramGuard<'vm> {
  vm: &'vm mut Vm,
  expected_len: usize,
}

impl<'vm> ProgramGuard<'vm> {
  fn new(vm: &'vm mut Vm, program: Arc<ParsedProgram>) -> Self {
    vm.program_stack.push(program);
    let expected_len = vm.program_stack.len();
    Self { vm, expected_len }
  }
}

impl ops::Deref for ProgramGuard<'_> {
  type Target = Vm;

  fn deref(&self) -> &Self::Target {
    &*self.vm
  }
}

impl ops::DerefMut for ProgramGuard<'_> {
  fn deref_mut(&mut self) -> &mut Self::Target {
    &mut *self.vm
  }
}

impl Drop for ProgramGuard<'_> {
  fn drop(&mut self) {
    debug_assert_eq!(
      self.vm.program_stack.len(),
      self.expected_len,
      "ProgramGuard dropped after stack length changed (did you manually pop?)"
    );
    let popped = self.vm.program_stack.pop();
    debug_assert!(
      popped.is_some(),
      "ProgramGuard dropped with empty program stack"
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
  fn erase_host_hooks_lifetime(host: &mut dyn VmHostHooks) -> *mut (dyn VmHostHooks + 'static) {
    let ptr: *mut (dyn VmHostHooks + '_) = host;
    // SAFETY: We only use this pointer while the embedder-provided `host` reference is alive.
    unsafe { mem::transmute::<*mut (dyn VmHostHooks + '_), *mut (dyn VmHostHooks + 'static)>(ptr) }
  }

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
      user_data: None,
      microtasks: MicrotaskQueue::new(),
      host_hooks_override: None,
      ecma_functions: Vec::new(),
      ecma_function_cache: HashMap::new(),
      program_stack: Vec::new(),
      intrinsics: None,
      realm_table: HashMap::new(),
      secondary_realms: Vec::new(),
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

  /// Temporarily override the host hook implementation used by [`Vm::call`] / [`Vm::construct`].
  ///
  /// This is primarily used by embedding entry points that need `vm-js` evaluation to enqueue
  /// Promise jobs onto a host-owned microtask queue (HTML `HostEnqueuePromiseJob`) instead of the
  /// VM-owned [`MicrotaskQueue`].
  pub fn with_host_hooks_override<R>(
    &mut self,
    host: &mut dyn VmHostHooks,
    f: impl FnOnce(&mut Vm) -> R,
  ) -> R {
    struct Guard<'a> {
      vm: &'a mut Vm,
      prev: Option<*mut (dyn VmHostHooks + 'static)>,
    }

    impl Drop for Guard<'_> {
      fn drop(&mut self) {
        self.vm.host_hooks_override = self.prev;
      }
    }

    let prev = self.host_hooks_override;
    self.host_hooks_override = Some(Self::erase_host_hooks_lifetime(host));
    let guard = Guard { vm: self, prev };
    f(&mut *guard.vm)
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

  /// Registers a realm's intrinsics under its global object (and optionally activates them).
  pub(crate) fn register_realm(
    &mut self,
    global: GcObject,
    id: RealmId,
    intrinsics: Intrinsics,
    global_lexical_env: GcEnv,
    global_lex_root: Option<EnvRootId>,
    activate: bool,
  ) {
    self.realm_table.insert(
      global.id().0,
      RealmTableEntry {
        global,
        id,
        intrinsics,
        global_lexical_env,
        global_lex_root,
      },
    );
    if activate {
      self.intrinsics = Some(intrinsics);
    }
  }

  /// Updates the global lexical environment recorded for `global` (primary realm after
  /// [`RuntimeEnv`] construction).
  pub(crate) fn set_realm_global_lexical_env(
    &mut self,
    global: GcObject,
    global_lexical_env: GcEnv,
  ) {
    if let Some(entry) = self.realm_table.get_mut(&global.id().0) {
      entry.global_lexical_env = global_lexical_env;
    }
  }

  /// Intrinsics for the realm whose global object is `global`.
  pub fn intrinsics_for_global(&self, global: GcObject) -> Option<Intrinsics> {
    self
      .realm_table
      .get(&global.id().0)
      .map(|e| e.intrinsics)
      .or(self.intrinsics)
  }

  /// Intrinsics for `func`'s [[Realm]] (stored as that realm's global object), falling back to the
  /// active realm.
  pub fn intrinsics_for_function(
    &self,
    heap: &Heap,
    func: GcObject,
  ) -> Result<Option<Intrinsics>, VmError> {
    Ok(match heap.get_function_realm(func)? {
      Some(global) => self.intrinsics_for_global(global),
      None => self.intrinsics(),
    })
  }

  /// If `eval_obj` is some registered realm's `%eval%`, return that realm's global, lexical env,
  /// and intrinsics.
  pub(crate) fn realm_for_eval_intrinsic(
    &self,
    eval_obj: GcObject,
  ) -> Option<(GcObject, GcEnv, Intrinsics, RealmId)> {
    self.realm_table.values().find_map(|e| {
      if e.intrinsics.eval() == eval_obj {
        Some((e.global, e.global_lexical_env, e.intrinsics, e.id))
      } else {
        None
      }
    })
  }

  /// Creates a new secondary realm, registers it, and returns its global object.
  ///
  /// The realm is retained on this VM until [`Vm::teardown_secondary_realms`] (called from
  /// [`crate::JsRuntime`] drop). Does **not** replace the active [`Vm::intrinsics`].
  pub fn create_realm(&mut self, heap: &mut Heap) -> Result<GcObject, VmError> {
    let realm = Realm::new_with_activation(self, heap, false)?;
    let global = realm.global_object();
    let id = realm.id();
    let intrinsics = *realm.intrinsics();
    let mut scope = heap.scope();
    scope.push_root(Value::Object(global))?;
    let lex = scope.env_create(None)?;
    let lex_root = scope.heap_mut().add_env_root(lex)?;
    drop(scope);
    self.register_realm(global, id, intrinsics, lex, Some(lex_root), false);
    self.secondary_realms.push(realm);
    Ok(global)
  }

  /// Tears down all secondary realms and their owned global-lexical env roots.
  pub fn teardown_secondary_realms(&mut self, heap: &mut Heap) {
    let secondary_keys: Vec<u64> = self
      .secondary_realms
      .iter()
      .map(|r| r.global_object().id().0)
      .collect();
    for key in secondary_keys {
      if let Some(entry) = self.realm_table.remove(&key) {
        if let Some(root) = entry.global_lex_root {
          heap.remove_env_root(root);
        }
      }
    }
    for mut realm in self.secondary_realms.drain(..) {
      realm.teardown(heap);
    }
  }

  pub fn interrupt_handle(&self) -> InterruptHandle {
    self.interrupt_handle.clone()
  }

  /// Clear the interrupt flag back to `false`.
  pub fn reset_interrupt(&self) {
    self.interrupt_handle.reset();
  }

  /// Attach arbitrary embedding state to this VM.
  ///
  /// Native (host-implemented) call/construct handlers receive both:
  /// - `&mut Vm` (engine state), and
  /// - `&mut dyn VmHost` (embedder-provided host context).
  ///
  /// Most host embeddings should thread shared state (DOM, event loop, wrapper caches, etc.) via
  /// [`VmHost`]. `Vm::user_data` is provided as a convenience for state that is logically owned by
  /// the VM itself, or when a host does not have access to a host-context object.
  ///
  /// The stored value can be downcast via [`Vm::user_data`] / [`Vm::user_data_mut`].
  pub fn set_user_data<T: Any>(&mut self, data: T) {
    self.user_data = Some(Box::new(data));
  }

  /// Borrow the embedded user data if it is of type `T`.
  pub fn user_data<T: Any>(&self) -> Option<&T> {
    self.user_data.as_deref()?.downcast_ref::<T>()
  }

  /// Mutably borrow the embedded user data if it is of type `T`.
  pub fn user_data_mut<T: Any>(&mut self) -> Option<&mut T> {
    self.user_data.as_deref_mut()?.downcast_mut::<T>()
  }

  /// Take ownership of the embedded user data if it is of type `T`.
  ///
  /// If the stored value exists but is not of type `T`, returns `None` and leaves the user data
  /// untouched.
  pub fn take_user_data<T: Any>(&mut self) -> Option<T> {
    let user_data = self.user_data.take()?;
    match user_data.downcast::<T>() {
      Ok(data) => Some(*data),
      Err(original) => {
        self.user_data = Some(original);
        None
      }
    }
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

  /// Pushes `program` as the active parsed AST for function registration / nested evaluation.
  pub(crate) fn enter_program(&mut self, program: Arc<ParsedProgram>) -> ProgramGuard<'_> {
    ProgramGuard::new(self, program)
  }

  /// Pushes `program` without an RAII guard (paired with [`Self::pop_program`]).
  pub(crate) fn push_program(&mut self, program: Arc<ParsedProgram>) {
    self.program_stack.push(program);
  }

  /// Pops the program pushed by [`Self::push_program`].
  pub(crate) fn pop_program(&mut self) {
    let _ = self.program_stack.pop();
  }

  /// Registers an ECMAScript function body by retaining a pointer into the active [`ParsedProgram`].
  ///
  /// `func` must be a node inside the current top-of-stack program AST. The program `Arc` is stored
  /// alongside the pointer so the body remains valid after the originating evaluation returns.
  pub(crate) fn register_ecma_function(
    &mut self,
    source: Arc<SourceText>,
    span_start: u32,
    span_end: u32,
    kind: EcmaFunctionKind,
    func: &Node<Func>,
  ) -> Result<EcmaFunctionId, VmError> {
    let key = EcmaFunctionKey {
      source: Arc::as_ptr(&source),
      span_start,
      span_end,
      kind,
    };
    if let Some(id) = self.ecma_function_cache.get(&key).copied() {
      return Ok(id);
    }

    let program = self
      .program_stack
      .last()
      .cloned()
      .ok_or(VmError::Unimplemented(
        "ECMAScript function registered without an active parsed program",
      ))?;

    let idx = u32::try_from(self.ecma_functions.len())
      .map_err(|_| VmError::LimitExceeded("too many ECMAScript functions registered"))?;

    self
      .ecma_functions
      .try_reserve(1)
      .map_err(|_| VmError::OutOfMemory)?;

    // SAFETY: `func` is borrowed from the active `ParsedProgram` tree. We store that same `Arc` in
    // `EcmaFunctionCode::program`, so the `NonNull` stays valid for as long as the code entry lives.
    let func_ptr = NonNull::from(func);

    self.ecma_functions.push(EcmaFunctionCode {
      source,
      span_start,
      span_end,
      kind,
      // Retained ASTs use absolute `Loc` offsets in `source`; no synthetic wrap prefix.
      prefix_len: 0,
      program,
      func: func_ptr,
    });

    let id = EcmaFunctionId(idx);
    self.ecma_function_cache.insert(key, id);
    Ok(id)
  }

  /// Returns the retained function AST plus the `Arc` that keeps it alive.
  ///
  /// The returned `NonNull` may be turned into `&Node<Func>` only while the `Arc<ParsedProgram>`
  /// (or another clone) is held.
  fn ecma_function_body(
    &self,
    id: EcmaFunctionId,
  ) -> Result<(Arc<SourceText>, Arc<ParsedProgram>, NonNull<Node<Func>>), VmError> {
    let code = self
      .ecma_functions
      .get(id.0 as usize)
      .ok_or(VmError::InvalidHandle)?;
    Ok((code.source.clone(), code.program.clone(), code.func))
  }

  fn dispatch_native_call(
    &mut self,
    call_id: NativeFunctionId,
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    hooks: &mut dyn VmHostHooks,
    callee: GcObject,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let f = self
      .native_calls
      .get(call_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native function id"))?;
    f(self, scope, host, hooks, callee, this, args)
  }

  fn dispatch_native_construct(
    &mut self,
    construct_id: NativeConstructId,
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    hooks: &mut dyn VmHostHooks,
    callee: GcObject,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let construct = self
      .native_constructs
      .get(construct_id.0 as usize)
      .copied()
      .ok_or(VmError::Unimplemented("unknown native constructor id"))?;
    construct(self, scope, host, hooks, callee, args, new_target)
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
    // `self.stack` is maintained in call-stack order (outermost → innermost). Stack traces are
    // conventionally rendered with the most recent frame first, so reverse during capture.
    self.stack.iter().cloned().rev().collect()
  }

  /// Pushes an [`ExecutionContext`] onto the execution context stack.
  pub fn push_execution_context(&mut self, ctx: ExecutionContext) {
    self.execution_context_stack.push(ctx);
  }

  pub(crate) fn push_active_host_hooks(
    &mut self,
    host: &mut dyn VmHostHooks,
  ) -> Option<*mut (dyn VmHostHooks + 'static)> {
    let prev = self.host_hooks_override;
    self.host_hooks_override = Some(Self::erase_host_hooks_lifetime(host));
    prev
  }

  pub(crate) fn pop_active_host_hooks(
    &mut self,
    previous: Option<*mut (dyn VmHostHooks + 'static)>,
  ) {
    self.host_hooks_override = previous;
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
  /// `host` is embedder-provided context (DOM/event loop/etc) forwarded to native call handlers.
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
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    if let Some(hooks_ptr) = self.host_hooks_override {
      // SAFETY: `host_hooks_override` is only set while a host hooks implementation is mutably
      // borrowed by an embedder entry point (for example `Vm::call_with_host_and_hooks` or
      // `JsRuntime::exec_script_source_with_hooks`).
      let hooks = unsafe { &mut *hooks_ptr };
      return self.call_impl(host, scope, hooks, callee, this, args);
    }

    // `call_with_host_and_hooks` requires `&mut self` plus an independent `&mut hooks`, but `Vm`
    // stores a default microtask queue inside itself. Temporarily move it out so it can serve as
    // the host hook implementation for this call.
    let mut hooks = mem::take(&mut self.microtasks);
    let prev_hooks = self.push_active_host_hooks(&mut hooks);
    let result = self.call_impl(host, scope, &mut hooks, callee, this, args);
    self.pop_active_host_hooks(prev_hooks);
    self.microtasks = hooks;
    result
  }

  /// Convenience wrapper around [`Vm::call`] that passes a dummy host context (`()`) and uses the
  /// VM-owned microtask queue.
  ///
  /// This exists for internal engine/tests that do not have embedder state available. Host
  /// embeddings should prefer [`Vm::call`] so native handlers can access real host context.
  #[inline]
  pub fn call_without_host(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let mut hooks = mem::take(&mut self.microtasks);
    let result = self.call_with_host(scope, &mut hooks, callee, this, args);
    self.microtasks = hooks;
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
    let mut dummy_host = ();
    self.call_with_host_and_hooks(&mut dummy_host, scope, host, callee, this, args)
  }

  /// Calls `callee` with the provided `this` value and arguments, using an explicit embedder host
  /// context and host hook implementation.
  #[inline]
  pub fn call_with_host_and_hooks(
    &mut self,
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    hooks: &mut dyn VmHostHooks,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let prev_hooks = self.push_active_host_hooks(hooks);
    let result = self.call_impl(host, scope, hooks, callee, this, args);
    self.pop_active_host_hooks(prev_hooks);
    result
  }

  fn call_impl(
    &mut self,
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    hooks: &mut dyn VmHostHooks,
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

        // Root the concatenated list for the duration of the forwarding call.
        scope.push_roots(&combined)?;

        return self.call_impl(
          host,
          &mut scope,
          hooks,
          Value::Object(bound_target),
          bound_this,
          &combined,
        );
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

    let (source, line, col) = match &call_handler {
      CallHandler::Native(_) => (Arc::<str>::from("<native>"), 0, 0),
      CallHandler::Ecma(code_id) => match self.ecma_functions.get(code_id.0 as usize) {
        Some(code) => {
          let (line, col) = code.source.line_col(code.span_start);
          (code.source.name.clone(), line, col)
        }
        None => (Arc::<str>::from("<call>"), 0, 0),
      },
      CallHandler::User(_) => (Arc::<str>::from("<user>"), 0, 0),
    };
    let frame = StackFrame {
      function: function_name,
      source,
      line,
      col,
    };

    let mut vm = self.enter_frame(frame)?;
    // Budget/interrupt check for host-initiated calls that may not pass through the evaluator.
    vm.tick()?;

    let result = match call_handler {
      CallHandler::Native(call_id) => {
        vm.dispatch_native_call(call_id, host, &mut scope, hooks, callee_obj, this, args)
      }
      CallHandler::Ecma(code_id) => {
        vm.call_ecma_function(&mut scope, host, hooks, code_id, callee_obj, this, args)
      }
      CallHandler::User(func) => {
        drop(func);
        Err(VmError::Unimplemented("user-defined function call"))
      }
    };

    // Capture a stack trace for thrown exceptions before the current frame is popped.
    match result {
      Err(VmError::Throw(value)) => Err(VmError::ThrowWithStack {
        value,
        stack: vm.capture_stack(),
      }),
      other => other,
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

  /// ECMAScript `GetMethod(O, P)` where `O` is already known to be an object.
  pub fn get_method_from_object(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    key: PropertyKey,
  ) -> Result<Option<Value>, VmError> {
    let value = self.get(scope, obj, key)?;
    if matches!(value, Value::Undefined | Value::Null) {
      return Ok(None);
    }

    if !scope.heap().is_callable(value)? {
      return Err(VmError::TypeError("GetMethod: target is not callable"));
    }
    Ok(Some(value))
  }

  /// ECMAScript `GetMethod(V, P)`.
  ///
  /// Uses `GetV` semantics: `null`/`undefined` throw a catchable `TypeError` (via `ToObject`);
  /// other primitives resolve against the matching intrinsic prototype without allocating a
  /// wrapper when possible (delegating to [`Self::get_method_from_object`] after a best-effort
  /// `Object(value)` box for exotic cases).
  pub fn get_method(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
    key: PropertyKey,
  ) -> Result<Option<Value>, VmError> {
    match value {
      Value::Object(obj) => self.get_method_from_object(scope, obj, key),
      Value::Undefined | Value::Null => {
        let intr = self
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = crate::error_object::new_error(
          scope,
          intr.type_error_prototype(),
          "TypeError",
          "GetMethod: cannot convert undefined or null to object",
        )?;
        Err(VmError::Throw(err))
      }
      other => {
        // Box via `%Object%` then GetMethod on the result (covers Number/String/… wrappers).
        let intr = self
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let object_ctor = Value::Object(intr.object_constructor());
        let mut box_scope = scope.reborrow();
        box_scope.push_root(other)?;
        box_scope.push_root(object_ctor)?;
        // `Vm::call` requires host+hooks; use the no-host path for intrinsic boxing.
        let boxed =
          self.call_without_host(&mut box_scope, object_ctor, Value::Undefined, &[other])?;
        let Value::Object(obj) = boxed else {
          return Err(VmError::InvariantViolation(
            "Object(..) conversion returned non-object",
          ));
        };
        box_scope.push_root(Value::Object(obj))?;
        self.get_method_from_object(&mut box_scope, obj, key)
      }
    }
  }

  /// Constructs `callee` with the provided arguments and `new_target`.
  ///
  /// `host` is embedder-provided context (DOM/event loop/etc) forwarded to native constructor
  /// handlers.
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
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    if let Some(hooks_ptr) = self.host_hooks_override {
      // SAFETY: see `Vm::call` for the safety contract of `host_hooks_override`.
      let hooks = unsafe { &mut *hooks_ptr };
      return self.construct_impl(host, scope, hooks, callee, args, new_target);
    }

    let mut hooks = mem::take(&mut self.microtasks);
    let prev_hooks = self.push_active_host_hooks(&mut hooks);
    let result = self.construct_impl(host, scope, &mut hooks, callee, args, new_target);
    self.pop_active_host_hooks(prev_hooks);
    self.microtasks = hooks;
    result
  }

  /// Convenience wrapper around [`Vm::construct`] that passes a dummy host context (`()`) and uses
  /// the VM-owned microtask queue.
  pub fn construct_without_host(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let mut hooks = mem::take(&mut self.microtasks);
    let result = self.construct_with_host(scope, &mut hooks, callee, args, new_target);
    self.microtasks = hooks;
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
    let mut dummy_host = ();
    self.construct_with_host_and_hooks(&mut dummy_host, scope, host, callee, args, new_target)
  }

  /// Constructs `callee` with the provided arguments and `new_target`, using an explicit embedder
  /// host context and host hook implementation.
  #[inline]
  pub fn construct_with_host_and_hooks(
    &mut self,
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    hooks: &mut dyn VmHostHooks,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let prev_hooks = self.push_active_host_hooks(hooks);
    let result = self.construct_impl(host, scope, hooks, callee, args, new_target);
    self.pop_active_host_hooks(prev_hooks);
    result
  }

  fn construct_impl(
    &mut self,
    host: &mut dyn VmHost,
    scope: &mut Scope<'_>,
    hooks: &mut dyn VmHostHooks,
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

        // ECMA-262: if `new_target` is the bound function itself, forward `new_target` as the
        // target function.
        let forwarded_new_target = if new_target == callee {
          Value::Object(bound_target)
        } else {
          new_target
        };

        // Root the concatenated list for the duration of the forwarding call.
        scope.push_roots(&combined)?;

        return self.construct_impl(
          host,
          &mut scope,
          hooks,
          Value::Object(bound_target),
          &combined,
          forwarded_new_target,
        );
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

    let (source, line, col) = match construct_handler {
      ConstructHandler::Native(_) => (Arc::<str>::from("<native>"), 0, 0),
      ConstructHandler::Ecma(code_id) => match self.ecma_functions.get(code_id.0 as usize) {
        Some(code) => {
          let (line, col) = code.source.line_col(code.span_start);
          (code.source.name.clone(), line, col)
        }
        None => (Arc::<str>::from("<call>"), 0, 0),
      },
    };
    let frame = StackFrame {
      function: function_name,
      source,
      line,
      col,
    };

    let mut vm = self.enter_frame(frame)?;
    // Budget/interrupt check for host-initiated construction that may not pass through the
    // evaluator.
    vm.tick()?;

    let result = match construct_handler {
      ConstructHandler::Native(construct_id) => vm.dispatch_native_construct(
        construct_id,
        host,
        &mut scope,
        hooks,
        callee_obj,
        args,
        new_target,
      ),
      ConstructHandler::Ecma(code_id) => vm.construct_ecma_function(
        &mut scope, host, hooks, code_id, callee_obj, args, new_target,
      ),
    };

    // Capture a stack trace for thrown exceptions before the current frame is popped.
    match result {
      Err(VmError::Throw(value)) => Err(VmError::ThrowWithStack {
        value,
        stack: vm.capture_stack(),
      }),
      other => other,
    }
  }

  fn call_ecma_function(
    &mut self,
    scope: &mut Scope<'_>,
    host: &mut dyn VmHost,
    hooks: &mut dyn VmHostHooks,
    code_id: EcmaFunctionId,
    callee: crate::GcObject,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let (this_mode, is_strict, realm, outer, bound_this, bound_new_target, is_class_constructor) = {
      let f = scope.heap().get_function(callee)?;
      (
        f.this_mode,
        f.is_strict,
        f.realm,
        f.closure_env,
        f.bound_this,
        f.bound_new_target,
        f.is_class_constructor,
      )
    };

    if is_class_constructor {
      let err = crate::builtins::create_type_error(
        self,
        scope,
        hooks,
        "Class constructor cannot be invoked without 'new'",
      )?;
      return Err(VmError::Throw(err));
    }

    let this = match this_mode {
      ThisMode::Lexical => bound_this.ok_or(VmError::Unimplemented(
        "arrow function missing captured lexical this",
      ))?,
      ThisMode::Strict => this,
      ThisMode::Global => match this {
        Value::Undefined | Value::Null => match realm {
          Some(global) => Value::Object(global),
          None => this,
        },
        other => other,
      },
    };

    let new_target = match this_mode {
      ThisMode::Lexical => bound_new_target.ok_or(VmError::Unimplemented(
        "arrow function missing captured lexical new.target",
      ))?,
      ThisMode::Strict | ThisMode::Global => Value::Undefined,
    };

    let global_object = realm.ok_or(VmError::Unimplemented(
      "ECMAScript function missing [[Realm]]",
    ))?;

    let (source, program, func_ptr) = self.ecma_function_body(code_id)?;
    let program_for_body = program.clone();
    let mut program_guard = self.enter_program(program);
    // SAFETY: `func_ptr` was registered from a node inside `program`, and `program_guard` (plus the
    // clone stored in `EcmaFunctionCode`) keeps that tree alive for this call.
    let func_ast = unsafe { func_ptr.as_ref() };

    let func_env = scope.env_create(outer)?;
    let mut env =
      RuntimeEnv::new_with_var_env(scope.heap_mut(), global_object, func_env, func_env)?;

    let result = if func_ast.stx.async_ || func_ast.stx.generator {
      // Suspendable bodies: capture the activation into a heap state machine instead of running
      // recursively (returns the generator object / result promise).
      crate::generator::call_suspendable_function(
        &mut *program_guard,
        scope,
        host,
        hooks,
        &mut env,
        source,
        is_strict,
        this,
        func_ast,
        args,
        callee,
        program_for_body,
      )
    } else {
      crate::exec::run_ecma_function(
        &mut *program_guard,
        scope,
        host,
        hooks,
        &mut env,
        source,
        // Retained ASTs carry absolute `Loc` offsets in `source`.
        0,
        0,
        is_strict,
        this,
        /* this_uninitialized */ false,
        new_target,
        Some(callee),
        func_ast,
        args,
      )
      .map(|r| r.value)
    };

    env.teardown(scope.heap_mut());
    result
  }

  fn construct_ecma_function(
    &mut self,
    scope: &mut Scope<'_>,
    host: &mut dyn VmHost,
    hooks: &mut dyn VmHostHooks,
    code_id: EcmaFunctionId,
    callee: crate::GcObject,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let (is_strict, global_object, outer) = {
      let f = scope.heap().get_function(callee)?;
      (
        f.is_strict,
        f.realm.ok_or(VmError::Unimplemented(
          "ECMAScript function missing [[Realm]]",
        ))?,
        f.closure_env,
      )
    };

    // Generator/async functions have no [[Construct]] (spec: not constructors).
    {
      let (_, _, func_ptr) = self.ecma_function_body(code_id)?;
      // SAFETY: the registered program (held by `EcmaFunctionCode`) keeps the node alive.
      let func_ast = unsafe { func_ptr.as_ref() };
      if func_ast.stx.async_ || func_ast.stx.generator {
        let err = crate::builtins::create_type_error(
          self,
          scope,
          hooks,
          "generator/async function is not a constructor",
        )?;
        return Err(VmError::Throw(err));
      }
    }

    // GetPrototypeFromConstructor(newTarget, %Object.prototype%).
    let intr = self
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    let default_proto = intr.object_prototype();
    let reference_error_prototype = intr.reference_error_prototype();
    let proto = match new_target {
      Value::Object(nt) => {
        let mut proto_scope = scope.reborrow();
        proto_scope.push_root(Value::Object(nt))?;
        let key_s = proto_scope.alloc_string("prototype")?;
        proto_scope.push_root(Value::String(key_s))?;
        let key = PropertyKey::from_string(key_s);
        let value = proto_scope.ordinary_get_with_host_and_hooks(
          self,
          host,
          hooks,
          nt,
          key,
          Value::Object(nt),
        )?;
        match value {
          Value::Object(o) => o,
          _ => default_proto,
        }
      }
      _ => default_proto,
    };

    let is_derived = scope.heap().function_is_derived_constructor(callee)?;

    let mut this_scope = scope.reborrow();
    let (this_arg, this_uninitialized) = if is_derived {
      // Derived constructors leave `this` uninitialized until `super()` (ECMA-262 §10.2.2).
      (Value::Undefined, true)
    } else {
      let this_obj = this_scope.alloc_object_with_prototype(Some(proto))?;
      this_scope.push_root(Value::Object(this_obj))?;
      this_scope.push_root(Value::Object(callee))?;
      // InitializeInstanceElements(O, F) before running the constructor body.
      this_scope
        .heap_mut()
        .initialize_instance_private_elements(this_obj, callee)?;
      (Value::Object(this_obj), false)
    };

    let func_env = this_scope.env_create(outer)?;
    let mut env =
      RuntimeEnv::new_with_var_env(this_scope.heap_mut(), global_object, func_env, func_env)?;

    let (source, program, func_ptr) = self.ecma_function_body(code_id)?;
    let mut program_guard = self.enter_program(program);
    // SAFETY: `func_ptr` was registered from a node inside `program`, and `program_guard` (plus the
    // clone stored in `EcmaFunctionCode`) keeps that tree alive for this call.
    let func_ast = unsafe { func_ptr.as_ref() };

    let result = crate::exec::run_ecma_function(
      &mut *program_guard,
      &mut this_scope,
      host,
      hooks,
      &mut env,
      source,
      // Retained ASTs carry absolute `Loc` offsets in `source`.
      0,
      0,
      is_strict,
      this_arg,
      this_uninitialized,
      new_target,
      Some(callee),
      func_ast,
      args,
    );
    drop(program_guard);

    env.teardown(this_scope.heap_mut());

    let body = result?;
    match body.value {
      Value::Object(o) => Ok(Value::Object(o)),
      _ if is_derived => {
        if !body.this_initialized {
          let err = crate::error_object::new_error(
            &mut this_scope,
            reference_error_prototype,
            "ReferenceError",
            "Must call super constructor in derived class before returning from derived constructor",
          )?;
          Err(VmError::Throw(err))
        } else {
          match body.this {
            Value::Object(o) => Ok(Value::Object(o)),
            _ => Err(VmError::InvariantViolation(
              "derived constructor this binding is not an object",
            )),
          }
        }
      }
      _ => match this_arg {
        Value::Object(o) => Ok(Value::Object(o)),
        _ => Err(VmError::InvariantViolation(
          "base constructor missing this object",
        )),
      },
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  fn noop_call(
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _host: &mut dyn VmHost,
    _hooks: &mut dyn VmHostHooks,
    _callee: GcObject,
    _this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    Ok(Value::Undefined)
  }

  fn noop_construct(
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _host: &mut dyn VmHost,
    _hooks: &mut dyn VmHostHooks,
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
