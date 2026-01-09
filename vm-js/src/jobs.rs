//! ECMAScript jobs and host integration hooks.
//!
//! This module is intentionally **evaluator-independent**: it defines small, engine-owned types
//! that can exist before a full ECMAScript evaluator/interpreter is implemented.
//!
//! ## Spec background
//!
//! - **ECMA-262** defines *job abstract closures* (e.g. Promise jobs) and requires the host
//!   environment to schedule them via host-defined hooks:
//!   - [`HostEnqueuePromiseJob`](https://tc39.es/ecma262/#sec-hostenqueuepromisejob) (FIFO ordering)
//!   - [`HostPromiseRejectionTracker`](https://tc39.es/ecma262/#sec-host-promise-rejection-tracker)
//! - **HTML** defines how these hooks map onto the browser event loop:
//!   - [`HostEnqueuePromiseJob`](https://html.spec.whatwg.org/multipage/webappapis.html#hostenqueuepromisejob)
//!     queues a microtask which "prepares to run script", runs the job, cleans up, and reports
//!     exceptions.
//!   - Microtasks are processed at
//!     [microtask checkpoints](https://html.spec.whatwg.org/multipage/webappapis.html#perform-a-microtask-checkpoint).
//!   - HTML also defines
//!     [`HostMakeJobCallback`](https://html.spec.whatwg.org/multipage/webappapis.html#hostmakejobcallback) and
//!     [`HostCallJobCallback`](https://html.spec.whatwg.org/multipage/webappapis.html#hostcalljobcallback) for
//!     capturing and propagating the incumbent settings object / active script when scheduling and
//!     running callbacks.
//!
//! The main integration point is [`VmHostHooks::host_enqueue_promise_job`]. An embedding (e.g.
//! FastRender) can implement it by routing Promise jobs into the HTML microtask queue. The actual
//! queue is **host-owned**; this crate only provides the job representation.

use crate::heap::{Trace, Tracer};
use crate::{GcObject, RootId, Value, VmError};
use crate::{HostDefined, ModuleLoadPayload, ModuleReferrer, ModuleRequest, VmModuleLoadingContext};
use std::any::Any;
use std::fmt;
use std::sync::Arc;

/// Opaque identifier for a Realm Record that a job should run in.
///
/// In ECMA-262, realms are described here:
/// <https://tc39.es/ecma262/#sec-code-realms>
///
/// In an HTML embedding, realms are typically associated with an
/// [environment settings object](https://html.spec.whatwg.org/multipage/webappapis.html#environment-settings-object).
///
/// This type is an *opaque token*: hosts should treat it as an identifier to store and pass back
/// to the VM/host hooks, not something to interpret.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct RealmId(u64);

impl RealmId {
  /// Create a new `RealmId` from an opaque numeric value.
  ///
  /// The numeric representation is intentionally unspecified; it may change.
  #[inline]
  pub const fn from_raw(raw: u64) -> Self {
    Self(raw)
  }

  /// Returns the underlying opaque numeric representation.
  #[inline]
  pub const fn to_raw(self) -> u64 {
    self.0
  }
}

impl fmt::Debug for RealmId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("RealmId").field(&self.0).finish()
  }
}

/// A coarse classification of host-scheduled work.
///
/// The host can use this to map work onto different event-loop queues (e.g. Promise jobs into the
/// microtask queue vs. timers into a task queue).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum JobKind {
  /// A Promise job (microtask in HTML).
  Promise,
  /// Generic work that does not have additional spec constraints.
  Generic,
  /// A timer callback (`setTimeout`/`setInterval`-like host tasks).
  Timeout,
  /// A cleanup job run for `FinalizationRegistry`.
  FinalizationRegistryCleanup,
}

/// The result of running an ECMAScript job.
///
/// If this returns an error, the embedding is expected to treat it similarly to an uncaught
/// exception during a microtask/task (e.g. report it).
pub type JobResult = Result<(), VmError>;

/// Dynamic context passed to jobs at execution time.
///
/// Promise jobs need to:
/// - call/construct JS values,
/// - keep captured GC handles alive while queued (persistent roots).
///
/// This trait is intentionally object-safe so hosts can store job runners behind trait objects.
pub trait VmJobContext {
  /// Calls `callee` with the provided `this` value and arguments.
  fn call(&mut self, callee: Value, this: Value, args: &[Value]) -> Result<Value, VmError>;

  /// Constructs `callee` with the provided arguments and `new_target`.
  fn construct(
    &mut self,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError>;

  /// Adds a persistent root, keeping `value` live until the returned [`RootId`] is removed.
  fn add_root(&mut self, value: Value) -> RootId;

  /// Removes a persistent root previously created by [`VmJobContext::add_root`].
  fn remove_root(&mut self, id: RootId);
}

/// A spec-shaped representation of an ECMAScript *Job Abstract Closure*.
///
/// In ECMA-262, a "job" is a parameterless abstract closure that can be enqueued and later run by
/// the host (usually as part of a microtask checkpoint).
///
/// This representation is Rust-idiomatic: a job is a boxed `FnOnce` that receives a dynamic
/// [`VmJobContext`] and [`VmHostHooks`] so it can call back into the evaluator/embedding at run
/// time.
///
/// # GC safety
///
/// Promise jobs can be queued across allocations/GC. Any GC-managed [`Value`] captured by a job
/// MUST be kept alive until the job runs.
///
/// The engine-supported pattern is:
/// - create persistent roots at enqueue time (via [`VmJobContext::add_root`]),
/// - record the returned [`RootId`]s on the job,
/// - and let [`Job::run`] / [`Job::discard`] automatically remove them.
pub struct Job {
  kind: JobKind,
  roots: Vec<RootId>,
  run: Option<Box<dyn FnOnce(&mut dyn VmJobContext, &mut dyn VmHostHooks) -> JobResult + Send + 'static>>,
}

impl Job {
  /// Create a new job of `kind` backed by `run`.
  pub fn new(
    kind: JobKind,
    run: impl FnOnce(&mut dyn VmJobContext, &mut dyn VmHostHooks) -> JobResult + Send + 'static,
  ) -> Self {
    Self {
      kind,
      roots: Vec::new(),
      run: Some(Box::new(run)),
    }
  }

  /// Adds a persistent root that will be automatically removed when the job is run or discarded.
  pub fn add_root(&mut self, ctx: &mut dyn VmJobContext, value: Value) -> RootId {
    let id = ctx.add_root(value);
    self.roots.push(id);
    id
  }

  /// Records an existing persistent root so it will be automatically removed when the job is run
  /// or discarded.
  pub fn push_root(&mut self, id: RootId) {
    self.roots.push(id);
  }

  /// Adds multiple existing persistent roots.
  pub fn extend_roots(&mut self, ids: impl IntoIterator<Item = RootId>) {
    self.roots.extend(ids);
  }

  /// Replaces the job's root list (useful when capturing roots at enqueue time).
  pub fn with_roots(mut self, roots: Vec<RootId>) -> Self {
    self.roots = roots;
    self
  }

  /// Returns this job's kind.
  #[inline]
  pub fn kind(&self) -> JobKind {
    self.kind
  }

  fn cleanup_roots(&mut self, ctx: &mut dyn VmJobContext) {
    for root in self.roots.drain(..) {
      ctx.remove_root(root);
    }
  }

  /// Run the job, consuming it.
  #[inline]
  pub fn run(mut self, ctx: &mut dyn VmJobContext, host: &mut dyn VmHostHooks) -> JobResult {
    let Some(run) = self.run.take() else {
      return Err(VmError::Unimplemented("job already consumed"));
    };

    // Ensure roots are cleaned up even if the job panics.
    let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| run(ctx, host)));
    self.cleanup_roots(ctx);

    match result {
      Ok(result) => result,
      Err(panic) => std::panic::resume_unwind(panic),
    }
  }

  /// Discards the job without running it, cleaning up any persistent roots it owns.
  pub fn discard(mut self, ctx: &mut dyn VmJobContext) {
    self.run = None;
    self.cleanup_roots(ctx);
  }
}

impl fmt::Debug for Job {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("Job")
      .field("kind", &self.kind)
      .field("roots", &self.roots.len())
      .finish()
  }
}

impl Drop for Job {
  fn drop(&mut self) {
    // Avoid panicking from a destructor while unwinding (that would abort).
    if std::thread::panicking() {
      return;
    }
    debug_assert!(
      self.roots.is_empty(),
      "Job dropped with {} leaked persistent roots; call Job::run(..) or Job::discard(..)",
      self.roots.len()
    );
  }
}

/// A host-defined *JobCallback* record.
///
/// HTML uses JobCallback records to capture the "incumbent settings object" / active script state
/// at the moment a callback is created, and later re-establish that state when calling it.
///
/// In this crate the record is mostly opaque: the host may associate arbitrary data with the
/// callback, but the callback object itself is stored explicitly so engine code can keep it alive
/// across GC cycles.
///
/// # GC safety / rooting (important!)
///
/// A [`JobCallback`] is **host-owned data**. Like any host-owned structure, it is not
/// automatically visited by the GC: the GC only traces objects that are reachable from the heap
/// graph and from explicit roots.
///
/// `JobCallback` implements [`Trace`] by tracing the callback object, so an embedding can keep the
/// callback alive by storing `JobCallback` inside a traced structure. However, simply holding a
/// `JobCallback` record in host state (queued tasks/microtasks, timers, etc.) does **not** keep the
/// callback alive.
///
/// If a callback must stay alive until some future host work runs, the embedding MUST keep
/// [`JobCallback::callback`] alive by registering it as a persistent root (for example via
/// [`VmJobContext::add_root`] / [`VmJobContext::remove_root`], typically attached to the queued
/// [`Job`], or via [`crate::Heap::add_root`] / [`crate::Heap::remove_root`]).
///
/// The host-defined payload is **opaque** to the GC. Hosts MUST NOT store GC handles inside the
/// payload unless they keep them alive independently.
///
/// ## Recommended pattern
///
/// When enqueuing a job that will later observe/call a callback, register the callback object as a
/// persistent root for the lifetime of the queued job:
///
/// ```no_run
/// # use vm_js::{GcObject, Job, JobKind, JobResult, JobCallback, RealmId, RootId, Value, VmError, VmHostHooks, VmJobContext};
/// # struct Host;
/// # impl VmHostHooks for Host {
/// #   fn host_enqueue_promise_job(&mut self, _job: Job, _realm: Option<RealmId>) {}
/// # }
/// # struct Ctx;
/// # impl VmJobContext for Ctx {
/// #   fn call(&mut self, _callee: Value, _this: Value, _args: &[Value]) -> Result<Value, VmError> { unimplemented!() }
/// #   fn construct(&mut self, _callee: Value, _args: &[Value], _new_target: Value) -> Result<Value, VmError> { unimplemented!() }
/// #   fn add_root(&mut self, _value: Value) -> RootId { unimplemented!() }
/// #   fn remove_root(&mut self, _id: RootId) { unimplemented!() }
/// # }
/// # let mut host = Host;
/// # let mut ctx = Ctx;
/// # let callback_obj: GcObject = todo!();
/// let job_callback: JobCallback = host.host_make_job_callback(callback_obj);
///
/// let mut job = Job::new(JobKind::Generic, move |_ctx, _host| -> JobResult {
///   // Later: _host.host_call_job_callback(_ctx, &job_callback, ...)?;
///   let _ = job_callback.callback();
///   Ok(())
/// });
///
/// // IMPORTANT: keep `callback_obj` alive until the queued job runs.
/// job.add_root(&mut ctx, Value::Object(callback_obj));
/// host.host_enqueue_promise_job(job, None);
/// ```
#[derive(Clone)]
pub struct JobCallback {
  callback: GcObject,
  host_defined: Option<Arc<dyn Any + Send + Sync>>,
}

impl JobCallback {
  /// Create a new `JobCallback` with no extra host-defined metadata.
  pub fn new(callback: GcObject) -> Self {
    Self {
      callback,
      host_defined: None,
    }
  }

  /// Create a new `JobCallback` with host-defined metadata.
  pub fn new_with_data<T: Any + Send + Sync>(callback: GcObject, data: T) -> Self {
    Self {
      callback,
      host_defined: Some(Arc::new(data)),
    }
  }

  /// Returns the callback object captured by this record.
  #[inline]
  pub fn callback(&self) -> GcObject {
    self.callback
  }

  /// Alias for [`JobCallback::callback`].
  #[inline]
  pub fn callback_object(&self) -> GcObject {
    self.callback
  }

  /// Attempts to downcast the host-defined metadata payload by reference.
  pub fn downcast_ref<T: Any>(&self) -> Option<&T> {
    self.host_defined.as_ref()?.downcast_ref::<T>()
  }
}

impl fmt::Debug for JobCallback {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("JobCallback")
      .field("callback", &self.callback)
      .field(
        "host_defined_type_id",
        &self.host_defined.as_ref().map(|v| v.type_id()),
      )
      .finish()
  }
}

impl Trace for JobCallback {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    tracer.trace_value(Value::Object(self.callback));
  }
}

/// Opaque handle to a promise object passed to [`VmHostHooks::host_promise_rejection_tracker`].
///
/// At this layer, promises are represented as ordinary JavaScript objects (in HTML, they are
/// surfaced as an `object` on `PromiseRejectionEvent`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct PromiseHandle(pub GcObject);

impl From<GcObject> for PromiseHandle {
  fn from(value: GcObject) -> Self {
    Self(value)
  }
}

impl From<PromiseHandle> for GcObject {
  fn from(value: PromiseHandle) -> Self {
    value.0
  }
}

/// The operation passed to [`VmHostHooks::host_promise_rejection_tracker`].
///
/// Mirrors the `operation` string argument in the ECMAScript spec.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PromiseRejectionOperation {
  /// A promise became rejected while having no rejection handlers.
  Reject,
  /// A rejection handler was added to a previously-unhandled rejected promise.
  Handle,
}

/// Host hooks required by the ECMAScript specification (and refined by HTML for browsers).
///
/// The VM/evaluator calls into this trait; the embedding provides the implementation.
///
/// ## FIFO requirement
///
/// ECMA-262 requires Promise jobs to be processed in FIFO order for an agent:
/// <https://tc39.es/ecma262/#sec-hostenqueuepromisejob>.
///
/// The VM will call [`VmHostHooks::host_enqueue_promise_job`] in the spec-required order; hosts
/// MUST preserve this ordering when running the queued jobs.
pub trait VmHostHooks {
  /// Enqueue a Promise job.
  ///
  /// ## ECMA-262
  ///
  /// This corresponds to
  /// [`HostEnqueuePromiseJob(job, realm)`](https://tc39.es/ecma262/#sec-hostenqueuepromisejob).
  ///
  /// ## HTML embedding
  ///
  /// HTML defines this hook by
  /// [queueing a microtask](https://html.spec.whatwg.org/multipage/webappapis.html#queue-a-microtask)
  /// that:
  ///
  /// 1. (If `realm` is not `None`) [prepares to run script](https://html.spec.whatwg.org/multipage/webappapis.html#prepare-to-run-script),
  /// 2. runs `job`,
  /// 3. [cleans up after running script](https://html.spec.whatwg.org/multipage/webappapis.html#clean-up-after-running-script),
  /// 4. and [reports exceptions](https://html.spec.whatwg.org/multipage/webappapis.html#report-the-exception).
  ///
  /// Microtasks are processed at
  /// [microtask checkpoints](https://html.spec.whatwg.org/multipage/webappapis.html#perform-a-microtask-checkpoint).
  fn host_enqueue_promise_job(&mut self, job: Job, realm: Option<RealmId>);

  /// Creates a host-defined [`JobCallback`] record.
  ///
  /// Stub hook for HTML's `HostMakeJobCallback`:
  /// <https://html.spec.whatwg.org/multipage/webappapis.html#hostmakejobcallback>.
  ///
  /// Embeddings that do not need incumbent/active-script propagation can use the default
  /// implementation, which stores the callback object with no extra host-defined metadata.
  ///
  /// ## GC safety (important!)
  ///
  /// The default implementation stores `callback` as a raw [`GcObject`] inside a [`JobCallback`]
  /// record, but does not register it as a persistent root.
  ///
  /// If the callback object must stay alive until some future task/microtask runs, the embedding
  /// MUST keep it alive itself (for example by rooting it as part of the queued [`Job`] via
  /// [`Job::add_root`], or by using [`crate::Heap::add_root`]).
  fn host_make_job_callback(&mut self, callback: GcObject) -> JobCallback {
    JobCallback::new(callback)
  }

  /// Calls a host-defined [`JobCallback`] record.
  ///
  /// Stub hook for HTML's `HostCallJobCallback`:
  /// <https://html.spec.whatwg.org/multipage/webappapis.html#hostcalljobcallback>.
  ///
  /// This default implementation is a stub and returns [`VmError::Unimplemented`].
  fn host_call_job_callback(
    &mut self,
    _ctx: &mut dyn VmJobContext,
    _callback: &JobCallback,
    _this_argument: Value,
    _arguments: &[Value],
  ) -> Result<Value, VmError> {
    Err(VmError::Unimplemented("HostCallJobCallback"))
  }

  /// Promise rejection tracker hook (unhandled rejection reporting).
  ///
  /// Stub hook for ECMA-262's `HostPromiseRejectionTracker`:
  /// <https://tc39.es/ecma262/#sec-host-promise-rejection-tracker>.
  ///
  /// HTML's host implementation uses:
  /// - an "about-to-be-notified rejected promises list", and
  /// - an "outstanding rejected promises weak set"
  ///
  /// to later report `unhandledrejection`/`rejectionhandled` events at microtask checkpoints. See:
  /// <https://html.spec.whatwg.org/multipage/webappapis.html#the-hostpromiserejectiontracker-implementation>.
  ///
  /// This default implementation does nothing.
  fn host_promise_rejection_tracker(
    &mut self,
    _promise: PromiseHandle,
    _operation: PromiseRejectionOperation,
  ) {
  }

  /// Returns the list of import attribute keys supported by this host.
  ///
  /// This corresponds to ECMA-262's `HostGetSupportedImportAttributes()`:
  /// <https://tc39.es/ecma262/#sec-hostgetsupportedimportattributes>.
  ///
  /// The default implementation returns an empty list (no attributes supported).
  fn host_get_supported_import_attributes(&self) -> &'static [&'static str] {
    &[]
  }

  /// Load an imported module (host hook).
  ///
  /// This corresponds to ECMA-262's
  /// [`HostLoadImportedModule(referrer, moduleRequest, hostDefined, payload)`](https://tc39.es/ecma262/#sec-HostLoadImportedModule).
  ///
  /// The host environment must perform
  /// `FinishLoadingImportedModule(referrer, moduleRequest, payload, result)` by calling
  /// [`VmModuleLoadingContext::finish_loading_imported_module`], either synchronously or
  /// asynchronously.
  ///
  /// ## Re-entrancy
  ///
  /// The host may call `FinishLoadingImportedModule` synchronously from inside this hook. That
  /// re-enters module graph loading (spec `ContinueModuleLoading`) and may cause nested
  /// `host_load_imported_module` calls.
  ///
  /// ## Caching requirement (ECMA-262)
  ///
  /// If this operation is called multiple times with the same `(referrer, moduleRequest)` pair (as
  /// determined by `ModuleRequestsEqual` / [`crate::module_requests_equal`]) and it completes
  /// normally (i.e. `FinishLoadingImportedModule` is called with `Ok(module)`), then it must
  /// complete with the **same Module Record** each time.
  ///
  /// The `payload` argument is an opaque token owned by the engine; the host must not inspect it.
  fn host_load_imported_module(
    &mut self,
    ctx: &mut dyn VmModuleLoadingContext,
    referrer: ModuleReferrer,
    module_request: ModuleRequest,
    host_defined: HostDefined,
    payload: ModuleLoadPayload,
  ) {
    let _ = host_defined;
    ctx.finish_loading_imported_module(
      referrer,
      module_request,
      payload,
      Err(VmError::Unimplemented("HostLoadImportedModule")),
    );
  }
}
