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

use crate::GcObject;
use crate::Heap;
use crate::PromiseHandle;
use crate::PromiseRejectionOperation;
use crate::RootId;
use crate::Value;
use crate::VmError;
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
/// This is deliberately minimal: jobs are created and stored before the evaluator exists, so the
/// trait doesn't expose evaluator-specific functionality yet.
pub trait VmJobContext {}

/// A spec-shaped representation of an ECMAScript *Job Abstract Closure*.
///
/// In ECMA-262, a "job" is a parameterless abstract closure that can be enqueued and later run by
/// the host (usually as part of a microtask checkpoint).
///
/// This representation is Rust-idiomatic: a job is a boxed `FnOnce` that receives a dynamic
/// [`VmJobContext`] and a mutable reference to [`VmHostHooks`] so it can schedule additional work
/// via host hooks (e.g. Promise job chaining).
pub struct Job {
  kind: JobKind,
  run: Box<dyn FnOnce(&mut dyn VmJobContext, &mut dyn VmHostHooks) -> JobResult + Send + 'static>,
}

impl Job {
  /// Create a new job of `kind` backed by `run`.
  pub fn new(
    kind: JobKind,
    run: impl FnOnce(&mut dyn VmJobContext, &mut dyn VmHostHooks) -> JobResult + Send + 'static,
  ) -> Self {
    Self {
      kind,
      run: Box::new(run),
    }
  }

  /// Returns this job's kind.
  #[inline]
  pub fn kind(&self) -> JobKind {
    self.kind
  }

  /// Run the job, consuming it.
  #[inline]
  pub fn run(self, ctx: &mut dyn VmJobContext, host: &mut dyn VmHostHooks) -> JobResult {
    let Job { run, .. } = self;
    run(ctx, host)
  }
}

impl fmt::Debug for Job {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("Job").field("kind", &self.kind).finish()
  }
}

/// A [`Job`] paired with persistent GC roots that keep captured heap values alive until the job is
/// executed or cancelled.
///
/// Dropping a `RootedJob` without calling [`RootedJob::teardown`] will leak persistent roots
/// (debug builds `debug_assert!` on drop). Hosts should store `RootedJob` values in a
/// [`crate::MicrotaskQueue`] and ensure they are cleaned up via
/// [`crate::MicrotaskQueue::perform_microtask_checkpoint`] or
/// [`crate::MicrotaskQueue::drain_and_cancel`].
pub struct RootedJob {
  job: Option<Job>,
  roots: Vec<RootId>,
}

impl RootedJob {
  /// Create a rooted job with no persistent roots.
  ///
  /// This is only GC-safe if the closure does not capture any GC handles.
  pub fn new(
    kind: JobKind,
    run: impl FnOnce(&mut dyn VmJobContext, &mut dyn VmHostHooks) -> JobResult + Send + 'static,
  ) -> Self {
    Self {
      job: Some(Job::new(kind, run)),
      roots: Vec::new(),
    }
  }

  /// Create a rooted job, registering `roots` as persistent GC roots.
  pub fn new_rooted(
    heap: &mut Heap,
    roots: impl IntoIterator<Item = Value>,
    kind: JobKind,
    run: impl FnOnce(&mut dyn VmJobContext, &mut dyn VmHostHooks) -> JobResult + Send + 'static,
  ) -> Self {
    let roots = roots.into_iter().map(|v| heap.add_root(v)).collect();
    Self {
      job: Some(Job::new(kind, run)),
      roots,
    }
  }

  /// Returns the kind of the underlying job.
  pub fn kind(&self) -> JobKind {
    self
      .job
      .as_ref()
      .expect("RootedJob::kind called after run/teardown")
      .kind()
  }

  /// Runs this job, consuming its closure but keeping its roots until `teardown`.
  pub fn run(&mut self, ctx: &mut dyn VmJobContext, host: &mut dyn VmHostHooks) -> JobResult {
    let job = self
      .job
      .take()
      .expect("RootedJob::run called more than once");
    job.run(ctx, host)
  }

  /// Cancels this job (if it has not run) and removes any persistent roots.
  pub fn teardown(&mut self, heap: &mut Heap) {
    // Drop the job closure first so it releases any captured handles before we unroot.
    self.job.take();
    for id in self.roots.drain(..) {
      heap.remove_root(id);
    }
  }
}

impl fmt::Debug for RootedJob {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RootedJob")
      .field(
        "kind",
        &self.job.as_ref().map(|job| job.kind()).unwrap_or(JobKind::Generic),
      )
      .field("roots", &self.roots.len())
      .finish()
  }
}

impl Drop for RootedJob {
  fn drop(&mut self) {
    debug_assert!(
      self.roots.is_empty(),
      "RootedJob dropped without teardown (persistent roots would leak)"
    );
  }
}

/// A host-defined *JobCallback* record.
///
/// HTML uses JobCallback records to capture the "incumbent settings object" / active script state
/// at the moment a callback is created, and later re-establish that state when calling it.
///
/// In this crate the record is opaque: the host decides what to store. The VM only carries this
/// value around and gives it back to the host when it needs to call the callback.
#[derive(Clone)]
pub struct JobCallback(Arc<dyn std::any::Any + Send + Sync>);

impl JobCallback {
  /// Create a new host-defined JobCallback record.
  ///
  /// The payload is host-defined and can be downcast by the host when the callback is later
  /// invoked.
  pub fn new<T: std::any::Any + Send + Sync>(data: T) -> Self {
    Self(Arc::new(data))
  }

  /// Attempts to downcast the payload by reference.
  pub fn downcast_ref<T: std::any::Any>(&self) -> Option<&T> {
    self.0.downcast_ref::<T>()
  }
}

impl fmt::Debug for JobCallback {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("JobCallback")
      .field("type_id", &self.0.type_id())
      .finish()
  }
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
  fn host_enqueue_promise_job(&mut self, job: RootedJob, realm: Option<RealmId>);

  /// Creates a host-defined [`JobCallback`] record.
  ///
  /// Stub hook for HTML's `HostMakeJobCallback`:
  /// <https://html.spec.whatwg.org/multipage/webappapis.html#hostmakejobcallback>.
  ///
  /// Embeddings that do not need incumbent/active-script propagation can use the default
  /// implementation, which stores the callback object with no extra host-defined metadata.
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
  /// This default implementation does nothing.
  fn host_promise_rejection_tracker(
    &mut self,
    _promise: PromiseHandle,
    _operation: PromiseRejectionOperation,
  ) {
  }
}
