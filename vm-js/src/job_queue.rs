//! ECMAScript jobs ("microtasks") and related host hooks.
//!
//! The ECMAScript specification defines a job queue for Promise reactions and async/await
//! continuations. Web user agents integrate this with the HTML event loop's microtask queue.
//!
//! Relevant specs:
//! - `HostEnqueuePromiseJob` (ECMA-262):
//!   <https://tc39.es/ecma262/#sec-hostenqueuepromisejob>
//! - `HostEnqueuePromiseJob` (HTML):
//!   <https://html.spec.whatwg.org/multipage/webappapis.html#hostenqueuepromisejob>
//! - `HostPromiseRejectionTracker` (ECMA-262):
//!   <https://tc39.es/ecma262/#sec-host-promise-rejection-tracker>
//! - `HostPromiseRejectionTracker` (HTML host implementation):
//!   <https://html.spec.whatwg.org/multipage/webappapis.html#the-hostpromiserejectiontracker-implementation>
//!   (uses the global's "about-to-be-notified rejected promises list" and the "outstanding rejected
//!   promises weak set")

use crate::GcObject;
use crate::VmError;

/// An engine-internal microtask job.
///
/// This corresponds to the ECMAScript "Job" record used by Promise reactions and async/await
/// continuations, but is represented here as an opaque callable to be executed by the embedding.
///
/// The job is passed:
/// - A mutable reference to the runtime state (`R`)
/// - A mutable reference to the host job queue so jobs can enqueue additional microtasks which will
///   run during the same microtask checkpoint.
pub type MicrotaskJob<R> =
  Box<dyn FnOnce(&mut R, &mut dyn JobQueue<R>) -> Result<(), VmError> + 'static>;

/// Opaque handle to a promise object passed to [`JobQueue::host_promise_rejection_tracker`].
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

/// The operation passed to [`JobQueue::host_promise_rejection_tracker`].
///
/// Mirrors the `operation` string argument in the ECMAScript spec.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum PromiseRejectionOperation {
  /// A promise became rejected while having no rejection handlers.
  Reject,
  /// A rejection handler was added to a previously-unhandled rejected promise.
  Handle,
}

/// Host interface for scheduling ECMAScript jobs onto the embedding's microtask queue.
///
/// This is the hook used by the ECMAScript specification algorithms:
/// - `HostEnqueuePromiseJob`
/// - `EnqueueJob`
/// - async function / `await` continuation scheduling
///
/// Embeddings should implement this by forwarding jobs into their microtask queue (e.g. an
/// HTML-shaped event loop).
pub trait JobQueue<R> {
  /// Enqueue a microtask job to be executed during the next microtask checkpoint.
  fn enqueue_microtask(&mut self, job: MicrotaskJob<R>);

  /// Spec-shaped alias for `HostEnqueuePromiseJob`.
  ///
  /// This is equivalent to [`JobQueue::enqueue_microtask`], but named after the ECMAScript host
  /// hook to make call sites more obviously spec-aligned.
  ///
  /// Spec references:
  /// - ECMA-262: <https://tc39.es/ecma262/#sec-hostenqueuepromisejob>
  /// - HTML: <https://html.spec.whatwg.org/multipage/webappapis.html#hostenqueuepromisejob>
  fn host_enqueue_promise_job(&mut self, job: MicrotaskJob<R>) {
    self.enqueue_microtask(job);
  }

  /// Tracks promise rejections for unhandled-rejection reporting.
  ///
  /// This hook corresponds to ECMA-262
  /// [`HostPromiseRejectionTracker(promise, operation)`](https://tc39.es/ecma262/#sec-host-promise-rejection-tracker).
  ///
  /// HTML's host implementation uses:
  /// - an "about-to-be-notified rejected promises list", and
  /// - an "outstanding rejected promises weak set"
  ///
  /// to later report `unhandledrejection`/`rejectionhandled` events at microtask checkpoints. See:
  /// <https://html.spec.whatwg.org/multipage/webappapis.html#the-hostpromiserejectiontracker-implementation>
  ///
  /// ## When the engine must call this hook
  ///
  /// Per ECMA-262, engines must invoke this hook in two scenarios:
  /// - [`PromiseRejectionOperation::Reject`]: when a promise is rejected and there is no rejection
  ///   handler attached.
  /// - [`PromiseRejectionOperation::Handle`]: when a handler is added to a previously unhandled
  ///   rejected promise (i.e. when it becomes handled for the first time).
  ///
  /// The default implementation does nothing.
  fn host_promise_rejection_tracker(
    &mut self,
    _promise: PromiseHandle,
    _operation: PromiseRejectionOperation,
  ) {
  }
}
