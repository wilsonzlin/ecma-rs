//! Promise algorithm scaffolding and Promise-internal-slot types.
//!
//! This module intentionally implements only the parts of the ECMA-262 Promise algorithms that are
//! needed to model *job scheduling* and the HTML integration points:
//!
//! - [`VmHostHooks::host_make_job_callback`] (HTML: `HostMakeJobCallback`)
//! - [`VmHostHooks::host_call_job_callback`] (HTML: `HostCallJobCallback`)
//!
//! In addition to job-scheduling scaffolding, it defines **GC-traceable, spec-shaped record types**
//! for Promise internal slots used by the heap's Promise object representation
//! (`HeapObject::Promise`).
//!
//! The spec requires Promise jobs (reaction jobs and thenable jobs) to call user-provided
//! callbacks via `HostCallJobCallback` so the embedding can re-establish incumbent/entry settings.
//!
//! Finally, this module exposes a minimal engine-internal [`Promise`] record and an [`await_value`]
//! helper that schedules async/`await` continuations as Promise jobs (microtasks) without creating
//! a derived promise.
//!
//! Spec references:
//! - `Await` abstract operation: <https://tc39.es/ecma262/#await>
//! - `PerformPromiseThen`: <https://tc39.es/ecma262/#sec-performpromisethen>
//! - `PromiseReactionJob`: <https://tc39.es/ecma262/#sec-promisereactionjob>
//! - `HostPromiseRejectionTracker`: <https://tc39.es/ecma262/#sec-host-promise-rejection-tracker>

use crate::heap::{Trace, Tracer};
use crate::promise_jobs::new_promise_reaction_job;
use crate::promise_jobs::new_promise_resolve_thenable_job;
use crate::{
  GcObject, Heap, Job, JobCallback, PromiseHandle, PromiseRejectionOperation, Value, VmError,
  VmHostHooks,
};
use std::cell::RefCell;
use std::mem;
use std::rc::Rc;

/// The value of a Promise object's `[[PromiseState]]` internal slot.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PromiseState {
  Pending,
  Fulfilled,
  Rejected,
}

/// The `[[Type]]` of a Promise reaction record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PromiseReactionType {
  Fulfill,
  Reject,
}

/// An ECMAScript PromiseCapability Record.
///
/// Spec reference: <https://tc39.es/ecma262/#sec-promisecapability-records>
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PromiseCapability {
  pub promise: GcObject,
  pub resolve: Value,
  pub reject: Value,
}

impl Trace for PromiseCapability {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    tracer.trace_value(Value::Object(self.promise));
    tracer.trace_value(self.resolve);
    tracer.trace_value(self.reject);
  }
}

/// An ECMAScript PromiseReaction Record stored in a Promise's reaction lists.
///
/// Spec reference: <https://tc39.es/ecma262/#sec-promisereaction-records>
#[derive(Debug, Clone)]
pub struct PromiseReaction {
  /// `[[Capability]]` is either a PromiseCapability record or empty.
  pub capability: Option<PromiseCapability>,
  /// `[[Type]]` is either fulfill or reject.
  pub type_: PromiseReactionType,
  /// `[[Handler]]` is either a host-defined [`JobCallback`] record or empty.
  pub handler: Option<JobCallback>,
}

impl Trace for PromiseReaction {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(cap) = &self.capability {
      cap.trace(tracer);
    }
    if let Some(handler) = &self.handler {
      handler.trace(tracer);
    }
  }
}

/// A spec-shaped Promise reaction record used by job scheduling scaffolding.
///
/// Mirrors ECMA-262's `PromiseReaction` record, but only includes the fields needed for job
/// creation at this scaffolding layer.
#[derive(Debug, Clone)]
pub struct PromiseReactionRecord {
  pub reaction_type: PromiseReactionType,
  /// The reaction handler stored as a host-defined [`JobCallback`] record (or empty).
  pub handler: Option<JobCallback>,
}

fn is_callable(heap: &Heap, value: Value) -> Result<Option<GcObject>, VmError> {
  let Value::Object(obj) = value else {
    return Ok(None);
  };

  match heap.get_function_call_handler(obj) {
    Ok(_) => Ok(Some(obj)),
    Err(VmError::NotCallable) => Ok(None),
    Err(e) => Err(e),
  }
}

/// Implements the "handler normalization" part of ECMA-262's `PerformPromiseThen`.
///
/// When `on_fulfilled` / `on_rejected` are callable, this captures them into host-defined
/// [`JobCallback`] records using [`VmHostHooks::host_make_job_callback`], per the ECMA-262 + HTML
/// integration requirements.
pub fn perform_promise_then(
  host: &mut dyn VmHostHooks,
  heap: &Heap,
  on_fulfilled: Value,
  on_rejected: Value,
) -> Result<(PromiseReactionRecord, PromiseReactionRecord), VmError> {
  let on_fulfilled = is_callable(heap, on_fulfilled)?
    .map(|cb| host.host_make_job_callback(cb));
  let on_rejected = is_callable(heap, on_rejected)?
    .map(|cb| host.host_make_job_callback(cb));

  Ok((
    PromiseReactionRecord {
      reaction_type: PromiseReactionType::Fulfill,
      handler: on_fulfilled,
    },
    PromiseReactionRecord {
      reaction_type: PromiseReactionType::Reject,
      handler: on_rejected,
    },
  ))
}

/// Creates a `PromiseResolveThenableJob` for a thenable resolution, capturing `then_action` as a
/// host-defined [`JobCallback`] record.
///
/// This corresponds to the part of ECMA-262's `CreateResolvingFunctions` that, when `then_action`
/// is callable, creates a `PromiseResolveThenableJob` and enqueues it.
pub fn create_promise_resolve_thenable_job(
  host: &mut dyn VmHostHooks,
  heap: &mut Heap,
  thenable: Value,
  then_action: Value,
  resolve: Value,
  reject: Value,
) -> Result<Option<Job>, VmError> {
  let Some(then_action) = is_callable(heap, then_action)? else {
    return Ok(None);
  };

  let then_job_callback = host.host_make_job_callback(then_action);
  Ok(Some(new_promise_resolve_thenable_job(
    heap,
    thenable,
    then_job_callback,
    resolve,
    reject,
  )?))
}

/// Minimal state for the engine-internal [`Promise`] record.
#[derive(Clone, Copy, Debug, PartialEq)]
enum PromiseRecordState {
  Pending,
  Fulfilled(Value),
  Rejected(Value),
}

struct PromiseInner {
  handle: Option<PromiseHandle>,
  state: PromiseRecordState,
  is_handled: bool,
  fulfill_reactions: Vec<PromiseReactionRecord>,
  reject_reactions: Vec<PromiseReactionRecord>,
}

/// An engine-internal Promise record.
///
/// This is **not** a user-facing `Promise` object implementation; it exists to model Promise job
/// scheduling and rejection tracking for early async/await machinery.
#[derive(Clone)]
pub struct Promise {
  inner: Rc<RefCell<PromiseInner>>,
}

impl Promise {
  /// Create a new pending promise, optionally associated with a host-visible [`PromiseHandle`].
  pub fn pending(handle: Option<PromiseHandle>) -> Self {
    Self {
      inner: Rc::new(RefCell::new(PromiseInner {
        handle,
        state: PromiseRecordState::Pending,
        is_handled: false,
        fulfill_reactions: Vec::new(),
        reject_reactions: Vec::new(),
      })),
    }
  }

  /// Create a new already-fulfilled promise (used for `PromiseResolve` on non-promise values).
  fn fulfilled(value: Value) -> Self {
    Self {
      inner: Rc::new(RefCell::new(PromiseInner {
        handle: None,
        state: PromiseRecordState::Fulfilled(value),
        is_handled: true,
        fulfill_reactions: Vec::new(),
        reject_reactions: Vec::new(),
      })),
    }
  }

  /// Reject this promise with `reason`, enqueueing any rejection reactions as Promise jobs.
  ///
  /// If this promise has no rejection handlers, this will call
  /// [`VmHostHooks::host_promise_rejection_tracker`] with
  /// [`PromiseRejectionOperation::Reject`].
  pub fn reject(&self, host: &mut dyn VmHostHooks, heap: &mut Heap, reason: Value) -> Result<(), VmError> {
    let (handle, should_track_reject, reactions) = {
      let mut inner = self.inner.borrow_mut();
      match inner.state {
        PromiseRecordState::Pending => {}
        PromiseRecordState::Fulfilled(_) | PromiseRecordState::Rejected(_) => return Ok(()),
      }

      inner.state = PromiseRecordState::Rejected(reason);
      let handle = inner.handle;
      let should_track_reject = !inner.is_handled;
      let reactions = mem::take(&mut inner.reject_reactions);
      (handle, should_track_reject, reactions)
    };

    if should_track_reject {
      if let Some(handle) = handle {
        host.host_promise_rejection_tracker(handle, PromiseRejectionOperation::Reject);
      }
    }

    for reaction in reactions {
      host.host_enqueue_promise_job(new_promise_reaction_job(heap, reaction, reason)?, None);
    }

    Ok(())
  }

  fn then_without_result(
    &self,
    host: &mut dyn VmHostHooks,
    heap: &mut Heap,
    on_fulfilled: Value,
    on_rejected: Value,
  ) -> Result<(), VmError> {
    let (fulfill_reaction, reject_reaction) =
      perform_promise_then(host, heap, on_fulfilled, on_rejected)?;

    // `[[PromiseIsHandled]]` bookkeeping for unhandled rejection tracking.
    let has_reject_handler = reject_reaction.handler.is_some();
    let mut inner = self.inner.borrow_mut();
    if has_reject_handler && !inner.is_handled {
      inner.is_handled = true;
      if matches!(inner.state, PromiseRecordState::Rejected(_)) {
        if let Some(handle) = inner.handle {
          host.host_promise_rejection_tracker(handle, PromiseRejectionOperation::Handle);
        }
      }
    }

    match inner.state {
      PromiseRecordState::Pending => {
        inner.fulfill_reactions.push(fulfill_reaction);
        inner.reject_reactions.push(reject_reaction);
      }
      PromiseRecordState::Fulfilled(v) => {
        host.host_enqueue_promise_job(new_promise_reaction_job(heap, fulfill_reaction, v)?, None);
      }
      PromiseRecordState::Rejected(r) => {
        host.host_enqueue_promise_job(new_promise_reaction_job(heap, reject_reaction, r)?, None);
      }
    }

    Ok(())
  }
}

/// A value that can be awaited.
#[derive(Clone)]
pub enum Awaitable {
  /// A non-Promise ECMAScript value.
  Value(Value),
  /// A Promise record.
  Promise(Promise),
}

impl From<Value> for Awaitable {
  fn from(value: Value) -> Self {
    Self::Value(value)
  }
}

impl From<Promise> for Awaitable {
  fn from(value: Promise) -> Self {
    Self::Promise(value)
  }
}

fn promise_resolve(value: Awaitable) -> Promise {
  match value {
    Awaitable::Promise(p) => p,
    Awaitable::Value(v) => Promise::fulfilled(v),
  }
}

/// Spec-shaped helper for async/await continuation scheduling.
///
/// Equivalent to `Await(value)` steps 2–4 + step 9:
/// 1. `promise = PromiseResolve(%Promise%, value)`
/// 2. `PerformPromiseThen(promise, on_fulfilled, on_rejected)` (no derived promise)
pub fn await_value(
  host: &mut dyn VmHostHooks,
  heap: &mut Heap,
  value: Awaitable,
  on_fulfilled: Value,
  on_rejected: Value,
) -> Result<(), VmError> {
  let promise = promise_resolve(value);
  promise.then_without_result(host, heap, on_fulfilled, on_rejected)
}
