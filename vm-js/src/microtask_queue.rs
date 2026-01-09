//! A minimal, engine-supplied microtask queue implementation.
//!
//! This is intended for embeddings that do not (yet) have a full HTML event loop implementation
//! but still need Promise/`queueMicrotask`-like behavior:
//! - FIFO job ordering
//! - "perform a microtask checkpoint" semantics (drain until empty, including jobs enqueued while
//!   running)
//! - teardown support for persistent-root cleanup when reusing a heap across many tests

use std::collections::VecDeque;

use crate::Heap;
use crate::JobQueue;
use crate::RealmId;
use crate::RootedJob;
use crate::RootedMicrotaskJob;
use crate::VmError;
use crate::VmHostHooks;
use crate::VmJobContext;

/// A FIFO microtask queue.
///
/// The queue stores jobs in a [`VecDeque`] and provides a microtask checkpoint runner that drains
/// the queue until empty (including jobs enqueued by jobs during execution).
///
/// This type is generic over the stored job representation:
/// - Use `MicrotaskQueue<RootedJob>` to integrate with [`VmHostHooks`] (spec-shaped Promise jobs).
/// - Use `MicrotaskQueue<RootedMicrotaskJob<R>>` to integrate with [`JobQueue`] (older, generic
///   microtask job interface).
pub struct MicrotaskQueue<J> {
  queue: VecDeque<J>,
}

impl<J> Default for MicrotaskQueue<J> {
  fn default() -> Self {
    Self::new()
  }
}

impl<J> MicrotaskQueue<J> {
  pub fn new() -> Self {
    Self {
      queue: VecDeque::new(),
    }
  }

  /// Enqueue a microtask job.
  pub fn enqueue(&mut self, job: J) {
    self.queue.push_back(job);
  }

  /// Returns whether the queue is empty.
  pub fn is_empty(&self) -> bool {
    self.queue.is_empty()
  }

  /// Returns the number of queued microtasks.
  pub fn len(&self) -> usize {
    self.queue.len()
  }
}

impl MicrotaskQueue<RootedJob> {
  /// Runs all queued microtasks (and any microtasks enqueued while running) until the queue is
  /// empty.
  ///
  /// If a job returns `Err`, this method **continues draining** the queue (HTML reports the
  /// exception and continues). Errors are returned to the caller for reporting.
  pub fn perform_microtask_checkpoint(
    &mut self,
    heap: &mut Heap,
    ctx: &mut dyn VmJobContext,
  ) -> Vec<VmError> {
    let mut errors = Vec::new();
    while let Some(mut job) = self.queue.pop_front() {
      let result = job.run(ctx, self);
      job.teardown(heap);
      if let Err(err) = result {
        errors.push(err);
      }
    }
    errors
  }

  /// Cancels all queued microtasks and removes their persistent roots.
  ///
  /// This is required when tearing down a realm or reusing a heap across many tests.
  pub fn drain_and_cancel(&mut self, heap: &mut Heap) {
    while let Some(mut job) = self.queue.pop_front() {
      job.teardown(heap);
    }
  }

  /// Alias for [`MicrotaskQueue::drain_and_cancel`].
  pub fn clear(&mut self, heap: &mut Heap) {
    self.drain_and_cancel(heap);
  }
}

impl VmHostHooks for MicrotaskQueue<RootedJob> {
  fn host_enqueue_promise_job(&mut self, job: RootedJob, _realm: Option<RealmId>) {
    self.enqueue(job);
  }
}

impl<R> MicrotaskQueue<RootedMicrotaskJob<R>> {
  /// Runs all queued microtasks (and any microtasks enqueued while running) until the queue is
  /// empty.
  ///
  /// If a job returns `Err`, this method **continues draining** the queue (HTML reports the
  /// exception and continues). Errors are returned to the caller for reporting.
  pub fn perform_microtask_checkpoint(&mut self, heap: &mut Heap, runtime: &mut R) -> Vec<VmError> {
    let mut errors = Vec::new();
    while let Some(mut job) = self.queue.pop_front() {
      let result = job.run(runtime, self);
      job.teardown(heap);
      if let Err(err) = result {
        errors.push(err);
      }
    }
    errors
  }

  /// Cancels all queued microtasks and removes their persistent roots.
  pub fn drain_and_cancel(&mut self, heap: &mut Heap) {
    while let Some(mut job) = self.queue.pop_front() {
      job.teardown(heap);
    }
  }

  /// Alias for [`MicrotaskQueue::drain_and_cancel`].
  pub fn clear(&mut self, heap: &mut Heap) {
    self.drain_and_cancel(heap);
  }
}

impl<R> JobQueue<R> for MicrotaskQueue<RootedMicrotaskJob<R>> {
  fn enqueue_microtask(&mut self, job: RootedMicrotaskJob<R>) {
    self.enqueue(job);
  }
}

