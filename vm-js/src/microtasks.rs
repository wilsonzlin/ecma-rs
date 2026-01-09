//! A minimal, GC-safe microtask queue for Promise jobs.
//!
//! This is a small host-side container suitable for unit tests and lightweight embeddings that do
//! not yet have a full event loop. It preserves FIFO ordering and implements an HTML-style
//! microtask checkpoint reentrancy guard.

use crate::Job;
use crate::JobCallback;
use crate::RealmId;
use crate::Value;
use crate::VmError;
use crate::VmHostHooks;
use crate::VmJobContext;
use std::collections::VecDeque;

/// A simple, VM-owned microtask queue.
#[derive(Debug, Default)]
pub struct MicrotaskQueue {
  queue: VecDeque<(Option<RealmId>, Job)>,
  performing_microtask_checkpoint: bool,
}

impl MicrotaskQueue {
  /// Creates an empty microtask queue.
  #[inline]
  pub fn new() -> Self {
    Self::default()
  }

  /// Enqueues a Promise job in FIFO order.
  #[inline]
  pub fn enqueue_promise_job(&mut self, job: Job, realm: Option<RealmId>) {
    self.queue.push_back((realm, job));
  }

  /// Returns the number of queued jobs.
  #[inline]
  pub fn len(&self) -> usize {
    self.queue.len()
  }

  /// Returns whether the queue is empty.
  #[inline]
  pub fn is_empty(&self) -> bool {
    self.queue.is_empty()
  }

  pub(crate) fn begin_checkpoint(&mut self) -> bool {
    if self.performing_microtask_checkpoint {
      return false;
    }
    self.performing_microtask_checkpoint = true;
    true
  }

  pub(crate) fn end_checkpoint(&mut self) {
    self.performing_microtask_checkpoint = false;
  }

  pub(crate) fn pop_front(&mut self) -> Option<(Option<RealmId>, Job)> {
    self.queue.pop_front()
  }

  /// Performs a microtask checkpoint (HTML terminology).
  ///
  /// - If a checkpoint is already in progress, this is a no-op (reentrancy guard).
  /// - Otherwise, drains the queue until it becomes empty.
  ///
  /// Any errors returned by jobs are collected and returned; the checkpoint continues to run later
  /// jobs even if earlier ones fail (HTML's "report the exception and keep draining microtasks"
  /// behavior).
  pub fn perform_microtask_checkpoint(&mut self, ctx: &mut dyn VmJobContext) -> Vec<VmError> {
    if self.performing_microtask_checkpoint {
      return Vec::new();
    }

    self.performing_microtask_checkpoint = true;
    let mut errors = Vec::new();
    while let Some((_realm, job)) = self.queue.pop_front() {
      if let Err(err) = job.run(ctx, self) {
        errors.push(err);
      }
    }
    self.performing_microtask_checkpoint = false;
    errors
  }

  /// Tears down all queued jobs without running them.
  ///
  /// This unregisters any persistent roots held by queued jobs. Use this when an embedding needs
  /// to abandon the queue but still intends to reuse the heap.
  pub fn teardown(&mut self, ctx: &mut dyn VmJobContext) {
    while let Some((_realm, job)) = self.queue.pop_front() {
      job.discard(ctx);
    }
  }

  /// Alias for [`MicrotaskQueue::teardown`].
  pub fn cancel_all(&mut self, ctx: &mut dyn VmJobContext) {
    self.teardown(ctx);
  }
}

impl VmHostHooks for MicrotaskQueue {
  fn host_enqueue_promise_job(&mut self, job: Job, realm: Option<RealmId>) {
    self.enqueue_promise_job(job, realm);
  }

  fn host_call_job_callback(
    &mut self,
    ctx: &mut dyn VmJobContext,
    callback: &JobCallback,
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
