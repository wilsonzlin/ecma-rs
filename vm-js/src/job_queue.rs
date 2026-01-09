//! Minimal microtask/job queue scaffolding.
//!
//! This module exists to provide a small, spec-shaped substrate for embeddings that want an
//! internal queue for Promise jobs / microtasks. The VM currently delegates actual scheduling to
//! the host via [`VmHostHooks::host_enqueue_promise_job`](crate::VmHostHooks::host_enqueue_promise_job),
//! but having a concrete queue type is useful for tests and simple embeddings.

use crate::jobs::Job;
use std::collections::VecDeque;

/// A queued microtask job.
///
/// For now, microtasks are represented directly as [`Job`] records.
pub type MicrotaskJob = Job;

/// A FIFO microtask queue.
#[derive(Default, Debug)]
pub struct JobQueue {
  queue: VecDeque<MicrotaskJob>,
}

impl JobQueue {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn push(&mut self, job: MicrotaskJob) {
    self.queue.push_back(job);
  }

  pub fn pop(&mut self) -> Option<MicrotaskJob> {
    self.queue.pop_front()
  }

  pub fn is_empty(&self) -> bool {
    self.queue.is_empty()
  }

  pub fn len(&self) -> usize {
    self.queue.len()
  }
}

pub use crate::jobs::PromiseHandle;
pub use crate::jobs::PromiseRejectionOperation;

