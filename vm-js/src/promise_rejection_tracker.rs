//! Spec-aligned helper for HTML-style promise rejection tracking.
//!
//! ECMA-262 defines the `HostPromiseRejectionTracker(promise, operation)` hook:
//! <https://tc39.es/ecma262/#sec-host-promise-rejection-tracker>.
//!
//! HTML provides a concrete host implementation based on two per-global data structures:
//! - the **about-to-be-notified rejected promises list** (strongly referenced), and
//! - the **outstanding rejected promises weak set** (weakly referenced).
//!
//! See: <https://html.spec.whatwg.org/multipage/webappapis.html#the-hostpromiserejectiontracker-implementation>
//!
//! This module provides a small, embedding-friendly state machine that is:
//! - **spec-shaped** (matches HTML's algorithm structure), and
//! - **GC-safe** (keeps promises alive only when required).
//!
//! The tracker is intentionally independent of Promise internals. The embedding is responsible
//! for determining whether the promise became handled during `unhandledrejection` dispatch and
//! passing that fact to [`PromiseRejectionTracker::after_unhandledrejection_dispatch`].

use crate::{Heap, PromiseHandle, RootId, Value, WeakGcObject};
use std::collections::HashSet;
use std::mem;

/// The action requested when a previously-unhandled rejected promise becomes handled.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PromiseRejectionHandleAction {
  /// No further action is required.
  None,
  /// Queue a `rejectionhandled` notification for `promise`.
  QueueRejectionHandled { promise: PromiseHandle },
}

#[derive(Debug, Clone, Copy)]
struct AboutToBeNotifiedEntry {
  promise: PromiseHandle,
  root: RootId,
}

/// A reusable implementation of HTML's promise rejection tracking state.
#[derive(Debug, Default)]
pub struct PromiseRejectionTracker {
  /// Strong references (via persistent roots) to promises that are about to be notified.
  about_to_be_notified: Vec<AboutToBeNotifiedEntry>,
  /// Weak set of promises that were reported as unhandled and have not yet had
  /// `rejectionhandled` dispatched.
  outstanding_rejected: HashSet<WeakGcObject>,
}

impl PromiseRejectionTracker {
  /// Creates a new empty tracker.
  pub fn new() -> Self {
    Self::default()
  }

  /// Called when the engine reports `HostPromiseRejectionTracker(promise, "reject")`.
  ///
  /// This roots `promise` and appends it to the about-to-be-notified list.
  pub fn on_reject(&mut self, heap: &mut Heap, promise: PromiseHandle) {
    // Best-effort: if we cannot allocate the persistent root or grow the internal queue, skip
    // tracking. Under OOM conditions the host is unlikely to be able to dispatch the corresponding
    // `unhandledrejection` event anyway.
    let Ok(root) = heap.add_root(Value::Object(promise.into())) else {
      return;
    };
    if self.about_to_be_notified.try_reserve_exact(1).is_err() {
      heap.remove_root(root);
      return;
    }
    self.about_to_be_notified.push(AboutToBeNotifiedEntry { promise, root });
  }

  /// Called when the engine reports `HostPromiseRejectionTracker(promise, "handle")`.
  pub fn on_handle(
    &mut self,
    heap: &mut Heap,
    promise: PromiseHandle,
  ) -> PromiseRejectionHandleAction {
    if let Some(idx) = self
      .about_to_be_notified
      .iter()
      .position(|entry| entry.promise == promise)
    {
      let entry = self.about_to_be_notified.remove(idx);
      heap.remove_root(entry.root);
      return PromiseRejectionHandleAction::None;
    }

    let promise_obj = crate::GcObject::from(promise);
    let weak = WeakGcObject::from(promise_obj);
    if self.outstanding_rejected.remove(&weak) {
      return PromiseRejectionHandleAction::QueueRejectionHandled { promise };
    }

    PromiseRejectionHandleAction::None
  }

  /// Drains the about-to-be-notified list into a host-owned batch.
  ///
  /// The returned batch keeps the promises alive until the host calls
  /// [`AboutToBeNotifiedBatch::teardown`].
  pub fn drain_about_to_be_notified(&mut self, heap: &mut Heap) -> AboutToBeNotifiedBatch {
    #[cfg(debug_assertions)]
    {
      let heap_ref: &Heap = &*heap;
      for entry in &self.about_to_be_notified {
        debug_assert_eq!(
          heap_ref.get_root(entry.root),
          Some(Value::Object(entry.promise.into())),
          "PromiseRejectionTracker invariant violated: about-to-be-notified root does not match"
        );
      }
    }

    let len = self.about_to_be_notified.len();
    let mut promises = Vec::new();
    let mut roots = Vec::new();
    if promises.try_reserve_exact(len).is_err() || roots.try_reserve_exact(len).is_err() {
      return AboutToBeNotifiedBatch {
        promises,
        roots,
        // Empty batch: nothing to tear down.
        torn_down: true,
      };
    }

    let entries = mem::take(&mut self.about_to_be_notified);
    for entry in entries {
      promises.push(entry.promise);
      roots.push(entry.root);
    }

    AboutToBeNotifiedBatch {
      promises,
      roots,
      torn_down: false,
    }
  }

  /// Called after the host fires `unhandledrejection` for `promise`.
  ///
  /// If the rejection remains unhandled, the promise is appended to the outstanding rejected
  /// promises weak set. If it became handled during event dispatch, no action is taken.
  pub fn after_unhandledrejection_dispatch(
    &mut self,
    promise: PromiseHandle,
    is_handled_after_event: bool,
  ) {
    if is_handled_after_event {
      return;
    }
    let promise_obj = crate::GcObject::from(promise);
    self
      .outstanding_rejected
      .insert(WeakGcObject::from(promise_obj));
  }
}

/// A drained batch of promises to be notified as unhandled rejections.
#[must_use]
pub struct AboutToBeNotifiedBatch {
  promises: Vec<PromiseHandle>,
  roots: Vec<RootId>,
  torn_down: bool,
}

impl AboutToBeNotifiedBatch {
  /// Returns the promises that need to be processed by the host.
  pub fn promises(&self) -> &[PromiseHandle] {
    &self.promises
  }

  /// Removes the persistent roots held by this batch.
  pub fn teardown(mut self, heap: &mut Heap) {
    for root in self.roots.drain(..) {
      heap.remove_root(root);
    }
    self.torn_down = true;
  }
}

impl Drop for AboutToBeNotifiedBatch {
  fn drop(&mut self) {
    debug_assert!(
      self.torn_down,
      "AboutToBeNotifiedBatch dropped without calling teardown(); this leaks persistent roots"
    );
  }
}
