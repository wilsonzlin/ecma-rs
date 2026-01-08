use std::collections::HashMap;
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering as AtomicOrdering};
use std::sync::{Arc, Condvar, Mutex};
use std::time::{Duration, Instant};

/// A cooperative cancellation token that can be toggled by [`TimeoutManager`].
///
/// The token is intentionally minimal: it only needs to support being cancelled
/// once a timeout deadline is reached.
pub trait CancellationToken: Send + Sync + 'static {
  fn cancel(&self);
}

impl CancellationToken for Arc<AtomicBool> {
  fn cancel(&self) {
    self.store(true, AtomicOrdering::Relaxed);
  }
}

pub struct TimeoutManager {
  inner: Arc<TimeoutManagerInner>,
  next_id: AtomicUsize,
  thread: Mutex<Option<std::thread::JoinHandle<()>>>,
}

struct TimeoutManagerInner {
  state: Mutex<TimeoutManagerState>,
  cv: Condvar,
}

struct TimeoutManagerState {
  active: HashMap<usize, TimeoutEntry>,
  shutdown: bool,
}

struct TimeoutEntry {
  deadline: Instant,
  cancel: Box<dyn CancellationToken>,
  cancelled: bool,
}

pub struct TimeoutGuard {
  id: usize,
  inner: Arc<TimeoutManagerInner>,
}

impl TimeoutManager {
  pub fn new() -> Self {
    let inner = Arc::new(TimeoutManagerInner {
      state: Mutex::new(TimeoutManagerState {
        active: HashMap::new(),
        shutdown: false,
      }),
      cv: Condvar::new(),
    });

    let thread_inner = Arc::clone(&inner);
    let handle = std::thread::spawn(move || timeout_thread(thread_inner));

    Self {
      inner,
      next_id: AtomicUsize::new(1),
      thread: Mutex::new(Some(handle)),
    }
  }

  pub fn register<T: CancellationToken>(&self, deadline: Instant, cancel: T) -> TimeoutGuard {
    let id = self.next_id.fetch_add(1, AtomicOrdering::Relaxed);
    let mut state = self.inner.state.lock().unwrap();
    state.active.insert(
      id,
      TimeoutEntry {
        deadline,
        cancel: Box::new(cancel),
        cancelled: false,
      },
    );
    self.inner.cv.notify_one();
    TimeoutGuard {
      id,
      inner: Arc::clone(&self.inner),
    }
  }
}

impl Default for TimeoutManager {
  fn default() -> Self {
    Self::new()
  }
}

impl Drop for TimeoutManager {
  fn drop(&mut self) {
    {
      let mut state = self.inner.state.lock().unwrap();
      state.shutdown = true;
      self.inner.cv.notify_one();
    }

    if let Some(handle) = self.thread.lock().unwrap().take() {
      let _ = handle.join();
    }
  }
}

impl Drop for TimeoutGuard {
  fn drop(&mut self) {
    let mut state = self.inner.state.lock().unwrap();
    state.active.remove(&self.id);
    self.inner.cv.notify_one();
  }
}

fn timeout_thread(inner: Arc<TimeoutManagerInner>) {
  let mut guard = inner.state.lock().unwrap();
  loop {
    if guard.shutdown {
      return;
    }

    let now = Instant::now();
    let mut next_deadline: Option<Instant> = None;

    for entry in guard.active.values_mut() {
      if entry.cancelled {
        continue;
      }
      if now >= entry.deadline {
        entry.cancelled = true;
        entry.cancel.cancel();
        continue;
      }

      next_deadline = match next_deadline {
        Some(existing) => Some(existing.min(entry.deadline)),
        None => Some(entry.deadline),
      };
    }

    if let Some(deadline) = next_deadline {
      let wait_for = deadline
        .checked_duration_since(now)
        .unwrap_or_else(|| Duration::from_millis(0));
      let (new_guard, _) = inner.cv.wait_timeout(guard, wait_for).unwrap();
      guard = new_guard;
    } else {
      guard = inner.cv.wait(guard).unwrap();
    }
  }
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn timeout_cancels_token() {
    let manager = TimeoutManager::new();
    let cancelled = Arc::new(AtomicBool::new(false));
    let deadline = Instant::now() + Duration::from_millis(10);
    let _guard = manager.register(deadline, Arc::clone(&cancelled));

    // Wait a bit longer than the deadline.
    std::thread::sleep(Duration::from_millis(50));
    assert!(cancelled.load(AtomicOrdering::Relaxed));
  }
}
