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
}

