//! Promise job abstract closures.
//!
//! These jobs are enqueued via `HostEnqueuePromiseJob` and run during microtask checkpoints in
//! HTML.

use crate::promise::PromiseReactionRecord;
use crate::Heap;
use crate::Job;
use crate::JobCallback;
use crate::JobKind;
use crate::Value;

/// Creates a `PromiseReactionJob` job abstract closure.
///
/// Spec reference: <https://tc39.es/ecma262/#sec-promisereactionjob>.
///
/// This implementation routes callback invocation through
/// [`crate::VmHostHooks::host_call_job_callback`], per ECMA-262 and HTML.
pub fn new_promise_reaction_job(heap: &mut Heap, reaction: PromiseReactionRecord, argument: Value) -> Job {
  let handler = reaction.handler;
  let callback_obj = handler.as_ref().map(|cb| cb.callback());
  let mut job = Job::new(JobKind::Promise, move |ctx, host| {
    if let Some(job_callback) = &handler {
      host.host_call_job_callback(ctx, job_callback, Value::Undefined, &[argument])?;
    }
    Ok(())
  });

  // Jobs are opaque closures and are not traced by the GC; explicitly root captured handles until
  // the job runs.
  job.push_root(heap.add_root(argument));
  if let Some(callback_obj) = callback_obj {
    job.push_root(heap.add_root(Value::Object(callback_obj)));
  }

  job
}

/// Creates a `PromiseResolveThenableJob` job abstract closure.
///
/// Spec reference: <https://tc39.es/ecma262/#sec-promiseresolvethenablejob>.
///
/// This implementation routes callback invocation through
/// [`crate::VmHostHooks::host_call_job_callback`], per ECMA-262 and HTML.
pub fn new_promise_resolve_thenable_job(
  heap: &mut Heap,
  thenable: Value,
  then_job_callback: JobCallback,
  resolve: Value,
  reject: Value,
) -> Job {
  let callback_obj = then_job_callback.callback();
  let mut job = Job::new(JobKind::Promise, move |ctx, host| {
    host.host_call_job_callback(ctx, &then_job_callback, thenable, &[resolve, reject])?;
    Ok(())
  });

  // Root all captured handles until the job runs.
  job.push_root(heap.add_root(thenable));
  job.push_root(heap.add_root(Value::Object(callback_obj)));
  job.push_root(heap.add_root(resolve));
  job.push_root(heap.add_root(reject));

  job
}
