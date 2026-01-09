//! Promise job abstract closures.
//!
//! These jobs are enqueued via `HostEnqueuePromiseJob` and run during microtask checkpoints in
//! HTML.

use crate::promise::PromiseReactionRecord;
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
pub fn new_promise_reaction_job(reaction: PromiseReactionRecord, argument: Value) -> Job {
  let handler = reaction.handler;
  Job::new(JobKind::Promise, move |ctx, host| {
    if let Some(job_callback) = &handler {
      host.host_call_job_callback(ctx, job_callback, Value::Undefined, &[argument])?;
    }
    Ok(())
  })
}

/// Creates a `PromiseResolveThenableJob` job abstract closure.
///
/// Spec reference: <https://tc39.es/ecma262/#sec-promiseresolvethenablejob>.
///
/// This implementation routes callback invocation through
/// [`crate::VmHostHooks::host_call_job_callback`], per ECMA-262 and HTML.
pub fn new_promise_resolve_thenable_job(
  thenable: Value,
  then_job_callback: JobCallback,
  resolve: Value,
  reject: Value,
) -> Job {
  Job::new(JobKind::Promise, move |ctx, host| {
    host.host_call_job_callback(ctx, &then_job_callback, thenable, &[resolve, reject])?;
    Ok(())
  })
}
