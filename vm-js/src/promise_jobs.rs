//! Promise job abstract closures.
//!
//! These jobs are enqueued via `HostEnqueuePromiseJob` and run during microtask checkpoints in
//! HTML.

use crate::promise::{PromiseReactionRecord, PromiseReactionType};
use crate::Heap;
use crate::Job;
use crate::JobCallback;
use crate::JobKind;
use crate::RootId;
use crate::Value;
use crate::VmError;

/// Creates a `PromiseReactionJob` job abstract closure.
///
/// Spec reference: <https://tc39.es/ecma262/#sec-promisereactionjob>.
///
/// This implementation routes callback invocation through
/// [`crate::VmHostHooks::host_call_job_callback`], per ECMA-262 and HTML.
pub fn new_promise_reaction_job(
  heap: &mut Heap,
  reaction: PromiseReactionRecord,
  argument: Value,
) -> Result<Job, VmError> {
  let PromiseReactionRecord {
    reaction_type,
    handler,
  } = reaction;
  let callback_obj = handler.as_ref().map(|cb| cb.callback());
  let job = Job::new(JobKind::Promise, move |ctx, host| {
    let Some(job_callback) = &handler else {
      // Spec invariant: `NewPromiseReactionJob` is only constructed with an undefined capability
      // for `Await`, where the handlers are always callable. A missing reject handler would imply
      // a `ThrowCompletion` handler result, which the spec rules out via an assertion.
      //
      // See: https://tc39.es/ecma262/#sec-newpromisereactionjob
      if matches!(reaction_type, PromiseReactionType::Reject) {
        return Err(VmError::InvariantViolation(
          "PromiseReactionJob reject handler is missing while capability is undefined",
        ));
      }
      return Ok(());
    };

    match host.host_call_job_callback(ctx, job_callback, Value::Undefined, &[argument]) {
      Ok(_) => Ok(()),
      Err(VmError::Throw(_)) => Err(VmError::InvariantViolation(
        "PromiseReactionJob handler threw while capability is undefined",
      )),
      Err(e) => Err(e),
    }
  });

  // Jobs are opaque closures and are not traced by the GC; explicitly root captured handles until
  // the job runs.
  //
  // Root all captured values on the stack while we create persistent roots, so a GC triggered by
  // one root allocation cannot collect the other yet-to-be-rooted values.
  let mut scope = heap.scope();
  let mut values = [Value::Undefined; 2];
  let mut value_count = 0usize;
  values[value_count] = argument;
  value_count += 1;
  if let Some(callback_obj) = callback_obj {
    values[value_count] = Value::Object(callback_obj);
    value_count += 1;
  }
  scope.push_roots(&values[..value_count])?;

  let mut roots: Vec<RootId> = Vec::new();
  roots
    .try_reserve_exact(value_count)
    .map_err(|_| VmError::OutOfMemory)?;
  for &value in &values[..value_count] {
    match scope.heap_mut().add_root(value) {
      Ok(id) => roots.push(id),
      Err(e) => {
        for id in roots.drain(..) {
          scope.heap_mut().remove_root(id);
        }
        return Err(e);
      }
    }
  }

  Ok(job.with_roots(roots))
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
) -> Result<Job, VmError> {
  let callback_obj = then_job_callback.callback();
  let job = Job::new(JobKind::Promise, move |ctx, host| {
    match host.host_call_job_callback(ctx, &then_job_callback, thenable, &[resolve, reject]) {
      Ok(_) => Ok(()),
      Err(VmError::Throw(thrown)) => {
        // Spec: if `then` throws, call `reject` with the thrown value.
        ctx.call(host, reject, Value::Undefined, &[thrown])?;
        Ok(())
      }
      Err(e) => Err(e),
    }
  });

  // Root all captured handles until the job runs.
  //
  // Root values on the stack while creating persistent roots to prevent GC from collecting
  // captured handles mid-construction.
  let values = [thenable, Value::Object(callback_obj), resolve, reject];
  let mut scope = heap.scope();
  scope.push_roots(&values)?;

  let mut roots: Vec<RootId> = Vec::new();
  roots
    .try_reserve_exact(values.len())
    .map_err(|_| VmError::OutOfMemory)?;
  for &value in &values {
    match scope.heap_mut().add_root(value) {
      Ok(id) => roots.push(id),
      Err(e) => {
        for id in roots.drain(..) {
          scope.heap_mut().remove_root(id);
        }
        return Err(e);
      }
    }
  }

  Ok(job.with_roots(roots))
}
