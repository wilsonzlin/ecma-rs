//! Promise algorithm scaffolding.
//!
//! This module intentionally implements only the parts of the ECMA-262 Promise algorithms that are
//! needed to model *job scheduling* and the HTML integration points:
//!
//! - [`VmHostHooks::host_make_job_callback`] (HTML: `HostMakeJobCallback`)
//! - [`VmHostHooks::host_call_job_callback`] (HTML: `HostCallJobCallback`)
//!
//! The spec requires Promise jobs (reaction jobs and thenable jobs) to call user-provided
//! callbacks via `HostCallJobCallback` so the embedding can re-establish incumbent/entry settings.

use crate::promise_jobs::new_promise_resolve_thenable_job;
use crate::GcObject;
use crate::Heap;
use crate::Job;
use crate::JobCallback;
use crate::Value;
use crate::VmError;
use crate::VmHostHooks;

/// The `[[Type]]` of a Promise reaction record.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PromiseReactionType {
  Fulfill,
  Reject,
}

/// A spec-shaped Promise reaction record.
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

  match heap.get_function_call_id(obj) {
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
  heap: &Heap,
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
    thenable,
    then_job_callback,
    resolve,
    reject,
  )))
}

