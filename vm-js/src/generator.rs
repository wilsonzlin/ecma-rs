//! Generator objects (§27.5) and async-function activations (§27.7).
//!
//! Both are backed by the same mechanism: a [`crate::resumable::ResumableBody`] (an explicit
//! frame stack over the retained AST) stored in a [`crate::heap::HeapObject::Generator`] heap
//! object. Sync generators surface the object directly (with `%GeneratorPrototype%` methods);
//! async functions keep the activation object internal and surface a Promise.
//!
//! Spec anchors:
//! - `GeneratorResume` / `GeneratorResumeAbrupt` (§27.5.3.3–4): implemented by
//!   [`generator_resume`] / [`generator_resume_abrupt`].
//! - `AsyncFunctionStart` (§27.7.5.1) + `Await` (§6.2.4 / §27.7.5.3): implemented by
//!   [`start_async_function`] / [`drive_async_step`] / [`await_continuation_call`], with the
//!   microtask queue provided by the existing promise machinery (`PerformPromiseThen`).
//!
//! Rooting contract: the suspended state (frames' Values/envs, captured environments, `this`) is
//! traced via the generator heap object (`JsGenerator::trace`). During a resume, callers root the
//! generator object itself; the body is additionally kept alive by the `Rc` handle held across
//! the drive loop, and the current environments are rooted by the temporary [`RuntimeEnv`].

use crate::exec::{Completion, Evaluator, FunctionFlavor, RuntimeEnv, Thrown};
use crate::function::FunctionData;
use crate::heap::{GeneratorKind, GeneratorState};
use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::resumable::{drive, DriveOutcome, Feedback, Frame, ListRef, NodeRef, ResumableBody};
use crate::source::SourceText;
use crate::vm::ParsedProgram;
use crate::{GcObject, Scope, Value, Vm, VmError, VmHost, VmHostHooks};

/// Extract a throw completion value from a call-time `VmError`, if it represents a
/// language-level throw (as opposed to OOM / ICE / unimplemented).
fn throw_value_from_error(err: &VmError) -> Option<Value> {
  match err {
    VmError::Throw(v) | VmError::ThrowWithStack { value: v, .. } => Some(*v),
    _ => None,
  }
}
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use std::cell::RefCell;
use std::rc::Rc;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Call-time entry: EvaluateBody for generator / async functions
// ---------------------------------------------------------------------------

/// Called by `Vm::call_ecma_function` instead of `run_ecma_function` when the callee is a
/// generator or async function. Performs FunctionDeclarationInstantiation eagerly (per spec both
/// flavors evaluate parameters before suspending), captures the environments into a
/// [`ResumableBody`], and returns the generator object / result promise.
#[allow(clippy::too_many_arguments)]
pub(crate) fn call_suspendable_function(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  env: &mut RuntimeEnv,
  source: Arc<SourceText>,
  strict: bool,
  this: Value,
  func: &Node<Func>,
  args: &[Value],
  callee: GcObject,
  program: Arc<ParsedProgram>,
) -> Result<Value, VmError> {
  let flavor = FunctionFlavor::of(&func.stx)?;
  env.set_source_info(source.clone(), 0, 0);

  // Async EvaluateBody creates the result promise *before* FDI so parameter
  // evaluation failures reject the promise rather than throw from the call
  // (test262 `dflt-params-ref-self` / `dflt-params-ref-later`).
  let async_result_promise = if matches!(flavor, FunctionFlavor::Async) {
    let intr = vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    let promise = scope.alloc_promise_with_prototype(Some(intr.promise_prototype()))?;
    scope.push_root(Value::Object(promise))?;
    Some(promise)
  } else {
    None
  };

  // FunctionDeclarationInstantiation: bind parameters/vars/functions in the fresh function env.
  // Parameter default-value expressions run here, before first suspension (spec order).
  {
    let mut ev = Evaluator::new_resumable(vm, host, hooks, env, strict, this);
    if let Err(err) = ev.instantiate_function_pub(scope, func, args) {
      if let Some(promise) = async_result_promise {
        if let Some(reason) = throw_value_from_error(&err) {
          crate::builtins::reject_promise(hooks, scope, promise, reason, vm.current_realm())?;
          return Ok(Value::Object(promise));
        }
      }
      return Err(err);
    }
  }

  let lexical_env = env.lexical_env();
  let var_env = env.var_env_env().unwrap_or(lexical_env);
  let global = env.global_object();

  let initial_frame = match &func.stx.body {
    Some(FuncBody::Block(stmts)) => Frame::StmtList {
      list: ListRef::new(stmts),
      idx: 0,
      last: None,
      needs_env: false,
      restore_env: None,
    },
    Some(FuncBody::Expression(expr)) => Frame::ImplicitReturn {
      operand: NodeRef::new(expr),
      started: false,
    },
    None => return Err(VmError::Unimplemented("function without body")),
  };

  let body = Rc::new(RefCell::new(ResumableBody {
    frames: vec![initial_frame],
    lexical_env,
    var_env,
    global,
    this,
    strict,
    program,
    source,
  }));

  match flavor {
    FunctionFlavor::Generator => {
      // OrdinaryCreateFromConstructor(F, "%GeneratorPrototype%"): use F.prototype if an object;
      // otherwise GetFunctionRealm(F)'s %GeneratorPrototype%.
      let active = vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
      let default_proto = vm
        .intrinsics_for_function(scope.heap(), callee)?
        .unwrap_or(active)
        .generator_prototype();
      let mut s = scope.reborrow();
      s.push_root(Value::Object(callee))?;
      s.push_root(this)?;
      s.push_root(Value::Object(default_proto))?;
      let key = PropertyKey::from_string(s.alloc_string("prototype")?);
      let proto_val = s.ordinary_get(vm, callee, key, Value::Object(callee))?;
      let proto = match proto_val {
        Value::Object(o) => o,
        _ => default_proto,
      };
      // `lexical_env`/`var_env` are rooted by the still-active RuntimeEnv, `this` by the root
      // above; the alloc may GC before the body becomes heap-traced.
      let gen = s.alloc_generator(Some(proto), body, GeneratorKind::Sync)?;
      Ok(Value::Object(gen))
    }
    FunctionFlavor::AsyncGenerator => {
      // OrdinaryCreateFromConstructor(F, "%AsyncGeneratorPrototype%").
      let active = vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
      let default_proto = vm
        .intrinsics_for_function(scope.heap(), callee)?
        .unwrap_or(active)
        .async_generator_prototype();
      let mut s = scope.reborrow();
      s.push_root(Value::Object(callee))?;
      s.push_root(this)?;
      s.push_root(Value::Object(default_proto))?;
      let key = PropertyKey::from_string(s.alloc_string("prototype")?);
      let proto_val = s.ordinary_get(vm, callee, key, Value::Object(callee))?;
      let proto = match proto_val {
        Value::Object(o) => o,
        _ => default_proto,
      };
      let gen = s.alloc_generator(Some(proto), body, GeneratorKind::AsyncGenerator)?;
      Ok(Value::Object(gen))
    }
    FunctionFlavor::Async => {
      // Result promise was allocated before FDI; attach the activation and start.
      let result_promise = async_result_promise.ok_or(VmError::InvariantViolation(
        "async call missing preallocated result promise",
      ))?;
      let mut s = scope.reborrow();
      s.push_root(this)?;
      s.push_root(Value::Object(result_promise))?;
      let gen = s.alloc_generator(None, body, GeneratorKind::AsyncFunction)?;
      s.push_root(Value::Object(gen))?;
      s.heap_mut()
        .set_generator_result_promise(gen, result_promise)?;

      drive_async_step(vm, &mut s, host, hooks, gen, Feedback::Start)?;
      Ok(Value::Object(result_promise))
    }
    FunctionFlavor::Normal => Err(VmError::InvariantViolation(
      "normal function routed to suspendable call path",
    )),
  }
}

// ---------------------------------------------------------------------------
// Shared resume driver
// ---------------------------------------------------------------------------

/// Reconstructs the execution context of a suspended body and drives it until the next
/// suspension or completion. On host-level errors the generator is poisoned (completed).
fn resume_body(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  gen: GcObject,
  feedback: Feedback,
) -> Result<DriveOutcome, VmError> {
  let body = scope
    .heap()
    .generator_body(gen)?
    .ok_or(VmError::InvariantViolation("resume of a completed body"))?;

  let (lexical_env, var_env, global, this, strict, source, program) = {
    let b = body.borrow();
    (
      b.lexical_env,
      b.var_env,
      b.global,
      b.this,
      b.strict,
      b.source.clone(),
      b.program.clone(),
    )
  };

  let mut env = RuntimeEnv::new_with_var_env(scope.heap_mut(), global, lexical_env, var_env)?;
  env.set_source_info(source, 0, 0);

  // Keep the originating ParsedProgram on the VM stack so nested function expressions
  // registered during resume (e.g. `await new Promise(function…)`) can retain AST pointers.
  vm.push_program(program);
  let result = {
    let mut ev = Evaluator::new_resumable(vm, host, hooks, &mut env, strict, this);
    drive(&mut ev, scope, &body, feedback)
  };
  vm.pop_program();
  env.teardown(scope.heap_mut());

  if result.is_err() {
    // Host-level error (OOM, budget, ICE): poison the generator so it cannot be resumed into an
    // inconsistent frame stack.
    let _ = scope
      .heap_mut()
      .set_generator_state(gen, GeneratorState::Completed);
    let _ = scope.heap_mut().clear_generator_body(gen);
  }
  result
}

/// Marks completion: state := completed, frames dropped.
fn complete_generator(scope: &mut Scope<'_>, gen: GcObject) -> Result<(), VmError> {
  scope
    .heap_mut()
    .set_generator_state(gen, GeneratorState::Completed)?;
  scope.heap_mut().clear_generator_body(gen)
}

// ---------------------------------------------------------------------------
// Sync generator semantics (§27.5.3)
// ---------------------------------------------------------------------------

/// CreateIterResultObject(value, done).
pub(crate) fn create_iter_result_object(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  value: Value,
  done: bool,
) -> Result<Value, VmError> {
  let proto = vm.intrinsics().map(|i| i.object_prototype());
  let mut s = scope.reborrow();
  s.push_root(value)?;
  let obj = s.alloc_object_with_prototype(proto)?;
  s.push_root(Value::Object(obj))?;

  let value_key = PropertyKey::from_string(s.alloc_string("value")?);
  s.define_property(
    obj,
    value_key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value,
        writable: true,
      },
    },
  )?;
  let done_key = PropertyKey::from_string(s.alloc_string("done")?);
  s.define_property(
    obj,
    done_key,
    PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value: Value::Bool(done),
        writable: true,
      },
    },
  )?;
  Ok(Value::Object(obj))
}

/// GeneratorValidate: `this` must be a generator object not currently executing.
fn generator_validate(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  this: Value,
  method: &str,
) -> Result<GcObject, VmError> {
  let Value::Object(obj) = this else {
    return Err(type_error(vm, scope, host, method)?);
  };
  if !scope.heap().is_generator(obj) {
    return Err(type_error(vm, scope, host, method)?);
  }
  if scope.heap().generator_state(obj)? == GeneratorState::Executing {
    let err =
      crate::builtins::create_type_error(vm, scope, host, "Generator is already executing")?;
    return Err(VmError::Throw(err));
  }
  Ok(obj)
}

fn type_error(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  method: &str,
) -> Result<VmError, VmError> {
  let err = crate::builtins::create_type_error(
    vm,
    scope,
    host,
    &format!("Generator.prototype.{method} called on a non-generator"),
  )?;
  Ok(VmError::Throw(err))
}

/// Routes a sync-generator drive outcome into the `next/return/throw` result protocol.
fn finish_sync_resume(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  gen: GcObject,
  outcome: DriveOutcome,
) -> Result<Value, VmError> {
  match outcome {
    DriveOutcome::Suspended(crate::resumable::SuspendKind::Yield, v) => {
      scope
        .heap_mut()
        .set_generator_state(gen, GeneratorState::SuspendedYield)?;
      create_iter_result_object(vm, scope, v, false)
    }
    DriveOutcome::Suspended(crate::resumable::SuspendKind::Await, _) => {
      complete_generator(scope, gen)?;
      Err(VmError::InvariantViolation(
        "await in a sync generator body",
      ))
    }
    DriveOutcome::Completed(completion) => {
      complete_generator(scope, gen)?;
      match completion {
        Completion::Normal(_) => create_iter_result_object(vm, scope, Value::Undefined, true),
        Completion::Return(v) => create_iter_result_object(vm, scope, v, true),
        Completion::Throw(thrown) => Err(VmError::ThrowWithStack {
          value: thrown.value,
          stack: thrown.stack,
        }),
        Completion::Break(..) | Completion::Continue(..) => Err(VmError::InvariantViolation(
          "loop completion escaped a function body",
        )),
      }
    }
  }
}

/// `Generator.prototype.next(value)` — GeneratorResume (§27.5.3.3).
pub(crate) fn generator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let gen = generator_validate(vm, scope, hooks, this, "next")?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(value)?;

  let state = s.heap().generator_state(gen)?;
  match state {
    GeneratorState::Completed => create_iter_result_object(vm, &mut s, Value::Undefined, true),
    GeneratorState::SuspendedStart | GeneratorState::SuspendedYield => {
      let feedback = if state == GeneratorState::SuspendedStart {
        Feedback::Start
      } else {
        Feedback::Value(value)
      };
      s.heap_mut()
        .set_generator_state(gen, GeneratorState::Executing)?;
      let outcome = resume_body(vm, &mut s, host, hooks, gen, feedback)?;
      finish_sync_resume(vm, &mut s, gen, outcome)
    }
    GeneratorState::Executing => Err(VmError::InvariantViolation(
      "executing state after validation",
    )),
  }
}

/// `Generator.prototype.return(value)` — GeneratorResumeAbrupt with a return completion.
pub(crate) fn generator_prototype_return(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let gen = generator_validate(vm, scope, hooks, this, "return")?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(value)?;

  match s.heap().generator_state(gen)? {
    GeneratorState::Completed => create_iter_result_object(vm, &mut s, value, true),
    GeneratorState::SuspendedStart => {
      // Never started: complete without running the body (no finally blocks exist yet).
      complete_generator(&mut s, gen)?;
      create_iter_result_object(vm, &mut s, value, true)
    }
    GeneratorState::SuspendedYield => {
      s.heap_mut()
        .set_generator_state(gen, GeneratorState::Executing)?;
      let feedback = Feedback::Completion(Completion::Return(value));
      let outcome = resume_body(vm, &mut s, host, hooks, gen, feedback)?;
      finish_sync_resume(vm, &mut s, gen, outcome)
    }
    GeneratorState::Executing => Err(VmError::InvariantViolation(
      "executing state after validation",
    )),
  }
}

/// `Generator.prototype.throw(exception)` — GeneratorResumeAbrupt with a throw completion.
pub(crate) fn generator_prototype_throw(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let gen = generator_validate(vm, scope, hooks, this, "throw")?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(value)?;

  match s.heap().generator_state(gen)? {
    GeneratorState::Completed => Err(VmError::Throw(value)),
    GeneratorState::SuspendedStart => {
      complete_generator(&mut s, gen)?;
      Err(VmError::Throw(value))
    }
    GeneratorState::SuspendedYield => {
      s.heap_mut()
        .set_generator_state(gen, GeneratorState::Executing)?;
      let thrown = Thrown {
        value,
        stack: vm.capture_stack(),
      };
      let feedback = Feedback::Completion(Completion::Throw(thrown));
      let outcome = resume_body(vm, &mut s, host, hooks, gen, feedback)?;
      finish_sync_resume(vm, &mut s, gen, outcome)
    }
    GeneratorState::Executing => Err(VmError::InvariantViolation(
      "executing state after validation",
    )),
  }
}

/// `%IteratorPrototype%[@@iterator]()` — returns `this`.
pub(crate) fn iterator_prototype_iterator(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(this)
}

// ---------------------------------------------------------------------------
// Async function semantics (§27.7.5)
// ---------------------------------------------------------------------------

/// Runs one resumption of an async activation: drives to the next `await` (scheduling the
/// continuation on the awaited promise) or to completion (settling the result promise).
fn drive_async_step(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  gen: GcObject,
  feedback: Feedback,
) -> Result<(), VmError> {
  scope
    .heap_mut()
    .set_generator_state(gen, GeneratorState::Executing)?;
  let outcome = resume_body(vm, scope, host, hooks, gen, feedback)?;

  match outcome {
    DriveOutcome::Suspended(crate::resumable::SuspendKind::Await, awaited) => {
      scope
        .heap_mut()
        .set_generator_state(gen, GeneratorState::SuspendedYield)?;
      schedule_await(vm, scope, hooks, gen, awaited, false)
    }
    DriveOutcome::Suspended(crate::resumable::SuspendKind::Yield, _) => {
      complete_generator(scope, gen)?;
      Err(VmError::InvariantViolation(
        "yield in an async function body",
      ))
    }
    DriveOutcome::Completed(completion) => {
      complete_generator(scope, gen)?;
      let promise =
        scope
          .heap()
          .generator_result_promise(gen)?
          .ok_or(VmError::InvariantViolation(
            "async activation lost its promise",
          ))?;
      let current_realm = vm.current_realm();
      match completion {
        Completion::Normal(_) => {
          crate::builtins::resolve_promise(vm, scope, hooks, promise, Value::Undefined)
        }
        Completion::Return(v) => crate::builtins::resolve_promise(vm, scope, hooks, promise, v),
        Completion::Throw(thrown) => {
          crate::builtins::reject_promise(hooks, scope, promise, thrown.value, current_realm)
        }
        Completion::Break(..) | Completion::Continue(..) => Err(VmError::InvariantViolation(
          "loop completion escaped a function body",
        )),
      }
    }
  }
}

/// Await(value) steps 2–8: resolve the operand to a promise and attach resume continuations.
fn schedule_await(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  hooks: &mut dyn VmHostHooks,
  gen: GcObject,
  awaited: Value,
  deliver_yield: bool,
) -> Result<(), VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let call_id = intr.await_continuation_call();
  let function_prototype = intr.function_prototype();

  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(awaited)?;

  let promise = crate::promise_ops::promise_resolve(vm, &mut s, hooks, awaited)?;
  s.push_root(promise)?;

  let make_continuation = |s: &mut Scope<'_>, is_reject: bool| -> Result<Value, VmError> {
    let name = s.alloc_string("")?;
    let f = s.alloc_native_function(call_id, None, name, 1)?;
    s.push_root(Value::Object(f))?;
    s.heap_mut()
      .object_set_prototype(f, Some(function_prototype))?;
    s.heap_mut().set_function_data(
      f,
      FunctionData::AwaitContinuation {
        generator: gen,
        is_reject,
        deliver_yield,
      },
    )?;
    Ok(Value::Object(f))
  };
  let on_fulfilled = make_continuation(&mut s, false)?;
  let on_rejected = make_continuation(&mut s, true)?;

  crate::promise_ops::perform_promise_then(
    vm,
    &mut s,
    hooks,
    promise,
    Some(on_fulfilled),
    Some(on_rejected),
  )?;
  Ok(())
}

/// The shared native behind both await continuations (fulfilled/rejected).
pub(crate) fn await_continuation_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let FunctionData::AwaitContinuation {
    generator,
    is_reject,
    deliver_yield,
  } = scope.heap().get_function_data(callee)?
  else {
    return Err(VmError::InvariantViolation(
      "await continuation without AwaitContinuation data",
    ));
  };
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(generator))?;
  s.push_root(value)?;

  let kind = s.heap().generator_kind(generator)?;

  // AsyncGeneratorYield fulfillment: deliver to the waiting next/return promise and suspend.
  if deliver_yield && !is_reject {
    async_generator_resolve(vm, &mut s, hooks, generator, value, false)?;
    return Ok(Value::Undefined);
  }

  // A continuation can race with generator completion only through VM bugs; the state machine
  // guarantees exactly one pending continuation per suspended await.
  let feedback = if is_reject {
    Feedback::Completion(Completion::Throw(Thrown {
      value,
      stack: vm.capture_stack(),
    }))
  } else {
    Feedback::Value(value)
  };

  match kind {
    GeneratorKind::AsyncFunction => {
      drive_async_step(vm, &mut s, host, hooks, generator, feedback)?;
    }
    GeneratorKind::AsyncGenerator => {
      drive_async_generator_step(vm, &mut s, host, hooks, generator, feedback)?;
    }
    GeneratorKind::Sync => {
      return Err(VmError::InvariantViolation(
        "await continuation on a sync generator",
      ));
    }
  }
  Ok(Value::Undefined)
}

// ---------------------------------------------------------------------------
// Async generator semantics (§27.6)
// ---------------------------------------------------------------------------

/// Settles the in-flight async-generator request promise with CreateIterResultObject.
fn async_generator_resolve(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  hooks: &mut dyn VmHostHooks,
  gen: GcObject,
  value: Value,
  done: bool,
) -> Result<(), VmError> {
  let promise = scope
    .heap()
    .generator_result_promise(gen)?
    .ok_or(VmError::InvariantViolation(
      "async generator resolve without pending promise",
    ))?;
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(Value::Object(promise))?;
  s.push_root(value)?;
  let iter_result = create_iter_result_object(vm, &mut s, value, done)?;
  s.push_root(iter_result)?;
  crate::builtins::resolve_promise(vm, &mut s, hooks, promise, iter_result)?;
  s.heap_mut().clear_generator_result_promise(gen)?;
  if done {
    complete_generator(&mut s, gen)?;
  } else {
    s.heap_mut()
      .set_generator_state(gen, GeneratorState::SuspendedYield)?;
  }
  Ok(())
}

fn async_generator_reject(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  hooks: &mut dyn VmHostHooks,
  gen: GcObject,
  reason: Value,
) -> Result<(), VmError> {
  let promise = scope
    .heap()
    .generator_result_promise(gen)?
    .ok_or(VmError::InvariantViolation(
      "async generator reject without pending promise",
    ))?;
  let current_realm = vm.current_realm();
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(Value::Object(promise))?;
  s.push_root(reason)?;
  crate::builtins::reject_promise(hooks, &mut s, promise, reason, current_realm)?;
  s.heap_mut().clear_generator_result_promise(gen)?;
  complete_generator(&mut s, gen)?;
  Ok(())
}

fn drive_async_generator_step(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  gen: GcObject,
  feedback: Feedback,
) -> Result<(), VmError> {
  scope
    .heap_mut()
    .set_generator_state(gen, GeneratorState::Executing)?;
  let outcome = resume_body(vm, scope, host, hooks, gen, feedback)?;

  match outcome {
    DriveOutcome::Suspended(crate::resumable::SuspendKind::Await, awaited) => {
      // Keep Executing across await so a second next() cannot steal the resume slot.
      // (for-await / single-outstanding clients wait for the pending promise.)
      schedule_await(vm, scope, hooks, gen, awaited, false)
    }
    DriveOutcome::Suspended(crate::resumable::SuspendKind::Yield, yielded) => {
      // AsyncGeneratorYield: await the yielded value, then deliver to the waiting promise.
      schedule_await(vm, scope, hooks, gen, yielded, true)
    }
    DriveOutcome::Completed(completion) => match completion {
      Completion::Normal(_) => {
        async_generator_resolve(vm, scope, hooks, gen, Value::Undefined, true)
      }
      Completion::Return(v) => async_generator_resolve(vm, scope, hooks, gen, v, true),
      Completion::Throw(thrown) => async_generator_reject(vm, scope, hooks, gen, thrown.value),
      Completion::Break(..) | Completion::Continue(..) => Err(VmError::InvariantViolation(
        "loop completion escaped a function body",
      )),
    },
  }
}

fn async_generator_validate(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  this: Value,
  method: &str,
) -> Result<GcObject, VmError> {
  let Value::Object(obj) = this else {
    return Err(async_gen_type_error(vm, scope, host, method)?);
  };
  if !scope.heap().is_generator(obj)
    || scope.heap().generator_kind(obj)? != GeneratorKind::AsyncGenerator
  {
    return Err(async_gen_type_error(vm, scope, host, method)?);
  }
  Ok(obj)
}

fn async_gen_type_error(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHostHooks,
  method: &str,
) -> Result<VmError, VmError> {
  let err = crate::builtins::create_type_error(
    vm,
    scope,
    host,
    &format!("AsyncGenerator.prototype.{method} called on incompatible receiver"),
  )?;
  Ok(VmError::Throw(err))
}

/// Allocates the promise returned by async-generator next/return/throw and stores it as pending.
fn async_generator_enqueue_promise(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  gen: GcObject,
) -> Result<GcObject, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let promise_proto = intr.promise_prototype();
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  let promise = s.alloc_promise_with_prototype(Some(promise_proto))?;
  s.push_root(Value::Object(promise))?;
  s.heap_mut().set_generator_result_promise(gen, promise)?;
  Ok(promise)
}

/// `AsyncGenerator.prototype.next(value)` — returns a Promise for the next iter result.
pub(crate) fn async_generator_prototype_next(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let gen = async_generator_validate(vm, scope, hooks, this, "next")?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(value)?;

  let promise = async_generator_enqueue_promise(vm, &mut s, gen)?;
  s.push_root(Value::Object(promise))?;

  match s.heap().generator_state(gen)? {
    GeneratorState::Completed => {
      async_generator_resolve(vm, &mut s, hooks, gen, Value::Undefined, true)?;
    }
    GeneratorState::Executing => {
      // Concurrent next while awaiting: not yet queued (explicit residual).
      return Err(VmError::Unimplemented(
        "async generator concurrent next/return/throw while executing",
      ));
    }
    GeneratorState::SuspendedStart | GeneratorState::SuspendedYield => {
      let feedback = if s.heap().generator_state(gen)? == GeneratorState::SuspendedStart {
        Feedback::Start
      } else {
        Feedback::Value(value)
      };
      drive_async_generator_step(vm, &mut s, host, hooks, gen, feedback)?;
    }
  }
  Ok(Value::Object(promise))
}

/// `AsyncGenerator.prototype.return(value)`.
pub(crate) fn async_generator_prototype_return(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let gen = async_generator_validate(vm, scope, hooks, this, "return")?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(value)?;

  let promise = async_generator_enqueue_promise(vm, &mut s, gen)?;
  s.push_root(Value::Object(promise))?;

  match s.heap().generator_state(gen)? {
    GeneratorState::Completed => {
      async_generator_resolve(vm, &mut s, hooks, gen, value, true)?;
    }
    GeneratorState::Executing => {
      return Err(VmError::Unimplemented(
        "async generator concurrent next/return/throw while executing",
      ));
    }
    GeneratorState::SuspendedStart => {
      // Never started: complete without running the body.
      async_generator_resolve(vm, &mut s, hooks, gen, value, true)?;
    }
    GeneratorState::SuspendedYield => {
      let feedback = Feedback::Completion(Completion::Return(value));
      drive_async_generator_step(vm, &mut s, host, hooks, gen, feedback)?;
    }
  }
  Ok(Value::Object(promise))
}

/// `AsyncGenerator.prototype.throw(exception)`.
pub(crate) fn async_generator_prototype_throw(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let gen = async_generator_validate(vm, scope, hooks, this, "throw")?;
  let value = args.first().copied().unwrap_or(Value::Undefined);
  let mut s = scope.reborrow();
  s.push_root(Value::Object(gen))?;
  s.push_root(value)?;

  let promise = async_generator_enqueue_promise(vm, &mut s, gen)?;
  s.push_root(Value::Object(promise))?;

  match s.heap().generator_state(gen)? {
    GeneratorState::Completed | GeneratorState::SuspendedStart => {
      async_generator_reject(vm, &mut s, hooks, gen, value)?;
    }
    GeneratorState::Executing => {
      return Err(VmError::Unimplemented(
        "async generator concurrent next/return/throw while executing",
      ));
    }
    GeneratorState::SuspendedYield => {
      let thrown = Thrown {
        value,
        stack: vm.capture_stack(),
      };
      let feedback = Feedback::Completion(Completion::Throw(thrown));
      drive_async_generator_step(vm, &mut s, host, hooks, gen, feedback)?;
    }
  }
  Ok(Value::Object(promise))
}
