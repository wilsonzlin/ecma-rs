use crate::heap::{ObjectBase, Trace, Tracer};
use crate::CompiledFunctionRef;
use crate::{GcEnv, GcObject, GcString, RealmId, Value};
use core::mem;

/// Identifier for a host/native `[[Call]]` implementation.
///
/// The embedding is expected to maintain a dispatch table keyed by this id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NativeFunctionId(pub u32);

/// Identifier for a host/native `[[Construct]]` implementation.
///
/// The embedding is expected to maintain a dispatch table keyed by this id.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct NativeConstructId(pub u32);

/// Identifier for an ECMAScript (user-defined) function's executable body.
///
/// This is intentionally just an id so that function objects can outlive a single `exec_script`
/// invocation without holding any references into ephemeral parser/AST data structures.
///
/// In the future this id can index into a per-realm code table (bytecode, HIR, etc.).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct EcmaFunctionId(pub u32);

/// ECMAScript `[[ThisMode]]` (ECMA-262).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ThisMode {
  /// Arrow functions.
  Lexical,
  /// Strict-mode functions.
  Strict,
  /// Sloppy-mode functions.
  Global,
}

#[derive(Debug, Clone)]
pub(crate) enum CallHandler {
  Native(NativeFunctionId),
  Ecma(EcmaFunctionId),
  User(CompiledFunctionRef),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ConstructHandler {
  Native(NativeConstructId),
  Ecma(EcmaFunctionId),
}

/// Extra per-function internal-slot-like data used by certain built-ins.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum FunctionData {
  None,
  /// Promise resolving function created by `CreateResolvingFunctions`.
  PromiseResolvingFunction { promise: GcObject, is_reject: bool },
  /// Closure function created by `Promise.prototype.finally` when `onFinally` is callable.
  ///
  /// - When `is_reject` is `false`, this is `thenFinally(value)`.
  /// - When `is_reject` is `true`, this is `catchFinally(reason)`.
  PromiseFinallyHandler {
    on_finally: Value,
    constructor: Value,
    is_reject: bool,
  },
  /// Closure function created by `Promise.prototype.finally`:
  /// - `valueThunk()` returns the captured fulfillment value.
  /// - `thrower()` throws the captured rejection reason.
  PromiseFinallyThunk { value: Value, is_throw: bool },
}

/// A JavaScript function object.
///
/// This is intentionally minimal and "spec-shaped":
/// - Functions are heap objects referenced as `Value::Object(GcObject)`.
/// - `[[Call]]` is required.
/// - `[[Construct]]` is optional.
#[derive(Debug)]
#[allow(dead_code)]
pub(crate) struct JsFunction {
  /// The function's `[[Call]]` internal method.
  pub(crate) call: CallHandler,
  /// The function's `[[Construct]]` internal method (if present).
  pub(crate) construct: Option<ConstructHandler>,
  /// Function `name` metadata (used by `Function.prototype.name`).
  pub(crate) name: GcString,
  /// Function `length` metadata (used by `Function.prototype.length`).
  pub(crate) length: u32,
  /// ECMAScript `[[ThisMode]]`.
  pub(crate) this_mode: ThisMode,
  /// Whether the function is strict mode.
  ///
  /// Note: `[[ThisMode]]` depends on strictness for ordinary functions, but strictness also affects
  /// other semantics (early errors, `arguments`, etc), so we store it separately.
  pub(crate) is_strict: bool,

  pub(crate) base: ObjectBase,
  pub(crate) data: FunctionData,

  // Spec-shaped internal slots for function objects.
  //
  // - Bound functions use `bound_target`, `bound_this`, and `bound_args`.
  // - Arrow functions capture their lexical `this`/`new.target` into `bound_this` and
  //   `bound_new_target`.
  //
  // For ordinary functions these remain `None`.
  pub(crate) bound_target: Option<GcObject>,
  pub(crate) bound_this: Option<Value>,
  pub(crate) bound_new_target: Option<Value>,
  pub(crate) bound_args: Option<Box<[Value]>>,
  /// Per-function captured state for native/builtin functions.
  ///
  /// This is the VM's representation of spec "abstract closures" that capture internal slots.
  ///
  /// For example, ECMA-262's `CreateResolvingFunctions(promise)` creates two fresh function objects
  /// (`resolve`/`reject`) that both capture:
  /// - the target promise, and
  /// - a shared `alreadyResolved` record.
  ///
  /// With `native_slots`, an embedding can represent these by allocating two builtin/native
  /// functions that share one captured value (e.g. a small heap object acting as the
  /// `alreadyResolved` record) and each capture the target promise.
  pub(crate) native_slots: Option<Box<[Value]>>,
  /// The function's `[[Realm]]` internal slot.
  ///
  /// For now this is represented as the Realm's global object.
  pub(crate) realm: Option<GcObject>,
  /// Realm identity used when scheduling Promise jobs.
  ///
  /// This is separate from `realm` because jobs need an opaque host-facing [`RealmId`] token,
  /// whereas `realm` is used internally for `this` binding and other semantics.
  pub(crate) job_realm: Option<RealmId>,
  pub(crate) closure_env: Option<GcEnv>,
}

impl JsFunction {
  #[allow(dead_code)]
  pub(crate) fn new_native(
    call: NativeFunctionId,
    construct: Option<NativeConstructId>,
    name: GcString,
    length: u32,
  ) -> Self {
    Self::new_native_with_slots_and_env(call, construct, name, length, None, None)
  }

  pub(crate) fn new_native_with_slots(
    call: NativeFunctionId,
    construct: Option<NativeConstructId>,
    name: GcString,
    length: u32,
    native_slots: Option<Box<[Value]>>,
  ) -> Self {
    Self::new_native_with_slots_and_env(call, construct, name, length, native_slots, None)
  }

  pub(crate) fn new_native_with_slots_and_env(
    call: NativeFunctionId,
    construct: Option<NativeConstructId>,
    name: GcString,
    length: u32,
    native_slots: Option<Box<[Value]>>,
    closure_env: Option<GcEnv>,
  ) -> Self {
    Self {
      call: CallHandler::Native(call),
      construct: construct.map(ConstructHandler::Native),
      name,
      length,
      this_mode: ThisMode::Global,
      is_strict: false,
      base: ObjectBase::new(None),
      data: FunctionData::None,
      bound_target: None,
      bound_this: None,
      bound_new_target: None,
      bound_args: None,
      native_slots,
      realm: None,
      job_realm: None,
      closure_env,
    }
  }

  pub(crate) fn new_ecma(
    code: EcmaFunctionId,
    is_constructable: bool,
    name: GcString,
    length: u32,
    this_mode: ThisMode,
    is_strict: bool,
    closure_env: Option<GcEnv>,
  ) -> Self {
    Self {
      call: CallHandler::Ecma(code),
      construct: if is_constructable {
        Some(ConstructHandler::Ecma(code))
      } else {
        None
      },
      name,
      length,
      this_mode,
      is_strict,
      base: ObjectBase::new(None),
      data: FunctionData::None,
      bound_target: None,
      bound_this: None,
      bound_new_target: None,
      bound_args: None,
      native_slots: None,
      realm: None,
      job_realm: None,
      closure_env,
    }
  }

  pub(crate) fn new_user(func: CompiledFunctionRef, name: GcString, length: u32) -> Self {
    Self {
      call: CallHandler::User(func),
      construct: None,
      name,
      length,
      this_mode: ThisMode::Global,
      is_strict: false,
      base: ObjectBase::new(None),
      data: FunctionData::None,
      bound_target: None,
      bound_this: None,
      bound_new_target: None,
      bound_args: None,
      native_slots: None,
      realm: None,
      job_realm: None,
      closure_env: None,
    }
  }
  pub(crate) fn heap_size_bytes(&self) -> usize {
    let bound_args_len = self.bound_args.as_ref().map(|args| args.len()).unwrap_or(0);
    let native_slots_len = self.native_slots.as_ref().map(|slots| slots.len()).unwrap_or(0);
    let property_count = self.base.property_count();
    Self::heap_size_bytes_for_counts(bound_args_len, native_slots_len, property_count)
  }

  pub(crate) fn heap_size_bytes_for_counts(
    bound_args_len: usize,
    native_slots_len: usize,
    property_count: usize,
  ) -> usize {
    let bound_args_bytes = bound_args_len
      .checked_mul(mem::size_of::<Value>())
      .unwrap_or(usize::MAX);
    let native_slots_bytes = native_slots_len
      .checked_mul(mem::size_of::<Value>())
      .unwrap_or(usize::MAX);
    let props_bytes = ObjectBase::properties_heap_size_bytes_for_count(property_count);
    // Payload bytes owned by this function allocation.
    //
    // Note: `JsFunction` headers are stored inline in the heap slot table, so this size
    // intentionally excludes `mem::size_of::<JsFunction>()` and only counts heap-owned payload
    // allocations.
    bound_args_bytes
      .checked_add(native_slots_bytes)
      .and_then(|b| b.checked_add(props_bytes))
      .unwrap_or(usize::MAX)
  }
}

impl Trace for JsFunction {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    self.base.trace(tracer);
    tracer.trace_value(Value::String(self.name));

    match self.data {
      FunctionData::None => {}
      FunctionData::PromiseResolvingFunction { promise, .. } => {
        tracer.trace_value(Value::Object(promise));
      }
      FunctionData::PromiseFinallyHandler {
        on_finally,
        constructor,
        ..
      } => {
        tracer.trace_value(on_finally);
        tracer.trace_value(constructor);
      }
      FunctionData::PromiseFinallyThunk { value, .. } => {
        tracer.trace_value(value);
      }
    }

    if let Some(target) = self.bound_target {
      tracer.trace_value(Value::Object(target));
    }
    if let Some(bound_this) = self.bound_this {
      tracer.trace_value(bound_this);
    }
    if let Some(bound_new_target) = self.bound_new_target {
      tracer.trace_value(bound_new_target);
    }
    if let Some(bound_args) = &self.bound_args {
      for value in bound_args.iter().copied() {
        tracer.trace_value(value);
      }
    }
    if let Some(native_slots) = &self.native_slots {
      for value in native_slots.iter().copied() {
        tracer.trace_value(value);
      }
    }
    if let Some(realm) = self.realm {
      tracer.trace_value(Value::Object(realm));
    }
    if let Some(env) = self.closure_env {
      tracer.trace_env(env);
    }
  }
}
