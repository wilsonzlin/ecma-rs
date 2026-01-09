use crate::heap::{ObjectBase, Trace, Tracer};
use crate::{GcEnv, GcObject, GcString, Value};
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CallHandler {
  Native(NativeFunctionId),
  Ecma(EcmaFunctionId),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ConstructHandler {
  Native(NativeConstructId),
  Ecma(EcmaFunctionId),
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

  // Forward-compat internal slots (currently unused but spec-aligned).
  pub(crate) bound_target: Option<GcObject>,
  pub(crate) bound_this: Option<Value>,
  pub(crate) bound_args: Option<Box<[Value]>>,
  pub(crate) realm: Option<GcObject>,
  pub(crate) closure_env: Option<GcEnv>,
}

impl JsFunction {
  pub(crate) fn new_native(
    call: NativeFunctionId,
    construct: Option<NativeConstructId>,
    name: GcString,
    length: u32,
  ) -> Self {
    Self {
      call: CallHandler::Native(call),
      construct: construct.map(ConstructHandler::Native),
      name,
      length,
      this_mode: ThisMode::Global,
      is_strict: false,
      base: ObjectBase::new(None),
      bound_target: None,
      bound_this: None,
      bound_args: None,
      realm: None,
      closure_env: None,
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
      bound_target: None,
      bound_this: None,
      bound_args: None,
      realm: None,
      closure_env,
    }
  }
  pub(crate) fn heap_size_bytes(&self) -> usize {
    let bound_args_len = self.bound_args.as_ref().map(|args| args.len()).unwrap_or(0);
    let property_count = self.base.property_count();
    Self::heap_size_bytes_for_bound_args_len_and_property_count(bound_args_len, property_count)
  }

  pub(crate) fn heap_size_bytes_for_bound_args_len_and_property_count(
    bound_args_len: usize,
    property_count: usize,
  ) -> usize {
    let bound_args_bytes = bound_args_len
      .checked_mul(mem::size_of::<Value>())
      .unwrap_or(usize::MAX);
    let props_bytes = ObjectBase::properties_heap_size_bytes_for_count(property_count);
    mem::size_of::<Self>()
      .checked_add(bound_args_bytes)
      .and_then(|size| size.checked_add(props_bytes))
      .unwrap_or(usize::MAX)
  }
}

impl Trace for JsFunction {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    self.base.trace(tracer);
    tracer.trace_value(Value::String(self.name));

    if let Some(target) = self.bound_target {
      tracer.trace_value(Value::Object(target));
    }
    if let Some(bound_this) = self.bound_this {
      tracer.trace_value(bound_this);
    }
    if let Some(bound_args) = &self.bound_args {
      for value in bound_args.iter().copied() {
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
