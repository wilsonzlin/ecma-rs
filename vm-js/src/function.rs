use crate::heap::{PropertyEntry, Trace, Tracer};
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

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum CallHandler {
  Native(NativeFunctionId),
  #[allow(dead_code)]
  EcmaScript,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum ConstructHandler {
  Native(NativeConstructId),
  #[allow(dead_code)]
  EcmaScript,
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
  /// `[[Prototype]]` internal slot (functions are ordinary objects).
  pub(crate) prototype: Option<GcObject>,
  /// `[[Extensible]]` internal slot.
  pub(crate) extensible: bool,
  /// The function's `[[Call]]` internal method.
  pub(crate) call: CallHandler,
  /// The function's `[[Construct]]` internal method (if present).
  pub(crate) construct: Option<ConstructHandler>,
  /// Function `name` metadata (used by `Function.prototype.name`).
  pub(crate) name: GcString,
  /// Function `length` metadata (used by `Function.prototype.length`).
  pub(crate) length: u32,

  /// Own properties (functions are ordinary objects).
  pub(crate) properties: Box<[PropertyEntry]>,

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
      prototype: None,
      extensible: true,
      call: CallHandler::Native(call),
      construct: construct.map(ConstructHandler::Native),
      name,
      length,
      properties: Box::default(),
      bound_target: None,
      bound_this: None,
      bound_args: None,
      realm: None,
      closure_env: None,
    }
  }

  #[allow(dead_code)]
  pub(crate) fn heap_size_bytes(&self) -> usize {
    let bound_args_len = self.bound_args.as_ref().map(|args| args.len()).unwrap_or(0);
    Self::heap_size_bytes_for_bound_args_len_and_property_count(bound_args_len, self.properties.len())
  }

  pub(crate) fn heap_size_bytes_for_bound_args_len_and_property_count(
    bound_args_len: usize,
    property_count: usize,
  ) -> usize {
    let bound_args_bytes = bound_args_len
      .checked_mul(mem::size_of::<Value>())
      .unwrap_or(usize::MAX);
    let props_bytes = property_count
      .checked_mul(mem::size_of::<PropertyEntry>())
      .unwrap_or(usize::MAX);
    mem::size_of::<Self>()
      .checked_add(bound_args_bytes)
      .and_then(|size| size.checked_add(props_bytes))
      .unwrap_or(usize::MAX)
  }
}

impl Trace for JsFunction {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(proto) = self.prototype {
      tracer.trace_value(Value::Object(proto));
    }
    tracer.trace_value(Value::String(self.name));
    for prop in self.properties.iter() {
      prop.trace(tracer);
    }

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
