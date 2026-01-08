//! `vm-js` adapter for the `webidl` conversion/runtime traits.
//!
//! This crate exists as integration scaffolding: it makes the `webidl` crate usable from real
//! embeddings while the JS VM is still incomplete. Missing VM functionality is reported explicitly
//! via `VmError::Unimplemented`.

use vm_js::{GcObject, GcString, GcSymbol, Heap, Value, VmError};
use webidl::{InterfaceId, IteratorResult, JsRuntime, PropertyKey, WebIdlHooks, WebIdlLimits};

/// `webidl` conversion context backed by `vm-js`.
pub struct VmJsWebIdlCx<'a> {
  pub heap: &'a mut Heap,
  pub limits: WebIdlLimits,
  pub hooks: &'a dyn WebIdlHooks<Value>,
}

impl<'a> VmJsWebIdlCx<'a> {
  pub fn new(heap: &'a mut Heap, limits: WebIdlLimits, hooks: &'a dyn WebIdlHooks<Value>) -> Self {
    Self { heap, limits, hooks }
  }

  /// Convenience helper: `hooks.is_platform_object`.
  #[inline]
  pub fn is_platform_object(&self, value: Value) -> bool {
    self.hooks.is_platform_object(value)
  }

  /// Convenience helper: `hooks.implements_interface`.
  #[inline]
  pub fn implements_interface(&self, value: Value, interface: InterfaceId) -> bool {
    self.hooks.implements_interface(value, interface)
  }
}

impl JsRuntime for VmJsWebIdlCx<'_> {
  type Value = Value;
  type String = GcString;
  type Object = GcObject;
  type Symbol = GcSymbol;
  type Error = VmError;

  fn limits(&self) -> WebIdlLimits {
    self.limits
  }

  fn hooks(&self) -> &dyn WebIdlHooks<Self::Value> {
    self.hooks
  }

  fn is_undefined(&self, value: Self::Value) -> bool {
    matches!(value, Value::Undefined)
  }

  fn is_null(&self, value: Self::Value) -> bool {
    matches!(value, Value::Null)
  }

  fn is_boolean(&self, value: Self::Value) -> bool {
    matches!(value, Value::Bool(_))
  }

  fn is_number(&self, value: Self::Value) -> bool {
    matches!(value, Value::Number(_))
  }

  fn is_string(&self, value: Self::Value) -> bool {
    matches!(value, Value::String(_))
  }

  fn is_symbol(&self, value: Self::Value) -> bool {
    matches!(value, Value::Symbol(_))
  }

  fn is_object(&self, value: Self::Value) -> bool {
    matches!(value, Value::Object(_))
  }

  fn as_string(&self, value: Self::Value) -> Option<Self::String> {
    match value {
      Value::String(s) => Some(s),
      _ => None,
    }
  }

  fn as_object(&self, value: Self::Value) -> Option<Self::Object> {
    match value {
      Value::Object(o) => Some(o),
      _ => None,
    }
  }

  fn as_symbol(&self, value: Self::Value) -> Option<Self::Symbol> {
    match value {
      Value::Symbol(s) => Some(s),
      _ => None,
    }
  }

  fn to_boolean(&mut self, value: Self::Value) -> Result<bool, Self::Error> {
    Ok(match value {
      Value::Undefined | Value::Null => false,
      Value::Bool(b) => b,
      Value::Number(n) => !(n == 0.0 || n.is_nan()),
      Value::String(s) => !self.heap.get_string(s)?.is_empty(),
      Value::Symbol(_) | Value::Object(_) => true,
    })
  }

  fn to_string(&mut self, value: Self::Value) -> Result<Self::String, Self::Error> {
    match value {
      Value::String(s) => Ok(s),
      other => self.heap.to_string(other),
    }
  }

  fn to_number(&mut self, value: Self::Value) -> Result<f64, Self::Error> {
    match value {
      Value::Number(n) => Ok(n),
      Value::Bool(true) => Ok(1.0),
      Value::Bool(false) => Ok(0.0),
      _ => Err(VmError::Unimplemented(
        "ToNumber requires interpreter + built-ins (numeric conversion)",
      )),
    }
  }

  fn get(
    &mut self,
    _object: Self::Object,
    _key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Self::Value, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL Get requires an object property model (Get/[[Get]] semantics)",
    ))
  }

  fn get_method(
    &mut self,
    _object: Self::Object,
    _key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<Self::Value>, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL GetMethod requires an object property model (Get/Callability semantics)",
    ))
  }

  fn own_property_keys(
    &mut self,
    _object: Self::Object,
  ) -> Result<Vec<PropertyKey<Self::String, Self::Symbol>>, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL OwnPropertyKeys requires object internal methods (OwnPropertyKeys)",
    ))
  }

  fn get_iterator(&mut self, _value: Self::Value) -> Result<Self::Object, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL iterable conversions require iterator protocol (GetIterator, IteratorNext)",
    ))
  }

  fn iterator_next(&mut self, _iterator: Self::Object) -> Result<IteratorResult<Self::Value>, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL iterable conversions require iterator protocol (IteratorNext)",
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::VmJsWebIdlCx;
  use vm_js::{Heap, HeapLimits, Value};
  use webidl::{conversions, InterfaceId, WebIdlHooks, WebIdlLimits};

  struct NoHooks;

  impl WebIdlHooks<Value> for NoHooks {
    fn is_platform_object(&self, _value: Value) -> bool {
      false
    }

    fn implements_interface(&self, _value: Value, _interface: InterfaceId) -> bool {
      false
    }
  }

  #[test]
  fn domstring_smoke_roundtrips_code_units() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

    let units: Vec<u16> = vec![0x0041, 0xD83D, 0xDE00, 0x0000, 0xFFFF];
    let s = {
      let mut scope = heap.scope();
      scope
        .alloc_string_from_code_units(&units)
        .expect("alloc string")
    };
    let _root = heap.add_root(Value::String(s));

    let hooks = NoHooks;
    let mut cx = VmJsWebIdlCx::new(&mut heap, WebIdlLimits::default(), &hooks);

    let out = conversions::dom_string(&mut cx, Value::String(s)).expect("DOMString conversion");
    drop(cx);

    let out_units = heap.get_string(out).expect("get string").as_code_units();
    assert_eq!(out_units, units.as_slice());
  }
}

