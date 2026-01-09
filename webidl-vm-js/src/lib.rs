//! `vm-js` adapter for the `webidl` conversion/runtime traits.
//!
//! This crate exists as integration scaffolding: it makes the `webidl` crate usable from real
//! embeddings while the JS VM is still incomplete. Missing VM functionality is reported explicitly
//! via `VmError::Unimplemented`.

use vm_js::{
  GcObject, GcString, GcSymbol, Heap, PropertyDescriptor, PropertyKey as VmPropertyKey, PropertyKind,
  RootId, Value, VmError,
};
use webidl::{
  InterfaceId, IteratorResult, JsRuntime, PropertyKey, WebIdlHooks, WebIdlLimits, WellKnownSymbol,
};

/// `webidl` conversion context backed by `vm-js`.
pub struct VmJsWebIdlCx<'a> {
  pub heap: &'a mut Heap,
  pub limits: WebIdlLimits,
  pub hooks: &'a dyn WebIdlHooks<Value>,
  temp_roots: Vec<RootId>,
}

impl<'a> VmJsWebIdlCx<'a> {
  pub fn new(heap: &'a mut Heap, limits: WebIdlLimits, hooks: &'a dyn WebIdlHooks<Value>) -> Self {
    Self {
      heap,
      limits,
      hooks,
      temp_roots: Vec::new(),
    }
  }

  fn root_temp(&mut self, value: Value) {
    match value {
      Value::String(_) | Value::Symbol(_) | Value::Object(_) => {
        // WebIDL conversions are host-driven and may hold VM handles in local Rust variables across
        // allocations. Root them conservatively for the lifetime of the conversion context so GC
        // can't invalidate handles mid-conversion.
        let id = self.heap.add_root(value);
        self.temp_roots.push(id);
      }
      Value::Undefined | Value::Null | Value::Bool(_) | Value::Number(_) => {}
    }
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

impl Drop for VmJsWebIdlCx<'_> {
  fn drop(&mut self) {
    for id in self.temp_roots.drain(..) {
      self.heap.remove_root(id);
    }
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

  fn value_undefined(&self) -> Self::Value {
    Value::Undefined
  }

  fn value_null(&self) -> Self::Value {
    Value::Null
  }

  fn value_bool(&self, value: bool) -> Self::Value {
    Value::Bool(value)
  }

  fn value_number(&self, value: f64) -> Self::Value {
    Value::Number(value)
  }

  fn value_string(&self, value: Self::String) -> Self::Value {
    Value::String(value)
  }

  fn value_object(&self, value: Self::Object) -> Self::Value {
    Value::Object(value)
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

  fn is_string_object(&self, _value: Self::Value) -> bool {
    // `vm-js` does not yet model boxed String objects.
    false
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

  fn type_error(&mut self, message: &'static str) -> Self::Error {
    VmError::Unimplemented(message)
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

  fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<Self::String, Self::Error> {
    let s = {
      let mut scope = self.heap.scope();
      scope.alloc_string_from_code_units(units)?
    };
    self.root_temp(Value::String(s));
    Ok(s)
  }

  fn alloc_object(&mut self) -> Result<Self::Object, Self::Error> {
    let obj = {
      let mut scope = self.heap.scope();
      scope.alloc_object()?
    };
    self.root_temp(Value::Object(obj));
    Ok(obj)
  }

  fn alloc_array(&mut self, _len: usize) -> Result<Self::Object, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL array creation requires VM array allocation",
    ))
  }

  fn create_data_property_or_throw(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
    value: Self::Value,
  ) -> Result<(), Self::Error> {
    let key = match key {
      PropertyKey::String(s) => VmPropertyKey::String(s),
      PropertyKey::Symbol(s) => VmPropertyKey::Symbol(s),
    };

    let desc = PropertyDescriptor {
      enumerable: true,
      configurable: true,
      kind: PropertyKind::Data {
        value,
        writable: true,
      },
    };

    let mut scope = self.heap.scope();
    scope.define_property(object, key, desc)
  }

  fn well_known_symbol(&mut self, _sym: WellKnownSymbol) -> Result<Self::Symbol, Self::Error> {
    Err(VmError::Unimplemented(
      "Well-known symbols require Symbol built-ins",
    ))
  }

  fn get_iterator(&mut self, _value: Self::Value) -> Result<Self::Object, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL iterable conversions require iterator protocol (GetIterator, IteratorNext)",
    ))
  }

  fn get_iterator_from_method(
    &mut self,
    _object: Self::Object,
    _method: Self::Value,
  ) -> Result<Self::Object, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL iterable conversions require iterator protocol (GetIteratorFromMethod)",
    ))
  }

  fn iterator_next(
    &mut self,
    _iterator: Self::Object,
  ) -> Result<IteratorResult<Self::Value>, Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL iterable conversions require iterator protocol (IteratorNext)",
    ))
  }

  fn set_integrity_level_frozen(&mut self, _object: Self::Object) -> Result<(), Self::Error> {
    Err(VmError::Unimplemented(
      "WebIDL FrozenArray requires SetIntegrityLevel('frozen')",
    ))
  }
}

#[cfg(test)]
mod tests {
  use super::VmJsWebIdlCx;
  use vm_js::{Heap, HeapLimits, PropertyKey as VmPropertyKey, Value};
  use webidl::{
    conversions, DomString, IdlRecord, InterfaceId, ToJsValue, WebIdlHooks, WebIdlLimits,
  };

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
    let out_units = cx
      .heap
      .get_string(out)
      .expect("get string")
      .as_code_units()
      .to_vec();
    assert_eq!(out_units, units);
  }

  #[test]
  fn record_to_js_defines_own_enumerable_data_properties() {
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let hooks = NoHooks;
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut heap, limits, &hooks);

    let record = IdlRecord(vec![
      (DomString::from_str("a"), 1u32),
      (DomString::from_str("b"), 2u32),
    ]);

    let v = record.to_js(&mut cx, &limits).expect("record to_js");
    let Value::Object(obj) = v else {
      panic!("expected object, got {v:?}");
    };

    // Use fresh key strings for lookup; vm-js compares string keys by UTF-16 code units.
    let key_a = {
      let mut scope = cx.heap.scope();
      scope.alloc_string("a").expect("alloc key a")
    };
    let key_b = {
      let mut scope = cx.heap.scope();
      scope.alloc_string("b").expect("alloc key b")
    };

    let desc_a = cx
      .heap
      .object_get_own_property(obj, &VmPropertyKey::String(key_a))
      .expect("get own property a")
      .expect("property a exists");
    assert!(desc_a.enumerable);
    assert!(desc_a.configurable);
    let vm_js::PropertyKind::Data { value, writable } = desc_a.kind else {
      panic!("expected data descriptor for a");
    };
    assert!(writable);
    assert_eq!(value, Value::Number(1.0));

    let desc_b = cx
      .heap
      .object_get_own_property(obj, &VmPropertyKey::String(key_b))
      .expect("get own property b")
      .expect("property b exists");
    assert!(desc_b.enumerable);
    assert!(desc_b.configurable);
    let vm_js::PropertyKind::Data { value, writable } = desc_b.kind else {
      panic!("expected data descriptor for b");
    };
    assert!(writable);
    assert_eq!(value, Value::Number(2.0));
  }
}
