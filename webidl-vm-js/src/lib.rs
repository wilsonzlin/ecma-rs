//! `vm-js` adapter for the `webidl` conversion/runtime traits.
//!
//! WebIDL conversions are host-driven Rust code that may keep VM handles (strings/objects/symbols)
//! in local variables across allocations. `vm-js` GC handles are *not* automatically rooted, so this
//! adapter conservatively roots values it produces/consumes for the lifetime of the conversion
//! context using a long-lived [`Scope`].

use vm_js::{
  GcObject, GcString, GcSymbol, Heap, PropertyKey as VmPropertyKey, Scope, Value, Vm, VmError,
};
use webidl::{
  InterfaceId, IteratorResult, JsRuntime, PropertyKey, WebIdlHooks, WebIdlLimits, WellKnownSymbol,
};

/// `webidl` conversion context backed by `vm-js`.
pub struct VmJsWebIdlCx<'a> {
  pub vm: &'a mut Vm,
  pub scope: Scope<'a>,
  pub limits: WebIdlLimits,
  pub hooks: &'a dyn WebIdlHooks<Value>,
  well_known_iterator: Option<GcSymbol>,
  well_known_async_iterator: Option<GcSymbol>,
}

impl<'a> VmJsWebIdlCx<'a> {
  pub fn new(
    vm: &'a mut Vm,
    heap: &'a mut Heap,
    limits: WebIdlLimits,
    hooks: &'a dyn WebIdlHooks<Value>,
  ) -> Self {
    Self {
      vm,
      scope: heap.scope(),
      limits,
      hooks,
      well_known_iterator: None,
      well_known_async_iterator: None,
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

  fn root(&mut self, value: Value) {
    self.scope.push_root(value);
  }

  fn to_vm_property_key(key: PropertyKey<GcString, GcSymbol>) -> VmPropertyKey {
    match key {
      PropertyKey::String(s) => VmPropertyKey::from_string(s),
      PropertyKey::Symbol(s) => VmPropertyKey::from_symbol(s),
    }
  }

  fn from_vm_property_key(key: VmPropertyKey) -> PropertyKey<GcString, GcSymbol> {
    match key {
      VmPropertyKey::String(s) => PropertyKey::String(s),
      VmPropertyKey::Symbol(s) => PropertyKey::Symbol(s),
    }
  }

  fn get_well_known_symbol_cached(&mut self, sym: WellKnownSymbol) -> Result<GcSymbol, VmError> {
    match sym {
      WellKnownSymbol::Iterator => {
        if let Some(sym) = self.well_known_iterator {
          return Ok(sym);
        }
        let key = self.scope.alloc_string("Symbol.iterator")?;
        let sym = self.scope.heap_mut().symbol_for(key)?;
        self.well_known_iterator = Some(sym);
        Ok(sym)
      }
      WellKnownSymbol::AsyncIterator => {
        if let Some(sym) = self.well_known_async_iterator {
          return Ok(sym);
        }
        let key = self.scope.alloc_string("Symbol.asyncIterator")?;
        let sym = self.scope.heap_mut().symbol_for(key)?;
        self.well_known_async_iterator = Some(sym);
        Ok(sym)
      }
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
    self.scope.heap().to_boolean(value)
  }

  fn to_string(&mut self, value: Self::Value) -> Result<Self::String, Self::Error> {
    let s = self.scope.heap_mut().to_string(value)?;
    self.root(Value::String(s));
    Ok(s)
  }

  fn to_number(&mut self, value: Self::Value) -> Result<f64, Self::Error> {
    self.scope.heap_mut().to_number(value)
  }

  fn type_error(&mut self, message: &'static str) -> Self::Error {
    // `vm-js` does not yet model Error objects.
    VmError::Unimplemented(message)
  }

  fn get(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Self::Value, Self::Error> {
    self.root(Value::Object(object));
    match key {
      PropertyKey::String(s) => self.root(Value::String(s)),
      PropertyKey::Symbol(s) => self.root(Value::Symbol(s)),
    };

    let key = Self::to_vm_property_key(key);
    let value = self.vm.get(&mut self.scope, object, key)?;
    self.root(value);
    Ok(value)
  }

  fn get_method(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<Self::Value>, Self::Error> {
    self.root(Value::Object(object));
    match key {
      PropertyKey::String(s) => self.root(Value::String(s)),
      PropertyKey::Symbol(s) => self.root(Value::Symbol(s)),
    };

    let key = Self::to_vm_property_key(key);
    let method = self.vm.get_method(&mut self.scope, object, key)?;
    if let Some(v) = method {
      self.root(v);
    }
    Ok(method)
  }

  fn own_property_keys(
    &mut self,
    object: Self::Object,
  ) -> Result<Vec<PropertyKey<Self::String, Self::Symbol>>, Self::Error> {
    self.root(Value::Object(object));
    let keys = self.scope.heap().ordinary_own_property_keys(object)?;
    Ok(keys.into_iter().map(Self::from_vm_property_key).collect())
  }

  fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<Self::String, Self::Error> {
    let s = self.scope.alloc_string_from_code_units(units)?;
    self.root(Value::String(s));
    Ok(s)
  }

  fn alloc_object(&mut self) -> Result<Self::Object, Self::Error> {
    let obj = self.scope.alloc_object()?;
    self.root(Value::Object(obj));
    Ok(obj)
  }

  fn alloc_array(&mut self, len: usize) -> Result<Self::Object, Self::Error> {
    let obj = self.scope.alloc_array(len)?;
    self.root(Value::Object(obj));
    Ok(obj)
  }

  fn create_data_property_or_throw(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
    value: Self::Value,
  ) -> Result<(), Self::Error> {
    self.root(Value::Object(object));
    match key {
      PropertyKey::String(s) => self.root(Value::String(s)),
      PropertyKey::Symbol(s) => self.root(Value::Symbol(s)),
    };
    self.root(value);

    let key = Self::to_vm_property_key(key);
    self.scope.create_data_property_or_throw(object, key, value)?;
    Ok(())
  }

  fn well_known_symbol(&mut self, sym: WellKnownSymbol) -> Result<Self::Symbol, Self::Error> {
    self.get_well_known_symbol_cached(sym)
  }

  fn get_iterator(&mut self, value: Self::Value) -> Result<Self::Object, Self::Error> {
    let Value::Object(obj) = value else {
      return Err(self.type_error("GetIterator(value): value is not an object"));
    };

    let sym = self.well_known_symbol(WellKnownSymbol::Iterator)?;
    let Some(method) = self.get_method(obj, PropertyKey::Symbol(sym))? else {
      return Err(self.type_error("GetIterator(value): @@iterator is undefined/null"));
    };
    self.get_iterator_from_method(obj, method)
  }

  fn get_iterator_from_method(
    &mut self,
    object: Self::Object,
    method: Self::Value,
  ) -> Result<Self::Object, Self::Error> {
    self.root(Value::Object(object));
    self.root(method);

    let iterator = self
      .vm
      .call(&mut self.scope, method, Value::Object(object), &[])?;
    let Value::Object(iterator) = iterator else {
      return Err(self.type_error("Iterator method did not return an object"));
    };
    self.root(Value::Object(iterator));
    Ok(iterator)
  }

  fn iterator_next(
    &mut self,
    iterator: Self::Object,
  ) -> Result<IteratorResult<Self::Value>, Self::Error> {
    self.root(Value::Object(iterator));

    let next_key = PropertyKey::String(self.scope.alloc_string("next")?);
    let Some(next_method) = self.get_method(iterator, next_key)? else {
      return Err(self.type_error("IteratorNext(iterator): next is undefined/null"));
    };

    let result = self
      .vm
      .call(&mut self.scope, next_method, Value::Object(iterator), &[])?;
    let Value::Object(result_obj) = result else {
      return Err(self.type_error("IteratorNext(iterator): next() did not return an object"));
    };
    self.root(Value::Object(result_obj));

    let done_key = PropertyKey::String(self.scope.alloc_string("done")?);
    let done_value = self.get(result_obj, done_key)?;
    let done = self.to_boolean(done_value)?;

    let value_key = PropertyKey::String(self.scope.alloc_string("value")?);
    let value = self.get(result_obj, value_key)?;
    self.root(value);

    Ok(IteratorResult { value, done })
  }
}

#[cfg(test)]
mod tests {
  use super::VmJsWebIdlCx;
  use vm_js::{Heap, HeapLimits, Value, Vm, VmOptions};
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
    let mut vm = Vm::new(VmOptions::default());
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
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    let out = conversions::dom_string(&mut cx, Value::String(s)).expect("DOMString conversion");
    drop(cx);

    let out_units = heap.get_string(out).expect("get string").as_code_units();
    assert_eq!(out_units, units.as_slice());
  }
}
