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

  fn root(&mut self, value: Value) -> Result<(), VmError> {
    self.scope.push_root(value)?;
    Ok(())
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
    if let Some(intrinsics) = self.vm.intrinsics() {
      let syms = intrinsics.well_known_symbols();
      return Ok(match sym {
        WellKnownSymbol::Iterator => syms.iterator,
        WellKnownSymbol::AsyncIterator => syms.async_iterator,
      });
    }

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
    self.root(Value::String(s))?;
    Ok(s)
  }

  fn to_number(&mut self, value: Self::Value) -> Result<f64, Self::Error> {
    self.scope.heap_mut().to_number(value)
  }

  fn type_error(&mut self, message: &'static str) -> Self::Error {
    VmError::TypeError(message)
  }

  fn get(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Self::Value, Self::Error> {
    self.root(Value::Object(object))?;
    match key {
      PropertyKey::String(s) => self.root(Value::String(s))?,
      PropertyKey::Symbol(s) => self.root(Value::Symbol(s))?,
    };

    let key = Self::to_vm_property_key(key);
    let value = self.vm.get(&mut self.scope, object, key)?;
    self.root(value)?;
    Ok(value)
  }

  fn get_method(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<Self::Value>, Self::Error> {
    self.root(Value::Object(object))?;
    match key {
      PropertyKey::String(s) => self.root(Value::String(s))?,
      PropertyKey::Symbol(s) => self.root(Value::Symbol(s))?,
    };

    let key = Self::to_vm_property_key(key);
    let method = self.vm.get_method(&mut self.scope, object, key)?;
    if let Some(v) = method {
      self.root(v)?;
    }
    Ok(method)
  }

  fn own_property_keys(
    &mut self,
    object: Self::Object,
  ) -> Result<Vec<PropertyKey<Self::String, Self::Symbol>>, Self::Error> {
    self.root(Value::Object(object))?;
    let keys = self.scope.heap().ordinary_own_property_keys(object)?;
    Ok(keys.into_iter().map(Self::from_vm_property_key).collect())
  }

  fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<Self::String, Self::Error> {
    let s = self.scope.alloc_string_from_code_units(units)?;
    self.root(Value::String(s))?;
    Ok(s)
  }

  fn alloc_object(&mut self) -> Result<Self::Object, Self::Error> {
    let obj = self.scope.alloc_object()?;
    self.root(Value::Object(obj))?;
    Ok(obj)
  }

  fn alloc_array(&mut self, len: usize) -> Result<Self::Object, Self::Error> {
    let obj = self.scope.alloc_array(len)?;
    self.root(Value::Object(obj))?;

    // When a realm is initialized, prefer `%Array.prototype%` so the result behaves like a normal
    // JavaScript array (e.g. is iterable, has standard methods).
    if let Some(intrinsics) = self.vm.intrinsics() {
      let proto = intrinsics.array_prototype();
      self.root(Value::Object(proto))?;
      self.scope.object_set_prototype(obj, Some(proto))?;
    }

    Ok(obj)
  }

  fn create_data_property_or_throw(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
    value: Self::Value,
  ) -> Result<(), Self::Error> {
    self.root(Value::Object(object))?;
    match key {
      PropertyKey::String(s) => self.root(Value::String(s))?,
      PropertyKey::Symbol(s) => self.root(Value::Symbol(s))?,
    };
    self.root(value)?;

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
    self.root(Value::Object(object))?;
    self.root(method)?;

    let iterator = self
      .vm
      .call(&mut self.scope, method, Value::Object(object), &[])?;
    let Value::Object(iterator) = iterator else {
      return Err(self.type_error("Iterator method did not return an object"));
    };
    self.root(Value::Object(iterator))?;
    Ok(iterator)
  }

  fn iterator_next(
    &mut self,
    iterator: Self::Object,
  ) -> Result<IteratorResult<Self::Value>, Self::Error> {
    self.root(Value::Object(iterator))?;

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
    self.root(Value::Object(result_obj))?;

    let done_key = PropertyKey::String(self.scope.alloc_string("done")?);
    let done_value = self.get(result_obj, done_key)?;
    let done = self.to_boolean(done_value)?;

    let value_key = PropertyKey::String(self.scope.alloc_string("value")?);
    let value = self.get(result_obj, value_key)?;
    self.root(value)?;

    Ok(IteratorResult { value, done })
  }
}

#[cfg(test)]
mod tests {
  use super::VmJsWebIdlCx;
  use vm_js::{
    GcObject, Heap, HeapLimits, NativeFunctionId, PropertyDescriptor, PropertyKey as VmPropertyKey,
    PropertyKind, Realm, Scope, Value, Vm, VmError, VmHostHooks, VmOptions,
  };
  use webidl::{
    conversions, index_to_property_key, record_to_js_object, sequence_to_js_array, DomString,
    IdlRecord, InterfaceId, JsRuntime, PropertyKey as WebIdlPropertyKey, ToJsValue, WebIdlHooks,
    WebIdlLimits,
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

  fn prop_key_str(
    cx: &mut VmJsWebIdlCx<'_>,
    s: &str,
  ) -> Result<WebIdlPropertyKey<vm_js::GcString, vm_js::GcSymbol>, VmError> {
    let units: Vec<u16> = s.encode_utf16().collect();
    let handle = cx.alloc_string_from_code_units(&units)?;
    Ok(WebIdlPropertyKey::String(handle))
  }

  #[test]
  fn domstring_smoke_roundtrips_code_units() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

    let units: Vec<u16> = vec![0x0041, 0xD83D, 0xDE00, 0x0000, 0xFFFF];
    let s = {
      let mut scope = heap.scope();
      scope
        .alloc_string_from_code_units(&units)
        .expect("alloc string")
    };
    let _root = heap.add_root(Value::String(s)).expect("add_root");

    let hooks = NoHooks;
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    let out = conversions::dom_string(&mut cx, Value::String(s)).expect("DOMString conversion");
    drop(cx);

    let out_units = heap.get_string(out).expect("get string").as_code_units();
    assert_eq!(out_units, units.as_slice());
    Ok(())
  }

  #[test]
  fn to_number_string_parsing_matches_ecma262_roughly() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let hooks = NoHooks;
    let limits = WebIdlLimits::default();

    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    assert!(cx.to_number(Value::Undefined)?.is_nan());
    assert_eq!(cx.to_number(Value::Null)?, 0.0);
    assert_eq!(cx.to_number(Value::Bool(true))?, 1.0);
    assert_eq!(cx.to_number(Value::Bool(false))?, 0.0);

    let s = cx.scope.alloc_string("  123  ")?;
    assert_eq!(cx.to_number(Value::String(s))?, 123.0);

    let s = cx.scope.alloc_string("")?;
    assert_eq!(cx.to_number(Value::String(s))?, 0.0);

    let s = cx.scope.alloc_string("Infinity")?;
    assert!(cx.to_number(Value::String(s))?.is_infinite());

    let s = cx.scope.alloc_string("0x10")?;
    assert_eq!(cx.to_number(Value::String(s))?, 16.0);

    let s = cx.scope.alloc_string("0b10")?;
    assert_eq!(cx.to_number(Value::String(s))?, 2.0);

    let s = cx.scope.alloc_string("0o10")?;
    assert_eq!(cx.to_number(Value::String(s))?, 8.0);

    let s = cx.scope.alloc_string("010")?;
    assert_eq!(cx.to_number(Value::String(s))?, 10.0);

    let s = cx.scope.alloc_string("-0x10")?;
    assert!(cx.to_number(Value::String(s))?.is_nan());

    Ok(())
  }

  #[test]
  fn well_known_symbol_uses_realm_intrinsics_when_available() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(8 * 1024 * 1024, 8 * 1024 * 1024));
    let mut realm = Realm::new(&mut vm, &mut heap)?;

    let hooks = NoHooks;
    let limits = WebIdlLimits::default();

    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);
    let iter_sym = cx.well_known_symbol(webidl::WellKnownSymbol::Iterator)?;
    assert_eq!(iter_sym, realm.well_known_symbols().iterator);

    // `alloc_array` should use `%Array.prototype%` when intrinsics are installed.
    let arr = cx.alloc_array(0)?;
    assert_eq!(
      cx.scope.heap().object_prototype(arr)?,
      Some(realm.intrinsics().array_prototype())
    );

    drop(cx);
    realm.teardown(&mut heap);
    Ok(())
  }

  #[test]
  fn record_to_js_defines_own_enumerable_data_properties() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let hooks = NoHooks;
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    let record = IdlRecord(vec![
      (DomString::from_str("a"), 1u32),
      (DomString::from_str("b"), 2u32),
    ]);

    let v = record.to_js(&mut cx, &limits).expect("record to_js");
    let Value::Object(obj) = v else {
      return Err(VmError::TypeError("expected object from record.to_js"));
    };

    // Use fresh key strings for lookup; vm-js compares string keys by UTF-16 code units.
    let key_a = cx.scope.alloc_string("a")?;
    let key_b = cx.scope.alloc_string("b")?;

    let desc_a = cx
      .scope
      .heap()
      .object_get_own_property(obj, &VmPropertyKey::from_string(key_a))?
      .expect("property a exists");
    assert!(desc_a.enumerable);
    assert!(desc_a.configurable);
    let PropertyKind::Data { value, writable } = desc_a.kind else {
      return Err(VmError::TypeError("expected data descriptor for a"));
    };
    assert!(writable);
    assert_eq!(value, Value::Number(1.0));

    let desc_b = cx
      .scope
      .heap()
      .object_get_own_property(obj, &VmPropertyKey::from_string(key_b))?
      .expect("property b exists");
    assert!(desc_b.enumerable);
    assert!(desc_b.configurable);
    let PropertyKind::Data { value, writable } = desc_b.kind else {
      return Err(VmError::TypeError("expected data descriptor for b"));
    };
    assert!(writable);
    assert_eq!(value, Value::Number(2.0));

    Ok(())
  }

  #[test]
  fn sequence_to_js_array_sets_length_indices_and_own_property_keys() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    // Stress rooting: force a GC before each allocation.
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
    let hooks = NoHooks;
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    let array =
      sequence_to_js_array(&mut cx, &limits, &[1u32, 2u32]).expect("sequence_to_js_array");

    // length === 2
    let length_key = prop_key_str(&mut cx, "length")?;
    let length = cx.get(array, length_key)?;
    assert_eq!(length, Value::Number(2.0));

    // array[0] === 1, array[1] === 2
    for (i, expected) in [1.0, 2.0].into_iter().enumerate() {
      let key = index_to_property_key(&mut cx, i).expect("index key");
      let v = cx.get(array, key)?;
      assert_eq!(v, Value::Number(expected));
    }

    let keys = cx.own_property_keys(array)?;
    let keys = keys
      .into_iter()
      .map(|k| match k {
        WebIdlPropertyKey::String(s) => cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(),
        WebIdlPropertyKey::Symbol(sym) => {
          format!("sym:{}", cx.scope.heap().get_symbol_id(sym).unwrap())
        }
      })
      .collect::<Vec<_>>();
    assert_eq!(keys, vec!["0".to_string(), "1".to_string(), "length".to_string()]);
    Ok(())
  }

  #[test]
  fn record_to_js_object_sets_properties_and_own_property_keys() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    // Stress rooting: force a GC before each allocation.
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 0));
    let hooks = NoHooks;
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    let entries = [("b", 2u32), ("a", 1u32)];
    let obj = record_to_js_object(&mut cx, &limits, &entries).expect("record_to_js_object");

    for (k, v_expected) in entries.iter() {
      let key = prop_key_str(&mut cx, k)?;
      let v = cx.get(obj, key)?;
      assert_eq!(v, Value::Number(*v_expected as f64));
    }

    let keys = cx.own_property_keys(obj)?;
    let keys = keys
      .into_iter()
      .map(|k| match k {
        WebIdlPropertyKey::String(s) => cx.scope.heap().get_string(s).unwrap().to_utf8_lossy(),
        WebIdlPropertyKey::Symbol(sym) => {
          format!("sym:{}", cx.scope.heap().get_symbol_id(sym).unwrap())
        }
      })
      .collect::<Vec<_>>();
    assert_eq!(keys, vec!["b".to_string(), "a".to_string()]);
    Ok(())
  }

  fn get_method_getter(this: Value, scope: &mut Scope<'_>) -> Result<Value, VmError> {
    let Value::Object(obj) = this else {
      return Err(VmError::TypeError("getter this is not object"));
    };

    // calls++
    let calls_key = VmPropertyKey::from_string(scope.alloc_string("calls")?);
    let calls = scope
      .heap()
      .object_get_own_data_property_value(obj, &calls_key)?
      .unwrap_or(Value::Number(0.0));
    let calls_n = match calls {
      Value::Number(n) => n,
      _ => 0.0,
    };
    scope.heap_mut().object_set_existing_data_property_value(
      obj,
      &calls_key,
      Value::Number(calls_n + 1.0),
    )?;

    // return this.fn
    let fn_key = VmPropertyKey::from_string(scope.alloc_string("fn")?);
    Ok(
      scope
        .heap()
        .object_get_own_data_property_value(obj, &fn_key)?
        .unwrap_or(Value::Undefined),
    )
  }

  fn getter_call_handler(
    _vm: &mut Vm,
    scope: &mut Scope<'_>,
    _host: &mut dyn VmHostHooks,
    _callee: GcObject,
    this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    get_method_getter(this, scope)
  }

  fn noop_call_handler(
    _vm: &mut Vm,
    _scope: &mut Scope<'_>,
    _host: &mut dyn VmHostHooks,
    _callee: GcObject,
    _this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    Ok(Value::Undefined)
  }

  #[test]
  fn get_method_invokes_accessor_getter() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));

    // Create a method function and a getter function.
    let method;
      let getter;
    {
      let noop_id: NativeFunctionId = vm.register_native_call(noop_call_handler)?;
      let getter_id: NativeFunctionId = vm.register_native_call(getter_call_handler)?;

      let mut scope = heap.scope();
      let method_name = scope.alloc_string("method")?;
      let getter_name = scope.alloc_string("getter")?;
      method = scope.alloc_native_function(noop_id, None, method_name, 0)?;
      getter = scope.alloc_native_function(getter_id, None, getter_name, 0)?;
    }

    let obj;
    {
      let mut scope = heap.scope();
      obj = scope.alloc_object()?;

      // calls = 0
      let calls_key = VmPropertyKey::from_string(scope.alloc_string("calls")?);
      scope.define_property(
        obj,
        calls_key,
        PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Data {
            value: Value::Number(0.0),
            writable: true,
          },
        },
      )?;

      // fn = method
      let fn_key = VmPropertyKey::from_string(scope.alloc_string("fn")?);
      scope.define_property(
        obj,
        fn_key,
        PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Data {
            value: Value::Object(method),
            writable: true,
          },
        },
      )?;

      // get m() { ... }
      let m_key = VmPropertyKey::from_string(scope.alloc_string("m")?);
      scope.define_property(
        obj,
        m_key,
        PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Accessor {
            get: Value::Object(getter),
            set: Value::Undefined,
          },
        },
      )?;
    }

    let hooks = NoHooks;
    let limits = WebIdlLimits::default();
    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);
    cx.scope.push_root(Value::Object(obj))?;

    let key = WebIdlPropertyKey::String(cx.scope.alloc_string("m")?);
    let got = cx.get_method(obj, key)?;
    assert_eq!(got, Some(Value::Object(method)));

    // Ensure getter ran exactly once.
    let calls_key = VmPropertyKey::from_string(cx.scope.alloc_string("calls")?);
    let calls = cx
      .scope
      .heap()
      .object_get_own_data_property_value(obj, &calls_key)?
      .unwrap_or(Value::Undefined);
    assert_eq!(calls, Value::Number(1.0));
    Ok(())
  }

  fn iterator_method_call(
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    _callee: GcObject,
    this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    let Value::Object(iterable) = this else {
      return Err(VmError::TypeError("iterator method this is not object"));
    };

    // Read iterable.items.
    let items_key = VmPropertyKey::from_string(scope.alloc_string("items")?);
    let items = scope
      .heap()
      .object_get_own_data_property_value(iterable, &items_key)?
      .unwrap_or(Value::Undefined);

    // Create iterator object: { items, index: 0, next: <native fn> }.
    let iter_obj = scope.alloc_object()?;
    scope.push_root(Value::Object(iter_obj))?;

    // items
    scope.define_property(
      iter_obj,
      items_key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: items,
          writable: true,
        },
      },
    )?;

    // index
    let index_key = VmPropertyKey::from_string(scope.alloc_string("index")?);
    scope.define_property(
      iter_obj,
      index_key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Number(0.0),
          writable: true,
        },
      },
    )?;

    // next
    let next_key = VmPropertyKey::from_string(scope.alloc_string("next")?);
    let next_name = scope.alloc_string("next")?;
    let next_id = vm.register_native_call(iterator_next_call)?;
    let next_fn = scope.alloc_native_function(next_id, None, next_name, 0)?;
    scope.define_property(
      iter_obj,
      next_key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Object(next_fn),
          writable: true,
        },
      },
    )?;

    Ok(Value::Object(iter_obj))
  }

  fn iterator_method_call_handler(
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    _host: &mut dyn VmHostHooks,
    callee: GcObject,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    iterator_method_call(vm, scope, callee, this, args)
  }

  fn iterator_next_call(
    _vm: &mut Vm,
    scope: &mut Scope<'_>,
    _host: &mut dyn VmHostHooks,
    _callee: GcObject,
    this: Value,
    _args: &[Value],
  ) -> Result<Value, VmError> {
    let Value::Object(iter_obj) = this else {
      return Err(VmError::TypeError("iterator this is not object"));
    };

    let items_key = VmPropertyKey::from_string(scope.alloc_string("items")?);
    let index_key = VmPropertyKey::from_string(scope.alloc_string("index")?);

    let items = scope
      .heap()
      .object_get_own_data_property_value(iter_obj, &items_key)?
      .unwrap_or(Value::Undefined);
    let Value::Object(items_obj) = items else {
      return Err(VmError::TypeError("iterator items is not object"));
    };

    let index = scope
      .heap()
      .object_get_own_data_property_value(iter_obj, &index_key)?
      .unwrap_or(Value::Number(0.0));
    let idx = match index {
      Value::Number(n) => n as usize,
      _ => 0,
    };

    // Read items.length.
    let length_key = VmPropertyKey::from_string(scope.alloc_string("length")?);
    let len = scope
      .heap()
      .object_get_own_data_property_value(items_obj, &length_key)?
      .unwrap_or(Value::Number(0.0));
    let len = match len {
      Value::Number(n) => n as usize,
      _ => 0,
    };

    let done = idx >= len;
    let value = if done {
      Value::Undefined
    } else {
      let idx_key = VmPropertyKey::from_string(scope.alloc_string(&idx.to_string())?);
      scope
        .heap()
        .object_get_own_data_property_value(items_obj, &idx_key)?
        .unwrap_or(Value::Undefined)
    };

    // index++
    scope.heap_mut().object_set_existing_data_property_value(
      iter_obj,
      &index_key,
      Value::Number((idx + 1) as f64),
    )?;

    // Return result object { value, done }.
    let result_obj = scope.alloc_object()?;
    scope.push_root(Value::Object(result_obj))?;

    let value_key = VmPropertyKey::from_string(scope.alloc_string("value")?);
    let done_key = VmPropertyKey::from_string(scope.alloc_string("done")?);

    scope.define_property(
      result_obj,
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
    scope.define_property(
      result_obj,
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

    Ok(Value::Object(result_obj))
  }

  #[test]
  fn iterator_protocol_smoke() -> Result<(), VmError> {
    let mut vm = Vm::new(VmOptions::default());
    let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
    let hooks = NoHooks;
    let limits = WebIdlLimits::default();

    let mut cx = VmJsWebIdlCx::new(&mut vm, &mut heap, limits, &hooks);

    // Build an array-like object `items` via WebIDL's IDL->JS helper (exercises alloc_array +
    // CreateDataPropertyOrThrow).
    let items =
      sequence_to_js_array(&mut cx, &limits, &["a", "b", "c"]).expect("sequence_to_js_array");

    // iterable = { items, [Symbol.iterator]: iterator_method }
    let iterable;
    {
      iterable = cx.scope.alloc_object()?;
      cx.scope.push_root(Value::Object(iterable))?;

      let items_key = VmPropertyKey::from_string(cx.scope.alloc_string("items")?);
      cx.scope.define_property(
        iterable,
        items_key,
        PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Data {
            value: Value::Object(items),
            writable: true,
          },
        },
      )?;

      let iter_name = cx.scope.alloc_string("iterator")?;
      let iter_id = cx.vm.register_native_call(iterator_method_call_handler)?;
      let iter_fn = cx.scope.alloc_native_function(iter_id, None, iter_name, 0)?;

      let sym = cx.well_known_symbol(webidl::WellKnownSymbol::Iterator)?;
      let key = VmPropertyKey::from_symbol(sym);
      cx.scope.define_property(
        iterable,
        key,
        PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Data {
            value: Value::Object(iter_fn),
            writable: true,
          },
        },
      )?;
    }

    let iterator = cx.get_iterator(Value::Object(iterable))?;
    let mut out = Vec::<String>::new();
    loop {
      let step = cx.iterator_next(iterator)?;
      if step.done {
        break;
      }
      let Value::String(s) = step.value else {
        return Err(VmError::TypeError("expected string iterator value"));
      };
      out.push(cx.scope.heap().get_string(s)?.to_utf8_lossy());
    }

    assert_eq!(out, vec!["a", "b", "c"]);
    Ok(())
  }
}
