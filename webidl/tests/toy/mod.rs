#![allow(dead_code)]

use std::fmt;

use webidl::{
  InterfaceId, IteratorResult, JsOwnPropertyDescriptor, JsPropertyKind, JsRuntime, PropertyKey,
  WebIdlHooks, WebIdlJsRuntime, WebIdlLimits, WellKnownSymbol,
};

#[derive(Debug)]
pub enum ToyError {
  Unimplemented(&'static str),
  TypeError(String),
  RangeError(String),
}

impl fmt::Display for ToyError {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    match self {
      ToyError::Unimplemented(msg) => write!(f, "unimplemented: {msg}"),
      ToyError::TypeError(msg) => write!(f, "TypeError: {msg}"),
      ToyError::RangeError(msg) => write!(f, "RangeError: {msg}"),
    }
  }
}

impl std::error::Error for ToyError {}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ToyString(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ToyObject(pub usize);

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ToySymbol(pub usize);

#[allow(dead_code)]
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum ToyValue {
  Undefined,
  Null,
  Bool(bool),
  Number(f64),
  String(ToyString),
  Object(ToyObject),
  Symbol(ToySymbol),
}

#[derive(Debug, Clone, PartialEq)]
pub enum ToyObjectKind {
  Ordinary,
  Array { len: usize },
  StringObject { string: ToyString },
  Iterator {
    values: Vec<ToyValue>,
    index: usize,
  },
  IteratorMethod { values: Vec<ToyValue> },
  AsyncIteratorMethod { values: Vec<ToyValue> },
}

impl Default for ToyObjectKind {
  fn default() -> Self {
    Self::Ordinary
  }
}

#[derive(Debug, Default)]
pub struct ToyObjectData {
  pub kind: ToyObjectKind,
  pub props: Vec<(PropertyKey<ToyString, ToySymbol>, ToyValue)>,
  pub frozen: bool,
}

pub struct ToyRuntime {
  pub limits: WebIdlLimits,
  pub strings: Vec<Vec<u16>>,
  pub objects: Vec<ToyObjectData>,
  pub get_method_calls: usize,
}

impl Default for ToyRuntime {
  fn default() -> Self {
    Self {
      limits: WebIdlLimits::default(),
      strings: Vec::new(),
      objects: Vec::new(),
      get_method_calls: 0,
    }
  }
}

impl ToyRuntime {
  fn alloc_string(&mut self, s: &str) -> ToyString {
    let idx = self.strings.len();
    self.strings.push(s.encode_utf16().collect());
    ToyString(idx)
  }

  fn alloc_object_with_kind(&mut self, kind: ToyObjectKind) -> ToyObject {
    let idx = self.objects.len();
    self.objects.push(ToyObjectData {
      kind,
      ..ToyObjectData::default()
    });
    ToyObject(idx)
  }

  /// Allocates a JS string primitive value.
  pub fn string(&mut self, s: &str) -> ToyValue {
    ToyValue::String(self.alloc_string(s))
  }

  /// Allocates a boxed string object (i.e. has `[[StringData]]`).
  pub fn string_object(&mut self, s: &str) -> ToyValue {
    let str_handle = self.alloc_string(s);
    let obj = self.alloc_object_with_kind(ToyObjectKind::StringObject { string: str_handle });
    ToyValue::Object(obj)
  }

  pub fn make_iterable(&mut self, elements: Vec<ToyValue>, async_: bool) -> ToyValue {
    let obj = ToyValue::Object(self.alloc_object_with_kind(ToyObjectKind::Ordinary));
    self.add_iterable_methods(obj, elements, async_);
    obj
  }

  pub fn add_iterable_methods(&mut self, obj: ToyValue, elements: Vec<ToyValue>, async_: bool) {
    let ToyValue::Object(obj) = obj else {
      panic!("add_iterable_methods expected object");
    };

    let sync_method_obj = self.alloc_object_with_kind(ToyObjectKind::IteratorMethod {
      values: elements.clone(),
    });

    let iterator_sym = ToySymbol(0);
    self
      .objects[obj.0]
      .props
      .push((PropertyKey::Symbol(iterator_sym), ToyValue::Object(sync_method_obj)));

    if async_ {
      let async_method_obj = self.alloc_object_with_kind(ToyObjectKind::AsyncIteratorMethod {
        values: elements,
      });
      let async_iter_sym = ToySymbol(1);
      self.objects[obj.0].props.push((
        PropertyKey::Symbol(async_iter_sym),
        ToyValue::Object(async_method_obj),
      ));
    }
  }

  pub fn is_frozen(&self, v: ToyValue) -> bool {
    let ToyValue::Object(o) = v else {
      return false;
    };
    self.objects[o.0].frozen
  }

  pub fn array_elements(&self, v: ToyValue) -> Option<Vec<ToyValue>> {
    let ToyValue::Object(o) = v else {
      return None;
    };
    let ToyObjectData {
      kind: ToyObjectKind::Array { len },
      props,
      ..
    } = &self.objects[o.0]
    else {
      return None;
    };

    fn parse_index(units: &[u16]) -> Option<usize> {
      let mut n: usize = 0;
      if units.is_empty() {
        return None;
      }
      for &u in units {
        if !(b'0' as u16..=b'9' as u16).contains(&u) {
          return None;
        }
        n = n.checked_mul(10)?;
        n = n.checked_add((u - (b'0' as u16)) as usize)?;
      }
      Some(n)
    }

    let mut out = vec![ToyValue::Undefined; *len];
    for (k, v) in props.iter() {
      let PropertyKey::String(s) = k else {
        continue;
      };
      let Some(idx) = parse_index(self.string_code_units(*s)) else {
        continue;
      };
      if idx < out.len() {
        out[idx] = *v;
      }
    }
    Some(out)
  }

  pub fn string_code_units(&self, s: ToyString) -> &[u16] {
    &self.strings[s.0]
  }

  pub fn string_contents(&self, s: ToyString) -> String {
    String::from_utf16_lossy(self.string_code_units(s))
  }

  pub fn object(&self, o: ToyObject) -> &ToyObjectData {
    &self.objects[o.0]
  }
}

struct NoHooks;

impl WebIdlHooks<ToyValue> for NoHooks {
  fn is_platform_object(&self, _value: ToyValue) -> bool {
    false
  }

  fn implements_interface(&self, _value: ToyValue, _interface: InterfaceId) -> bool {
    false
  }
}

static NO_HOOKS: NoHooks = NoHooks;

impl JsRuntime for ToyRuntime {
  type Value = ToyValue;
  type String = ToyString;
  type Object = ToyObject;
  type Symbol = ToySymbol;
  type Error = ToyError;

  fn limits(&self) -> WebIdlLimits {
    self.limits
  }

  fn hooks(&self) -> &dyn WebIdlHooks<Self::Value> {
    &NO_HOOKS
  }

  fn value_undefined(&self) -> Self::Value {
    ToyValue::Undefined
  }

  fn value_null(&self) -> Self::Value {
    ToyValue::Null
  }

  fn value_bool(&self, value: bool) -> Self::Value {
    ToyValue::Bool(value)
  }

  fn value_number(&self, value: f64) -> Self::Value {
    ToyValue::Number(value)
  }

  fn value_string(&self, value: Self::String) -> Self::Value {
    ToyValue::String(value)
  }

  fn value_object(&self, value: Self::Object) -> Self::Value {
    ToyValue::Object(value)
  }

  fn is_undefined(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::Undefined)
  }

  fn is_null(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::Null)
  }

  fn is_boolean(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::Bool(_))
  }

  fn is_number(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::Number(_))
  }

  fn is_string(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::String(_))
  }

  fn is_symbol(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::Symbol(_))
  }

  fn is_object(&self, value: Self::Value) -> bool {
    matches!(value, ToyValue::Object(_))
  }

  fn is_string_object(&self, value: Self::Value) -> bool {
    let ToyValue::Object(o) = value else {
      return false;
    };
    matches!(&self.objects[o.0].kind, ToyObjectKind::StringObject { .. })
  }

  fn as_string(&self, value: Self::Value) -> Option<Self::String> {
    match value {
      ToyValue::String(s) => Some(s),
      _ => None,
    }
  }

  fn as_object(&self, value: Self::Value) -> Option<Self::Object> {
    match value {
      ToyValue::Object(o) => Some(o),
      _ => None,
    }
  }

  fn as_symbol(&self, value: Self::Value) -> Option<Self::Symbol> {
    match value {
      ToyValue::Symbol(s) => Some(s),
      _ => None,
    }
  }

  fn to_boolean(&mut self, value: Self::Value) -> Result<bool, Self::Error> {
    Ok(match value {
      ToyValue::Undefined | ToyValue::Null => false,
      ToyValue::Bool(b) => b,
      ToyValue::Number(n) => !(n == 0.0 || n.is_nan()),
      ToyValue::String(s) => !self.string_code_units(s).is_empty(),
      ToyValue::Symbol(_) | ToyValue::Object(_) => true,
    })
  }

  fn to_string(&mut self, value: Self::Value) -> Result<Self::String, Self::Error> {
    match value {
      ToyValue::String(s) => Ok(s),
      ToyValue::Undefined => {
        self.alloc_string_from_code_units(&"undefined".encode_utf16().collect::<Vec<_>>())
      }
      ToyValue::Null => {
        self.alloc_string_from_code_units(&"null".encode_utf16().collect::<Vec<_>>())
      }
      ToyValue::Bool(true) => {
        self.alloc_string_from_code_units(&"true".encode_utf16().collect::<Vec<_>>())
      }
      ToyValue::Bool(false) => {
        self.alloc_string_from_code_units(&"false".encode_utf16().collect::<Vec<_>>())
      }
      ToyValue::Number(n) => {
        let txt = n.to_string();
        self.alloc_string_from_code_units(&txt.encode_utf16().collect::<Vec<_>>())
      }
      ToyValue::Object(o) => match &self.objects[o.0].kind {
        ToyObjectKind::StringObject { string } => Ok(*string),
        _ => self.alloc_string_from_code_units(
          &"[object Object]".encode_utf16().collect::<Vec<_>>(),
        ),
      },
      ToyValue::Symbol(_) => Err(ToyError::Unimplemented("ToString(Symbol)")),
    }
  }

  fn to_number(&mut self, value: Self::Value) -> Result<f64, Self::Error> {
    match value {
      ToyValue::Number(n) => Ok(n),
      ToyValue::Bool(true) => Ok(1.0),
      ToyValue::Bool(false) => Ok(0.0),
      ToyValue::Null => Ok(0.0),
      ToyValue::Undefined => Ok(f64::NAN),
      _ => Err(ToyError::Unimplemented("ToNumber for non-primitive")),
    }
  }

  fn type_error(&mut self, message: &'static str) -> Self::Error {
    ToyError::TypeError(message.to_string())
  }

  fn get(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Self::Value, Self::Error> {
    let data = &self.objects[object.0];
    if let Some((_k, v)) = data.props.iter().find(|(k, _)| *k == key) {
      return Ok(*v);
    }
    Ok(ToyValue::Undefined)
  }

  fn get_method(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<Self::Value>, Self::Error> {
    self.get_method_calls += 1;
    let v = self.get(object, key)?;
    match v {
      ToyValue::Undefined | ToyValue::Null => Ok(None),
      ToyValue::Object(o) => match &self.objects[o.0].kind {
        ToyObjectKind::IteratorMethod { .. } | ToyObjectKind::AsyncIteratorMethod { .. } => {
          Ok(Some(v))
        }
        _ => Err(ToyError::TypeError("property is not callable".to_string())),
      },
      _ => Err(ToyError::TypeError("property is not callable".to_string())),
    }
  }

  fn own_property_keys(
    &mut self,
    object: Self::Object,
  ) -> Result<Vec<PropertyKey<Self::String, Self::Symbol>>, Self::Error> {
    Ok(
      self.objects[object.0]
        .props
        .iter()
        .map(|(k, _)| *k)
        .collect(),
    )
  }

  fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<Self::String, Self::Error> {
    let idx = self.strings.len();
    self.strings.push(units.to_vec());
    Ok(ToyString(idx))
  }

  fn alloc_object(&mut self) -> Result<Self::Object, Self::Error> {
    let idx = self.objects.len();
    self.objects.push(ToyObjectData {
      kind: ToyObjectKind::Ordinary,
      ..ToyObjectData::default()
    });
    Ok(ToyObject(idx))
  }

  fn alloc_array(&mut self, len: usize) -> Result<Self::Object, Self::Error> {
    let idx = self.objects.len();
    self.objects.push(ToyObjectData {
      kind: ToyObjectKind::Array { len },
      ..ToyObjectData::default()
    });
    Ok(ToyObject(idx))
  }

  fn create_data_property_or_throw(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
    value: Self::Value,
  ) -> Result<(), Self::Error> {
    let data = &mut self.objects[object.0];
    if let Some((_k, v)) = data.props.iter_mut().find(|(k, _v)| *k == key) {
      *v = value;
      return Ok(());
    }
    data.props.push((key, value));
    Ok(())
  }

  fn set_integrity_level_frozen(&mut self, object: Self::Object) -> Result<(), Self::Error> {
    self.objects[object.0].frozen = true;
    Ok(())
  }

  fn well_known_symbol(&mut self, sym: WellKnownSymbol) -> Result<Self::Symbol, Self::Error> {
    Ok(match sym {
      WellKnownSymbol::Iterator => ToySymbol(0),
      WellKnownSymbol::AsyncIterator => ToySymbol(1),
    })
  }

  fn get_iterator(&mut self, value: Self::Value) -> Result<Self::Object, Self::Error> {
    let ToyValue::Object(obj) = value else {
      return Err(ToyError::TypeError("GetIterator expected object".to_string()));
    };
    let iter_sym = self.well_known_symbol(WellKnownSymbol::Iterator)?;
    let method = self
      .get_method(obj, PropertyKey::Symbol(iter_sym))?
      .ok_or(ToyError::TypeError("GetIterator: value is not iterable".to_string()))?;
    self.get_iterator_from_method(obj, method)
  }

  fn get_iterator_from_method(
    &mut self,
    _object: Self::Object,
    method: Self::Value,
  ) -> Result<Self::Object, Self::Error> {
    let ToyValue::Object(method_obj) = method else {
      return Err(ToyError::TypeError(
        "GetIteratorFromMethod expected object method".to_string(),
      ));
    };
    let values = match &self.objects[method_obj.0].kind {
      ToyObjectKind::IteratorMethod { values } | ToyObjectKind::AsyncIteratorMethod { values } => {
        values.clone()
      }
      _ => {
        return Err(ToyError::TypeError(
          "GetIteratorFromMethod: method is not iterable".to_string(),
        ));
      }
    };
    Ok(self.alloc_object_with_kind(ToyObjectKind::Iterator { values, index: 0 }))
  }

  fn iterator_next(&mut self, iterator: Self::Object) -> Result<IteratorResult<Self::Value>, Self::Error> {
    let ToyObjectKind::Iterator { values, index } = &mut self.objects[iterator.0].kind else {
      return Err(ToyError::TypeError(
        "IteratorNext expected iterator object".to_string(),
      ));
    };
    if *index >= values.len() {
      return Ok(IteratorResult {
        value: ToyValue::Undefined,
        done: true,
      });
    }
    let v = values[*index];
    *index += 1;
    Ok(IteratorResult { value: v, done: false })
  }
}

impl WebIdlJsRuntime for ToyRuntime {
  fn is_callable(&self, _value: Self::Value) -> bool {
    false
  }

  fn is_bigint(&self, _value: Self::Value) -> bool {
    false
  }

  fn to_bigint(&mut self, _value: Self::Value) -> Result<Self::Value, Self::Error> {
    Err(ToyError::Unimplemented("ToBigInt"))
  }

  fn to_numeric(&mut self, _value: Self::Value) -> Result<Self::Value, Self::Error> {
    Err(ToyError::Unimplemented("ToNumeric"))
  }

  fn get_own_property(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<JsOwnPropertyDescriptor<Self::Value>>, Self::Error> {
    let data = &self.objects[object.0];
    let Some((_k, v)) = data.props.iter().find(|(k, _)| *k == key) else {
      return Ok(None);
    };

    Ok(Some(JsOwnPropertyDescriptor {
      enumerable: true,
      kind: JsPropertyKind::Data { value: *v },
    }))
  }

  fn throw_type_error(&mut self, message: &str) -> Self::Error {
    ToyError::TypeError(message.to_string())
  }

  fn throw_range_error(&mut self, message: &str) -> Self::Error {
    ToyError::RangeError(message.to_string())
  }

  fn is_array_buffer(&self, _value: Self::Value) -> bool {
    false
  }

  fn is_shared_array_buffer(&self, _value: Self::Value) -> bool {
    false
  }

  fn is_data_view(&self, _value: Self::Value) -> bool {
    false
  }

  fn typed_array_name(&self, _value: Self::Value) -> Option<&'static str> {
    None
  }
}
