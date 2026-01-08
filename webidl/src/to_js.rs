use crate::{
  error::{WebIdlError, WebIdlLimit},
  idl::{FrozenArray, IdlRecord, IdlString, IdlUndefined},
  JsRuntime, PropertyKey, WebIdlLimits,
};

pub trait ToJsValue<R: JsRuntime> {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError>;
}

pub trait ToJsPropertyKey<R: JsRuntime> {
  fn to_property_key(
    &self,
    rt: &mut R,
    limits: &WebIdlLimits,
  ) -> Result<PropertyKey<R::String, R::Symbol>, WebIdlError>;
}

impl<R: JsRuntime> ToJsPropertyKey<R> for IdlString {
  fn to_property_key(
    &self,
    rt: &mut R,
    limits: &WebIdlLimits,
  ) -> Result<PropertyKey<R::String, R::Symbol>, WebIdlError> {
    if self.code_units().len() > limits.max_string_code_units {
      return Err(WebIdlError::limit_exceeded(
        WebIdlLimit::MaxStringCodeUnits,
        self.code_units().len(),
        limits.max_string_code_units,
      ));
    }

    let s = rt
      .alloc_string_from_code_units(self.code_units())
      .map_err(WebIdlError::js)?;
    Ok(rt.to_property_key_from_string(s))
  }
}

impl<R: JsRuntime> ToJsPropertyKey<R> for &str {
  fn to_property_key(
    &self,
    rt: &mut R,
    limits: &WebIdlLimits,
  ) -> Result<PropertyKey<R::String, R::Symbol>, WebIdlError> {
    let units: Vec<u16> = self.encode_utf16().collect();
    if units.len() > limits.max_string_code_units {
      return Err(WebIdlError::limit_exceeded(
        WebIdlLimit::MaxStringCodeUnits,
        units.len(),
        limits.max_string_code_units,
      ));
    }

    let s = rt
      .alloc_string_from_code_units(&units)
      .map_err(WebIdlError::js)?;
    Ok(rt.to_property_key_from_string(s))
  }
}

/// Converts an array index `i` into a property key representing `ToString(i)`.
pub fn index_to_property_key<R: JsRuntime>(
  rt: &mut R,
  index: usize,
) -> Result<PropertyKey<R::String, R::Symbol>, WebIdlError> {
  // Max digits for u64 is 20; `usize` is <= u64 on supported platforms.
  let mut buf = [0u16; 20];
  let mut i = buf.len();

  let mut n = index;
  if n == 0 {
    i -= 1;
    buf[i] = b'0' as u16;
  } else {
    while n != 0 {
      let digit = (n % 10) as u16;
      n /= 10;
      i -= 1;
      buf[i] = (b'0' as u16) + digit;
    }
  }

  let s = rt
    .alloc_string_from_code_units(&buf[i..])
    .map_err(WebIdlError::js)?;
  Ok(rt.to_property_key_from_string(s))
}

pub fn sequence_to_js_array<R: JsRuntime, T: ToJsValue<R>>(
  rt: &mut R,
  limits: &WebIdlLimits,
  seq: &[T],
) -> Result<R::Object, WebIdlError> {
  if seq.len() > limits.max_sequence_length {
    return Err(WebIdlError::limit_exceeded(
      WebIdlLimit::MaxSequenceLength,
      seq.len(),
      limits.max_sequence_length,
    ));
  }

  let array = rt.alloc_array(seq.len()).map_err(WebIdlError::js)?;
  for (i, el) in seq.iter().enumerate() {
    let js_el = el.to_js(rt, limits)?;
    let key = index_to_property_key(rt, i)?;
    rt.create_data_property_or_throw(array, key, js_el)
      .map_err(WebIdlError::js)?;
  }
  Ok(array)
}

pub fn record_to_js_object<R: JsRuntime, K: ToJsPropertyKey<R>, V: ToJsValue<R>>(
  rt: &mut R,
  limits: &WebIdlLimits,
  entries: &[(K, V)],
) -> Result<R::Object, WebIdlError> {
  if entries.len() > limits.max_record_entries {
    return Err(WebIdlError::limit_exceeded(
      WebIdlLimit::MaxRecordEntries,
      entries.len(),
      limits.max_record_entries,
    ));
  }

  let obj = rt.alloc_object().map_err(WebIdlError::js)?;
  for (k, v) in entries.iter() {
    let key = k.to_property_key(rt, limits)?;
    let value = v.to_js(rt, limits)?;
    rt.create_data_property_or_throw(obj, key, value)
      .map_err(WebIdlError::js)?;
  }
  Ok(obj)
}

/// Helper for dictionary conversions.
///
/// Codegen should call this helper and provide `build` that adds members in the required
/// WebIDL serialization order:
/// - dictionaries from least to most derived
/// - members in lexicographic order
pub fn dictionary_to_js<R: JsRuntime>(
  rt: &mut R,
  limits: &WebIdlLimits,
  build: impl FnOnce(&mut R, &WebIdlLimits, R::Object) -> Result<(), WebIdlError>,
) -> Result<R::Value, WebIdlError> {
  let obj = rt.alloc_object().map_err(WebIdlError::js)?;
  build(rt, limits, obj)?;
  Ok(rt.value_object(obj))
}

/// Helper for union conversions.
///
/// Codegen should `match` on the union's active variant and pass the contained member value to this
/// helper (or call [`ToJsValue::to_js`] directly).
pub fn union_to_js<R: JsRuntime, T: ToJsValue<R>>(
  rt: &mut R,
  limits: &WebIdlLimits,
  value: &T,
) -> Result<R::Value, WebIdlError> {
  value.to_js(rt, limits)
}

impl<R: JsRuntime> ToJsValue<R> for IdlUndefined {
  fn to_js(&self, rt: &mut R, _limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    Ok(rt.value_undefined())
  }
}

impl<R: JsRuntime> ToJsValue<R> for () {
  fn to_js(&self, rt: &mut R, _limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    Ok(rt.value_undefined())
  }
}

impl<R: JsRuntime> ToJsValue<R> for bool {
  fn to_js(&self, rt: &mut R, _limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    Ok(rt.value_bool(*self))
  }
}

macro_rules! impl_int_to_js {
  ($($t:ty),* $(,)?) => {
    $(
      impl<R: JsRuntime> ToJsValue<R> for $t {
        fn to_js(&self, rt: &mut R, _limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
          Ok(rt.value_number(*self as f64))
        }
      }
    )*
  };
}

impl_int_to_js!(i8, u8, i16, u16, i32, u32, i64, u64, isize, usize);

impl<R: JsRuntime> ToJsValue<R> for f64 {
  fn to_js(&self, rt: &mut R, _limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    Ok(rt.value_number(*self))
  }
}

impl<R: JsRuntime> ToJsValue<R> for IdlString {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    if self.code_units().len() > limits.max_string_code_units {
      return Err(WebIdlError::limit_exceeded(
        WebIdlLimit::MaxStringCodeUnits,
        self.code_units().len(),
        limits.max_string_code_units,
      ));
    }

    let s = rt
      .alloc_string_from_code_units(self.code_units())
      .map_err(WebIdlError::js)?;
    Ok(rt.value_string(s))
  }
}

impl<R: JsRuntime> ToJsValue<R> for &str {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    let units: Vec<u16> = self.encode_utf16().collect();
    if units.len() > limits.max_string_code_units {
      return Err(WebIdlError::limit_exceeded(
        WebIdlLimit::MaxStringCodeUnits,
        units.len(),
        limits.max_string_code_units,
      ));
    }

    let s = rt
      .alloc_string_from_code_units(&units)
      .map_err(WebIdlError::js)?;
    Ok(rt.value_string(s))
  }
}

impl<R: JsRuntime> ToJsValue<R> for String {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    self.as_str().to_js(rt, limits)
  }
}

impl<R: JsRuntime, T: ToJsValue<R>> ToJsValue<R> for Option<T> {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    match self {
      Some(v) => v.to_js(rt, limits),
      None => Ok(rt.value_null()),
    }
  }
}

impl<R: JsRuntime, T: ToJsValue<R>> ToJsValue<R> for Vec<T> {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    let obj = sequence_to_js_array(rt, limits, self)?;
    Ok(rt.value_object(obj))
  }
}

impl<R: JsRuntime, K: ToJsPropertyKey<R>, V: ToJsValue<R>> ToJsValue<R> for IdlRecord<K, V> {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    let obj = record_to_js_object(rt, limits, &self.0)?;
    Ok(rt.value_object(obj))
  }
}

impl<R: JsRuntime, T: ToJsValue<R>> ToJsValue<R> for FrozenArray<T> {
  fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
    let array = sequence_to_js_array(rt, limits, &self.0)?;
    rt.set_integrity_level_frozen(array)
      .map_err(WebIdlError::js)?;
    Ok(rt.value_object(array))
  }
}
