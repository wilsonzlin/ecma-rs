use crate::heap::{Trace, Tracer};
use crate::{GcString, GcSymbol, Heap, Value, VmError};

/// A JavaScript property key (ECMAScript `PropertyKey`).
///
/// This mirrors the spec's `PropertyKey` union: `String | Symbol`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum PropertyKey {
  String(GcString),
  Symbol(GcSymbol),
}

impl PropertyKey {
  pub fn from_string(value: GcString) -> Self {
    Self::String(value)
  }

  pub fn from_symbol(value: GcSymbol) -> Self {
    Self::Symbol(value)
  }
}

impl Trace for PropertyKey {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    match self {
      PropertyKey::String(s) => tracer.trace_value(Value::String(*s)),
      PropertyKey::Symbol(s) => tracer.trace_value(Value::Symbol(*s)),
    }
  }
}

/// A concrete property descriptor.
#[derive(Debug, Clone, Copy)]
pub struct PropertyDescriptor {
  pub enumerable: bool,
  pub configurable: bool,
  pub kind: PropertyKind,
}

impl Trace for PropertyDescriptor {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    self.kind.trace(tracer);
  }
}

/// The kind of property described by a [`PropertyDescriptor`].
#[derive(Debug, Clone, Copy)]
pub enum PropertyKind {
  Data { value: Value, writable: bool },
  Accessor { get: Value, set: Value },
}

impl Trace for PropertyKind {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    match self {
      PropertyKind::Data { value, .. } => tracer.trace_value(*value),
      PropertyKind::Accessor { get, set } => {
        tracer.trace_value(*get);
        tracer.trace_value(*set);
      }
    }
  }
}

/// A "partial" property descriptor patch used by `DefineProperty`-style operations.
#[derive(Debug, Default, Clone, Copy)]
pub struct PropertyDescriptorPatch {
  pub enumerable: Option<bool>,
  pub configurable: Option<bool>,
  pub value: Option<Value>,
  pub writable: Option<bool>,
  pub get: Option<Value>,
  pub set: Option<Value>,
}

impl PropertyDescriptorPatch {
  /// Validates that this patch does not mix data and accessor descriptor fields.
  ///
  /// Per ECMAScript, a descriptor cannot be both a Data Descriptor and an Accessor Descriptor.
  pub fn validate(&self) -> Result<(), VmError> {
    let has_data = self.value.is_some() || self.writable.is_some();
    let has_accessor = self.get.is_some() || self.set.is_some();
    if has_data && has_accessor {
      return Err(VmError::InvalidPropertyDescriptorPatch);
    }
    Ok(())
  }
}

impl Trace for PropertyDescriptorPatch {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(v) = self.value {
      tracer.trace_value(v);
    }
    if let Some(v) = self.get {
      tracer.trace_value(v);
    }
    if let Some(v) = self.set {
      tracer.trace_value(v);
    }
  }
}

impl Heap {
  /// Compare two property keys.
  ///
  /// - String keys compare by UTF-16 code units.
  /// - Symbol keys compare by identity (handle equality).
  pub fn property_key_eq(&self, a: &PropertyKey, b: &PropertyKey) -> bool {
    match (a, b) {
      (PropertyKey::String(a), PropertyKey::String(b)) => {
        let Ok(a) = self.get_string(*a) else {
          return false;
        };
        let Ok(b) = self.get_string(*b) else {
          return false;
        };
        a.as_code_units() == b.as_code_units()
      }
      (PropertyKey::Symbol(a), PropertyKey::Symbol(b)) => a == b,
      _ => false,
    }
  }

  /// Attempts to parse `s` as an ECMAScript array index.
  ///
  /// This matches the `ToString(ToUint32(P)) === P` and `ToUint32(P) != 2^32-1` conditions used by
  /// `OrdinaryOwnPropertyKeys`.
  pub fn string_to_array_index(&self, s: GcString) -> Result<Option<u32>, VmError> {
    let s = self.get_string(s)?;
    let units = s.as_code_units();
    if units.is_empty() {
      return Ok(None);
    }

    const U0: u16 = b'0' as u16;
    const U9: u16 = b'9' as u16;

    // No leading zeros (except the single "0").
    if units.len() > 1 && units[0] == U0 {
      return Ok(None);
    }

    let mut value: u64 = 0;
    for &u in units {
      if !(U0..=U9).contains(&u) {
        return Ok(None);
      }
      value = match value.checked_mul(10).and_then(|v| v.checked_add((u - U0) as u64)) {
        Some(v) => v,
        None => return Ok(None),
      };
      if value > u32::MAX as u64 {
        return Ok(None);
      }
    }

    // Exclude 2^32-1.
    if value == u32::MAX as u64 {
      return Ok(None);
    }
    Ok(Some(value as u32))
  }

  /// Attempts to parse `key` as an ECMAScript array index.
  pub fn property_key_to_array_index(&self, key: &PropertyKey) -> Result<Option<u32>, VmError> {
    match key {
      PropertyKey::String(s) => self.string_to_array_index(*s),
      PropertyKey::Symbol(_) => Ok(None),
    }
  }

  /// Convert a value to a property key.
  ///
  /// This is a minimal stub (sufficient for early scaffolding):
  /// - `String`/`Symbol` values are returned directly.
  /// - All other values will eventually go through `ToPropertyKey` (ToPrimitive + ToString).
  ///   For now, we call the `to_string` placeholder which returns
  ///   [`VmError::Unimplemented`].
  pub fn to_property_key(&mut self, value: Value) -> Result<PropertyKey, VmError> {
    match value {
      Value::String(s) => Ok(PropertyKey::String(s)),
      Value::Symbol(s) => Ok(PropertyKey::Symbol(s)),
      other => Ok(PropertyKey::String(self.to_string(other)?)),
    }
  }

  /// Placeholder for ECMAScript `ToString`.
  ///
  /// Full `ToString` / `ToPropertyKey` semantics will be implemented once the interpreter and
  /// built-ins exist.
  pub fn to_string(&mut self, _value: Value) -> Result<GcString, VmError> {
    Err(VmError::Unimplemented(
      "ToString / ToPropertyKey requires interpreter + built-ins",
    ))
  }
}
