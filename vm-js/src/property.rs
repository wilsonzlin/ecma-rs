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

impl PropertyDescriptor {
  pub fn is_data_descriptor(&self) -> bool {
    matches!(self.kind, PropertyKind::Data { .. })
  }

  pub fn is_accessor_descriptor(&self) -> bool {
    matches!(self.kind, PropertyKind::Accessor { .. })
  }

  pub fn is_generic_descriptor(&self) -> bool {
    false
  }
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
  pub fn is_empty(&self) -> bool {
    self.enumerable.is_none()
      && self.configurable.is_none()
      && self.value.is_none()
      && self.writable.is_none()
      && self.get.is_none()
      && self.set.is_none()
  }

  pub fn is_data_descriptor(&self) -> bool {
    self.value.is_some() || self.writable.is_some()
  }

  pub fn is_accessor_descriptor(&self) -> bool {
    self.get.is_some() || self.set.is_some()
  }

  pub fn is_generic_descriptor(&self) -> bool {
    !self.is_data_descriptor() && !self.is_accessor_descriptor()
  }
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

  /// If `key` is a String that is an ECMAScript array index, returns its numeric value.
  ///
  /// An "array index" is a canonical `uint32` string `P` such that:
  /// - `ToString(ToUint32(P)) === P`, and
  /// - `ToUint32(P) !== 2^32 - 1`.
  ///
  /// This matches the ordering requirements for `OrdinaryOwnPropertyKeys`.
  pub(crate) fn array_index(&self, key: &PropertyKey) -> Option<u32> {
    let PropertyKey::String(s) = key else {
      return None;
    };
    let s = self.get_string(*s).ok()?;
    let units = s.as_code_units();
    if units.is_empty() {
      return None;
    }

    const U0: u16 = b'0' as u16;
    const U9: u16 = b'9' as u16;

    // `ToString(ToUint32(P)) === P` implies no leading zeros (except the single "0").
    if units.len() > 1 && units[0] == U0 {
      return None;
    }

    let mut value: u64 = 0;
    for &u in units {
      if !(U0..=U9).contains(&u) {
        return None;
      }
      value = value.checked_mul(10)?;
      value = value.checked_add((u - U0) as u64)?;
      if value > u32::MAX as u64 {
        return None;
      }
    }

    // Exclude 2^32-1.
    if value == u32::MAX as u64 {
      return None;
    }

    Some(value as u32)
  }

  /// Convert a value to a property key.
  ///
  /// This is a minimal implementation (sufficient for early scaffolding):
  /// - `String`/`Symbol` values are returned directly.
  /// - All other values go through a partial `ToPropertyKey` (`ToString` for now).
  pub fn to_property_key(&mut self, value: Value) -> Result<PropertyKey, VmError> {
    match value {
      Value::String(s) => Ok(PropertyKey::String(s)),
      Value::Symbol(s) => Ok(PropertyKey::Symbol(s)),
      other => Ok(PropertyKey::String(self.to_string(other)?)),
    }
  }

  /// Minimal ECMAScript `ToString`.
  ///
  /// This is intentionally small (sufficient for early interpreter scaffolding):
  /// - Objects stringify to `"[object Object]"` for now (no `ToPrimitive` / user `toString` yet).
  pub fn to_string(&mut self, value: Value) -> Result<GcString, VmError> {
    // Fast path: no allocation.
    if let Value::String(s) = value {
      return Ok(s);
    }

    // Allocate via a scope so we can root `value` across a GC triggered by the string allocation.
    let mut scope = self.scope();
    scope.push_root(value);

    match value {
      Value::Undefined => scope.alloc_string("undefined"),
      Value::Null => scope.alloc_string("null"),
      Value::Bool(true) => scope.alloc_string("true"),
      Value::Bool(false) => scope.alloc_string("false"),
      Value::Number(n) => {
        if n.is_nan() {
          scope.alloc_string("NaN")
        } else if n.is_infinite() {
          if n.is_sign_negative() {
            scope.alloc_string("-Infinity")
          } else {
            scope.alloc_string("Infinity")
          }
        } else if n == 0.0 {
          // `ToString(-0)` is `"0"` in ECMAScript.
          scope.alloc_string("0")
        } else {
          let mut buf = ryu::Buffer::new();
          let formatted = buf.format(n);
          // `ryu` formats `1.0` as `"1.0"`, but ECMAScript `ToString(1)` is `"1"`.
          let formatted = formatted.strip_suffix(".0").unwrap_or(formatted);
          scope.alloc_string(formatted)
        }
      }
      Value::String(_) => unreachable!(),
      Value::Symbol(_) => Err(VmError::TypeError("Cannot convert a Symbol value to a string")),
      Value::Object(_) => scope.alloc_string("[object Object]"),
    }
  }

  /// Minimal ECMAScript `ToBoolean`.
  pub fn to_boolean(&self, value: Value) -> Result<bool, VmError> {
    Ok(match value {
      Value::Undefined | Value::Null => false,
      Value::Bool(b) => b,
      Value::Number(n) => n != 0.0 && !n.is_nan(),
      Value::String(s) => !self.get_string(s)?.as_code_units().is_empty(),
      Value::Symbol(_) | Value::Object(_) => true,
    })
  }
}
