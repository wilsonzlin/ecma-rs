use std::fmt;

/// A WebIDL `undefined` value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct IdlUndefined;

/// A UTF-16 code unit string used by WebIDL types like `DOMString`, `ByteString`, and `USVString`.
#[derive(Clone, PartialEq, Eq, Hash)]
pub struct IdlString {
  code_units: Vec<u16>,
}

impl fmt::Debug for IdlString {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_tuple("IdlString")
      .field(&format_args!("{:?}", &self.code_units))
      .finish()
  }
}

impl IdlString {
  pub fn from_code_units(code_units: Vec<u16>) -> Self {
    Self { code_units }
  }

  pub fn code_units(&self) -> &[u16] {
    &self.code_units
  }

  pub fn from_str(s: &str) -> Self {
    Self {
      code_units: s.encode_utf16().collect(),
    }
  }
}

pub type DomString = IdlString;
pub type ByteString = IdlString;
pub type UsvString = IdlString;

/// A WebIDL `record<K, V>` value.
///
/// This is a newtype wrapper around `Vec<(K, V)>` so we can provide a `ToJsValue`
/// implementation without conflicting with the `Vec<T>` sequence implementation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct IdlRecord<K, V>(pub Vec<(K, V)>);

/// A WebIDL `FrozenArray<T>` value.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrozenArray<T>(pub Vec<T>);
