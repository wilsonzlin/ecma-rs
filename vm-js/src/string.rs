use std::cmp::Ordering;
use std::fmt;

/// A JavaScript String value.
///
/// Per ECMAScript, strings are sequences of UTF-16 code units and may contain
/// unpaired surrogate code units.
#[derive(Clone)]
pub struct JsString {
  units: Box<[u16]>,
  hash64: u64,
}

impl JsString {
  pub fn from_code_units(units: &[u16]) -> Self {
    Self::from_u16_vec(units.to_vec())
  }

  pub fn from_u16_vec(mut units: Vec<u16>) -> Self {
    // Prefer an exact-sized backing allocation (avoid spare capacity).
    units.shrink_to_fit();
    let units = units.into_boxed_slice();
    let hash64 = stable_hash64(units.as_ref());
    Self { units, hash64 }
  }

  pub fn len_code_units(&self) -> usize {
    self.units.len()
  }

  pub fn is_empty(&self) -> bool {
    self.units.is_empty()
  }

  pub fn as_code_units(&self) -> &[u16] {
    self.units.as_ref()
  }

  pub fn to_utf8_lossy(&self) -> String {
    String::from_utf16_lossy(self.as_code_units())
  }

  pub fn stable_hash64(&self) -> u64 {
    self.hash64
  }

  pub(crate) fn heap_size_bytes(&self) -> usize {
    Self::heap_size_bytes_for_len(self.units.len())
  }

  pub(crate) fn heap_size_bytes_for_len(units_len: usize) -> usize {
    // Payload bytes owned by this string allocation.
    //
    // Note: `JsString` headers are stored inline in the heap slot table, so this size intentionally
    // excludes `mem::size_of::<JsString>()` and only counts the backing UTF-16 buffer.
    units_len.checked_mul(2).unwrap_or(usize::MAX)
  }
}

impl PartialEq for JsString {
  fn eq(&self, other: &Self) -> bool {
    self.units == other.units
  }
}

impl Eq for JsString {}

impl PartialOrd for JsString {
  fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    Some(self.cmp(other))
  }
}

impl Ord for JsString {
  fn cmp(&self, other: &Self) -> Ordering {
    self.units.as_ref().cmp(other.units.as_ref())
  }
}

impl fmt::Debug for JsString {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    // Rust `String` cannot represent lone surrogates; use a lossy conversion so
    // Debug never panics.
    f.debug_struct("JsString")
      .field("len_code_units", &self.len_code_units())
      .field("utf8_lossy", &self.to_utf8_lossy())
      .finish()
  }
}

const FNV_OFFSET_BASIS_64: u64 = 0xcbf29ce484222325;
const FNV_PRIME_64: u64 = 0x00000100000001B3;

fn stable_hash64(units: &[u16]) -> u64 {
  let mut hash = FNV_OFFSET_BASIS_64;
  for unit in units {
    for byte in unit.to_le_bytes() {
      hash ^= byte as u64;
      hash = hash.wrapping_mul(FNV_PRIME_64);
    }
  }
  hash
}
