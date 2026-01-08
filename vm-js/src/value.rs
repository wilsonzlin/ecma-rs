use crate::{GcObject, GcString, GcSymbol};

/// A JavaScript value.
///
/// This is the VM's canonical value representation. Heap-allocated values are represented using
/// GC-managed handles (e.g. [`GcString`]).
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Value {
  /// The JavaScript `undefined` value.
  Undefined,
  /// The JavaScript `null` value.
  Null,
  /// A JavaScript boolean.
  Bool(bool),
  /// A JavaScript number (IEEE-754 double).
  Number(f64),
  /// A GC-managed JavaScript string.
  String(GcString),
  /// A GC-managed JavaScript symbol.
  Symbol(GcSymbol),
  /// A GC-managed JavaScript object.
  Object(GcObject),
}

impl From<GcString> for Value {
  fn from(value: GcString) -> Self {
    Self::String(value)
  }
}

impl From<GcSymbol> for Value {
  fn from(value: GcSymbol) -> Self {
    Self::Symbol(value)
  }
}

impl From<GcObject> for Value {
  fn from(value: GcObject) -> Self {
    Self::Object(value)
  }
}

