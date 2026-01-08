use std::sync::Arc;

/// Opaque object handle for later GC integration.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct ObjectId(pub(crate) u64);

/// JavaScript value placeholder.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
  Undefined,
  Null,
  Bool(bool),
  Number(f64),
  String(Arc<str>),
  Object(ObjectId),
}
