use crate::GcString;

/// A heap-allocated JS Symbol record.
///
/// Note: equality for `GcSymbol` is based on handle identity. `id` exists for
/// debug/introspection and is monotonically assigned by the heap.
#[derive(Debug)]
pub struct JsSymbol {
  id: u64,
  description: Option<GcString>,
}

impl JsSymbol {
  pub(crate) fn new(id: u64, description: Option<GcString>) -> Self {
    Self { id, description }
  }

  pub fn id(&self) -> u64 {
    self.id
  }

  pub fn description(&self) -> Option<GcString> {
    self.description
  }
}

