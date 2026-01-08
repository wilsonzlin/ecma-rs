use crate::error::Termination;
use crate::error::TerminationReason;
use crate::error::VmError;
use crate::gc::{Trace, Tracer};
use crate::string::JsString;

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub struct GcString(pub(crate) usize);

pub enum HeapObject {
  String(JsString),
}

impl Trace for HeapObject {
  fn trace(&self, tracer: &mut Tracer) {
    match self {
      HeapObject::String(s) => s.trace(tracer),
    }
  }
}

pub struct Heap {
  max_bytes: usize,
  used_bytes: usize,
  objects: Vec<HeapObject>,
}

impl Heap {
  pub fn new(max_bytes: usize) -> Self {
    Self {
      max_bytes,
      used_bytes: 0,
      objects: Vec::new(),
    }
  }

  pub fn max_bytes(&self) -> usize {
    self.max_bytes
  }

  pub fn used_bytes(&self) -> usize {
    self.used_bytes
  }

  pub(crate) fn try_alloc_bytes(&self, bytes: usize) -> Result<(), VmError> {
    match self.max_bytes.checked_sub(self.used_bytes) {
      Some(remaining) if bytes <= remaining => Ok(()),
      _ => Err(VmError::Termination(Termination::new(
        TerminationReason::OutOfMemory,
        Vec::new(),
      ))),
    }
  }

  pub fn alloc_string(&mut self, string: JsString) -> Result<GcString, VmError> {
    let bytes = string.heap_size_bytes();
    self.try_alloc_bytes(bytes)?;
    let idx = self.objects.len();
    self.objects.push(HeapObject::String(string));
    self.used_bytes += bytes;
    Ok(GcString(idx))
  }

  pub fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<GcString, VmError> {
    let bytes = JsString::heap_size_bytes_for_len(units.len());
    self.try_alloc_bytes(bytes)?;
    self.alloc_string(JsString::from_code_units(units))
  }

  pub fn alloc_string_from_u16_vec(&mut self, units: Vec<u16>) -> Result<GcString, VmError> {
    let bytes = JsString::heap_size_bytes_for_len(units.len());
    self.try_alloc_bytes(bytes)?;
    self.alloc_string(JsString::from_u16_vec(units))
  }

  pub fn get_string(&self, s: GcString) -> &JsString {
    match &self.objects[s.0] {
      HeapObject::String(s) => s,
    }
  }
}
