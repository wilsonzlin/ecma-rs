use crate::error::VmError;
use crate::heap::{GcString, Heap};

pub struct Scope {
  heap: Heap,
}

impl Scope {
  pub fn new(max_heap_bytes: usize) -> Self {
    Self {
      heap: Heap::new(max_heap_bytes),
    }
  }

  pub fn heap(&self) -> &Heap {
    &self.heap
  }

  pub fn heap_mut(&mut self) -> &mut Heap {
    &mut self.heap
  }

  pub fn alloc_string_from_utf8(&mut self, s: &str) -> Result<GcString, VmError> {
    let units: Vec<u16> = s.encode_utf16().collect();
    self.alloc_string_from_u16_vec(units)
  }

  pub fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<GcString, VmError> {
    self.heap.alloc_string_from_code_units(units)
  }

  pub fn alloc_string_from_u16_vec(&mut self, units: Vec<u16>) -> Result<GcString, VmError> {
    self.heap.alloc_string_from_u16_vec(units)
  }
}

