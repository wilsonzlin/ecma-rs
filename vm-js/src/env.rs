use crate::heap::{Trace, Tracer};
use crate::{GcEnv, GcString, Heap, Value, VmError};
use core::mem;

#[derive(Debug)]
pub(crate) struct EnvRecord {
  pub(crate) outer: Option<GcEnv>,
  pub(crate) bindings: Box<[EnvBinding]>,
}

impl EnvRecord {
  pub(crate) fn new(outer: Option<GcEnv>) -> Self {
    Self {
      outer,
      bindings: Box::default(),
    }
  }

  pub(crate) fn heap_size_bytes_for_binding_count(count: usize) -> usize {
    let bindings_bytes = count
      .checked_mul(mem::size_of::<EnvBinding>())
      .unwrap_or(usize::MAX);
    mem::size_of::<Self>()
      .checked_add(bindings_bytes)
      .unwrap_or(usize::MAX)
  }

  pub(crate) fn find_binding_index(&self, heap: &Heap, name: &str) -> Result<Option<usize>, VmError> {
    for (idx, binding) in self.bindings.iter().enumerate() {
      if gc_string_eq_str(heap, binding.name, name)? {
        return Ok(Some(idx));
      }
    }
    Ok(None)
  }
}

impl Trace for EnvRecord {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(outer) = self.outer {
      tracer.trace_env(outer);
    }
    for binding in self.bindings.iter() {
      binding.trace(tracer);
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct EnvBinding {
  pub(crate) name: GcString,
  pub(crate) value: Value,
  pub(crate) mutable: bool,
  pub(crate) initialized: bool,
}

impl Trace for EnvBinding {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    tracer.trace_value(Value::String(self.name));
    tracer.trace_value(self.value);
  }
}

pub(crate) fn gc_string_eq_str(heap: &Heap, s: GcString, needle: &str) -> Result<bool, VmError> {
  let s = heap.get_string(s)?;
  Ok(needle.encode_utf16().eq(s.as_code_units().iter().copied()))
}
