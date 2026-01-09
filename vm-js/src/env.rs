use crate::heap::{Trace, Tracer};
use crate::{GcEnv, GcObject, GcString, Heap, Value, VmError};
use core::mem;
use semantic_js::js::SymbolId;

#[derive(Debug)]
pub(crate) struct DeclarativeEnvRecord {
  pub(crate) outer: Option<GcEnv>,
  pub(crate) bindings: Box<[EnvBinding]>,
  pub(crate) this_value: Option<Value>,
  pub(crate) new_target: Option<Value>,
}

impl DeclarativeEnvRecord {
  pub(crate) fn new(outer: Option<GcEnv>) -> Self {
    Self {
      outer,
      bindings: Box::default(),
      this_value: None,
      new_target: None,
    }
  }

  pub(crate) fn new_with_bindings(outer: Option<GcEnv>, bindings: Box<[EnvBinding]>) -> Self {
    Self {
      outer,
      bindings,
      this_value: None,
      new_target: None,
    }
  }

  pub(crate) fn find_binding_index(
    &self,
    heap: &Heap,
    name: &str,
  ) -> Result<Option<usize>, VmError> {
    for (idx, binding) in self.bindings.iter().enumerate() {
      let Some(binding_name) = binding.name else {
        continue;
      };
      if gc_string_eq_str(heap, binding_name, name)? {
        return Ok(Some(idx));
      }
    }
    Ok(None)
  }

  #[inline]
  fn symbol_binding_index(&self, symbol: SymbolId) -> Option<usize> {
    self
      .bindings
      .binary_search_by_key(&symbol, |binding| binding.symbol)
      .ok()
  }

  pub(crate) fn has_symbol_binding(&self, symbol: SymbolId) -> bool {
    self.symbol_binding_index(symbol).is_some()
  }

  pub(crate) fn get_symbol_binding_value(&self, symbol: SymbolId) -> Result<Value, VmError> {
    let idx = self
      .symbol_binding_index(symbol)
      .ok_or(VmError::Unimplemented("unbound identifier"))?;
    let binding = self
      .bindings
      .get(idx)
      .ok_or(VmError::Unimplemented(
        "environment record binding index out of bounds",
      ))?;
    if !binding.initialized {
      // TDZ.
      //
      // EnvRecords do not have access to a Realm to construct a `ReferenceError` object, so we use
      // the same sentinel throw value as the name-based binding API (`Heap::env_get_binding_value`)
      // and rely on higher-level execution code to convert it.
      return Err(VmError::Throw(Value::Null));
    }
    Ok(binding.value)
  }

  pub(crate) fn initialize_symbol_binding(
    &mut self,
    symbol: SymbolId,
    value: Value,
  ) -> Result<(), VmError> {
    let idx = self
      .symbol_binding_index(symbol)
      .ok_or(VmError::Unimplemented("unbound identifier"))?;
    let binding = self
      .bindings
      .get_mut(idx)
      .ok_or(VmError::Unimplemented(
        "environment record binding index out of bounds",
      ))?;
    if binding.initialized {
      return Err(VmError::Unimplemented("binding already initialized"));
    }
    binding.value = value;
    binding.initialized = true;
    Ok(())
  }

  pub(crate) fn set_mutable_symbol_binding(
    &mut self,
    symbol: SymbolId,
    value: Value,
  ) -> Result<(), VmError> {
    let idx = self
      .symbol_binding_index(symbol)
      .ok_or(VmError::Unimplemented("unbound identifier"))?;
    let binding = self
      .bindings
      .get_mut(idx)
      .ok_or(VmError::Unimplemented(
        "environment record binding index out of bounds",
      ))?;
    if !binding.initialized {
      // TDZ sentinel; see `get_symbol_binding_value`.
      return Err(VmError::Throw(Value::Null));
    }
    if !binding.mutable {
      // Assignment to const sentinel; higher-level execution code maps this to a `TypeError`.
      return Err(VmError::Throw(Value::Undefined));
    }
    binding.value = value;
    Ok(())
  }
}

#[derive(Debug)]
pub(crate) struct ObjectEnvRecord {
  pub(crate) outer: Option<GcEnv>,
  pub(crate) binding_object: GcObject,
  #[allow(dead_code)]
  pub(crate) with_environment: bool,
}

impl ObjectEnvRecord {
  pub(crate) fn heap_size_bytes() -> usize {
    mem::size_of::<Self>()
  }
}

#[derive(Debug)]
pub(crate) enum EnvRecord {
  Declarative(DeclarativeEnvRecord),
  Object(ObjectEnvRecord),
}

impl EnvRecord {
  pub(crate) fn new(outer: Option<GcEnv>) -> Self {
    EnvRecord::Declarative(DeclarativeEnvRecord::new(outer))
  }

  pub(crate) fn new_with_bindings(outer: Option<GcEnv>, bindings: Box<[EnvBinding]>) -> Self {
    EnvRecord::Declarative(DeclarativeEnvRecord::new_with_bindings(outer, bindings))
  }

  pub(crate) fn heap_size_bytes_for_binding_count(count: usize) -> usize {
    // Payload bytes owned by this environment record allocation.
    //
    // Note: `EnvRecord` headers are stored inline in the heap slot table, so this size
    // intentionally excludes `mem::size_of::<EnvRecord>()` and only counts the backing binding
    // table allocation.
    count
      .checked_mul(mem::size_of::<EnvBinding>())
      .unwrap_or(usize::MAX)
  }

  pub(crate) fn outer(&self) -> Option<GcEnv> {
    match self {
      EnvRecord::Declarative(env) => env.outer,
      EnvRecord::Object(env) => env.outer,
    }
  }
}

impl Trace for EnvRecord {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    match self {
      EnvRecord::Declarative(env) => {
        if let Some(outer) = env.outer {
          tracer.trace_env(outer);
        }
        for binding in env.bindings.iter() {
          binding.trace(tracer);
        }
        if let Some(this_value) = env.this_value {
          tracer.trace_value(this_value);
        }
        if let Some(new_target) = env.new_target {
          tracer.trace_value(new_target);
        }
      }
      EnvRecord::Object(env) => {
        if let Some(outer) = env.outer {
          tracer.trace_env(outer);
        }
        tracer.trace_value(Value::Object(env.binding_object));
      }
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub struct EnvBinding {
  pub symbol: SymbolId,
  pub name: Option<GcString>,
  pub value: Value,
  pub mutable: bool,
  pub initialized: bool,
  pub strict: bool,
}

impl Trace for EnvBinding {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(name) = self.name {
      tracer.trace_value(Value::String(name));
    }
    tracer.trace_value(self.value);
  }
}

pub(crate) fn gc_string_eq_str(heap: &Heap, s: GcString, needle: &str) -> Result<bool, VmError> {
  let s = heap.get_string(s)?;
  Ok(needle.encode_utf16().eq(s.as_code_units().iter().copied()))
}
