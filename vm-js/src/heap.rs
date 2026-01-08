use crate::string::JsString;
use crate::property::PropertyDescriptor;
use crate::symbol::JsSymbol;
use crate::{GcObject, GcString, GcSymbol, HeapId, RootId, Value, VmError};
use core::mem;
use std::collections::BTreeMap;

/// Heap configuration and memory limits.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HeapLimits {
  /// Hard memory limit for live heap allocations, in bytes.
  pub max_bytes: usize,
  /// When an allocation would cause `used_bytes` to exceed this threshold, the heap will trigger a
  /// GC cycle before attempting the allocation.
  pub gc_threshold: usize,
}

impl HeapLimits {
  /// Creates a new set of heap limits.
  pub fn new(max_bytes: usize, gc_threshold: usize) -> Self {
    Self {
      max_bytes,
      gc_threshold,
    }
  }
}

/// A non-moving mark/sweep GC heap.
///
/// The heap stores objects in a `Vec` of slots. GC handles store the slot `index` and a
/// per-slot `generation`, which makes handles stable across `Vec` reallocations and allows
/// detection of stale handles when slots are reused.
pub struct Heap {
  limits: HeapLimits,

  /// Bytes used by live allocations.
  used_bytes: usize,
  gc_runs: u64,

  // GC-managed allocations.
  slots: Vec<Slot>,
  marks: Vec<u8>,
  free_list: Vec<u32>,

  next_symbol_id: u64,

  // Root sets.
  pub(crate) root_stack: Vec<Value>,
  persistent_roots: Vec<Option<Value>>,
  persistent_roots_free: Vec<u32>,

  // Global symbol registry for `Symbol.for`-like behaviour.
  //
  // The registry is scanned during GC (as an additional root set) to keep
  // interned symbols alive.
  symbol_registry: BTreeMap<JsString, GcSymbol>,
}

impl Heap {
  /// Creates a new heap with the provided memory limits.
  pub fn new(limits: HeapLimits) -> Self {
    debug_assert!(
      limits.gc_threshold <= limits.max_bytes,
      "gc_threshold should be <= max_bytes"
    );

    Self {
      limits,
      used_bytes: 0,
      gc_runs: 0,
      slots: Vec::new(),
      marks: Vec::new(),
      free_list: Vec::new(),
      next_symbol_id: 1,
      root_stack: Vec::new(),
      persistent_roots: Vec::new(),
      persistent_roots_free: Vec::new(),
      symbol_registry: BTreeMap::new(),
    }
  }

  /// Enters a stack-rooting scope.
  ///
  /// Stack roots pushed via [`Scope::push_root`] are removed when the returned `Scope` is dropped.
  pub fn scope(&mut self) -> Scope<'_> {
    let root_stack_len_at_entry = self.root_stack.len();
    Scope {
      heap: self,
      root_stack_len_at_entry,
    }
  }

  /// Bytes currently used by live heap allocations.
  pub fn used_bytes(&self) -> usize {
    self.used_bytes
  }

  /// Total number of GC cycles that have run.
  pub fn gc_runs(&self) -> u64 {
    self.gc_runs
  }

  /// Explicitly runs a GC cycle.
  pub fn collect_garbage(&mut self) {
    self.gc_runs += 1;

    // Mark.
    {
      debug_assert_eq!(self.slots.len(), self.marks.len());

      let slots = &self.slots;
      let marks = &mut self.marks[..];

      let mut tracer = Tracer::new(slots, marks);
      for value in &self.root_stack {
        tracer.trace_value(*value);
      }
      for value in self.persistent_roots.iter().flatten() {
        tracer.trace_value(*value);
      }
      for sym in self.symbol_registry.values().copied() {
        tracer.trace_value(Value::Symbol(sym));
      }

      while let Some(id) = tracer.pop_work() {
        let Some(idx) = tracer.validate(id) else {
          continue;
        };
        if tracer.marks[idx] != 0 {
          continue;
        }
        tracer.marks[idx] = 1;

        let Some(obj) = tracer.slots[idx].value.as_ref() else {
          debug_assert!(false, "validated heap id points to a free slot: {id:?}");
          continue;
        };
        obj.trace(&mut tracer);
      }
    }

    // Sweep.
    for (idx, slot) in self.slots.iter_mut().enumerate() {
      let marked = self.marks[idx] != 0;
      // Reset mark bits for next cycle.
      self.marks[idx] = 0;

      if slot.value.is_none() {
        debug_assert!(!marked);
        continue;
      }

      if marked {
        continue;
      }

      // Unreachable: drop the object and free the slot.
      self.used_bytes = self.used_bytes.saturating_sub(slot.bytes);
      slot.value = None;
      slot.bytes = 0;
      slot.generation = slot.generation.wrapping_add(1);
      self.free_list.push(idx as u32);
    }
  }

  /// Adds a persistent root, keeping `value` live until the returned [`RootId`] is removed.
  pub fn add_root(&mut self, value: Value) -> RootId {
    // Root sets should not contain stale handles; detect issues early in debug builds.
    debug_assert!(self.debug_value_is_valid_or_primitive(value));

    let idx = match self.persistent_roots_free.pop() {
      Some(idx) => idx as usize,
      None => {
        self.persistent_roots.push(None);
        self.persistent_roots.len() - 1
      }
    };
    debug_assert!(self.persistent_roots[idx].is_none());
    self.persistent_roots[idx] = Some(value);
    RootId(idx as u32)
  }

  /// Removes a persistent root previously created by [`Heap::add_root`].
  pub fn remove_root(&mut self, id: RootId) {
    let idx = id.0 as usize;
    debug_assert!(idx < self.persistent_roots.len(), "invalid RootId");
    if idx >= self.persistent_roots.len() {
      return;
    }
    debug_assert!(self.persistent_roots[idx].is_some(), "RootId already removed");
    if self.persistent_roots[idx].take().is_some() {
      self.persistent_roots_free.push(id.0);
    }
  }

  /// Returns `true` if `obj` currently points to a live object allocation.
  pub fn is_valid_object(&self, obj: GcObject) -> bool {
    matches!(self.get_heap_object(obj.0), Ok(HeapObject::Object(_)))
  }

  /// Returns `true` if `s` currently points to a live string allocation.
  pub fn is_valid_string(&self, s: GcString) -> bool {
    matches!(self.get_heap_object(s.0), Ok(HeapObject::String(_)))
  }

  /// Returns `true` if `sym` currently points to a live symbol allocation.
  pub fn is_valid_symbol(&self, sym: GcSymbol) -> bool {
    matches!(self.get_heap_object(sym.0), Ok(HeapObject::Symbol(_)))
  }

  /// Gets the string contents for `s`.
  pub fn get_string(&self, s: GcString) -> Result<&JsString, VmError> {
    match self.get_heap_object(s.0)? {
      HeapObject::String(s) => Ok(s),
      _ => Err(VmError::InvalidHandle),
    }
  }

  /// Gets the (optional) description for `sym`.
  pub fn get_symbol_description(&self, sym: GcSymbol) -> Result<Option<GcString>, VmError> {
    match self.get_heap_object(sym.0)? {
      HeapObject::Symbol(sym) => Ok(sym.description()),
      _ => Err(VmError::InvalidHandle),
    }
  }

  /// Convenience: returns the (optional) description for `sym`, treating invalid handles as
  /// "no description".
  pub fn symbol_description(&self, sym: GcSymbol) -> Option<GcString> {
    self.get_symbol_description(sym).ok().flatten()
  }

  /// Returns the debug/introspection id for `sym`.
  pub fn get_symbol_id(&self, sym: GcSymbol) -> Result<u64, VmError> {
    match self.get_heap_object(sym.0)? {
      HeapObject::Symbol(sym) => Ok(sym.id()),
      _ => Err(VmError::InvalidHandle),
    }
  }

  /// Implements `Symbol.for`-like behaviour using a deterministic global registry.
  ///
  /// The registry is scanned by the GC, so registered symbols remain live even if they are not
  /// referenced from the stack or persistent roots.
  pub fn symbol_for(&mut self, key: GcString) -> Result<GcSymbol, VmError> {
    let key_contents = self.get_string(key)?.clone();
    if let Some(sym) = self.symbol_registry.get(&key_contents).copied() {
      return Ok(sym);
    }

    // Root `key` for the duration of allocation in case `ensure_can_allocate` triggers a GC.
    let sym = {
      let mut scope = self.scope();
      scope.push_root(Value::String(key));
      scope.new_symbol(Some(key))?
    };

    self.symbol_registry.insert(key_contents, sym);
    Ok(sym)
  }

  fn get_heap_object(&self, id: HeapId) -> Result<&HeapObject, VmError> {
    let idx = self.validate(id).ok_or(VmError::InvalidHandle)?;
    self.slots[idx]
      .value
      .as_ref()
      .ok_or(VmError::InvalidHandle)
  }

  fn validate(&self, id: HeapId) -> Option<usize> {
    let idx = id.index() as usize;
    let slot = self.slots.get(idx)?;
    if slot.generation != id.generation() {
      return None;
    }
    if slot.value.is_none() {
      return None;
    }
    Some(idx)
  }

  fn ensure_can_allocate(&mut self, new_bytes: usize) -> Result<(), VmError> {
    let after = self.used_bytes.saturating_add(new_bytes);
    if after > self.limits.gc_threshold {
      self.collect_garbage();
    }

    let after = self.used_bytes.saturating_add(new_bytes);
    if after > self.limits.max_bytes {
      return Err(VmError::OutOfMemory);
    }
    Ok(())
  }

  fn alloc_unchecked(&mut self, obj: HeapObject, new_bytes: usize) -> HeapId {
    let idx = match self.free_list.pop() {
      Some(idx) => idx as usize,
      None => {
        let idx = self.slots.len();
        self.slots.push(Slot::new());
        self.marks.push(0);
        idx
      }
    };

    let slot = &mut self.slots[idx];
    debug_assert!(slot.value.is_none(), "free list returned an occupied slot");

    slot.value = Some(obj);
    slot.bytes = new_bytes;
    self.used_bytes = self.used_bytes.saturating_add(new_bytes);

    HeapId::from_parts(idx as u32, slot.generation)
  }

  fn debug_value_is_valid_or_primitive(&self, value: Value) -> bool {
    match value {
      Value::Undefined | Value::Null | Value::Bool(_) | Value::Number(_) => true,
      Value::String(s) => self.is_valid_string(s),
      Value::Symbol(s) => self.is_valid_symbol(s),
      Value::Object(o) => self.is_valid_object(o),
    }
  }
}

/// A stack-rooting scope.
///
/// All stack roots pushed via [`Scope::push_root`] are removed when the scope is dropped.
pub struct Scope<'a> {
  heap: &'a mut Heap,
  root_stack_len_at_entry: usize,
}

impl Drop for Scope<'_> {
  fn drop(&mut self) {
    self.heap.root_stack.truncate(self.root_stack_len_at_entry);
  }
}

impl<'a> Scope<'a> {
  /// Pushes a stack root.
  ///
  /// The returned `Value` is the same as the input, allowing call sites to write
  /// `let v = scope.push_root(v);` if desired.
  pub fn push_root(&mut self, value: Value) -> Value {
    debug_assert!(self.heap.debug_value_is_valid_or_primitive(value));
    self.heap.root_stack.push(value);
    value
  }

  /// Creates a nested child scope that borrows the same heap.
  pub fn reborrow(&mut self) -> Scope<'_> {
    let root_stack_len_at_entry = self.heap.root_stack.len();
    Scope {
      heap: &mut *self.heap,
      root_stack_len_at_entry,
    }
  }

  /// Borrows the underlying heap immutably.
  pub fn heap(&self) -> &Heap {
    &*self.heap
  }

  /// Borrows the underlying heap mutably.
  pub fn heap_mut(&mut self) -> &mut Heap {
    &mut *self.heap
  }

  /// Allocates a JavaScript string on the heap from UTF-8.
  pub fn alloc_string_from_utf8(&mut self, s: &str) -> Result<GcString, VmError> {
    let units_len = s.encode_utf16().count();
    let new_bytes = JsString::heap_size_bytes_for_len(units_len);
    self.heap.ensure_can_allocate(new_bytes)?;

    // Allocate the backing buffer fallibly so hostile input cannot abort the
    // host process on allocator OOM.
    let mut units: Vec<u16> = Vec::new();
    units
      .try_reserve_exact(units_len)
      .map_err(|_| VmError::OutOfMemory)?;
    units.extend(s.encode_utf16());
    let js = JsString::from_u16_vec(units);
    debug_assert_eq!(new_bytes, js.heap_size_bytes());
    let obj = HeapObject::String(js);
    Ok(GcString(self.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Allocates a JavaScript string on the heap from UTF-16 code units.
  pub fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<GcString, VmError> {
    let new_bytes = JsString::heap_size_bytes_for_len(units.len());
    self.heap.ensure_can_allocate(new_bytes)?;

    // Fallible allocation for the backing buffer (avoid process abort on OOM).
    let mut buf: Vec<u16> = Vec::new();
    buf
      .try_reserve_exact(units.len())
      .map_err(|_| VmError::OutOfMemory)?;
    buf.extend_from_slice(units);

    let js = JsString::from_u16_vec(buf);
    debug_assert_eq!(new_bytes, js.heap_size_bytes());
    let obj = HeapObject::String(js);
    Ok(GcString(self.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Allocates a JavaScript string on the heap from a UTF-16 code unit buffer.
  pub fn alloc_string_from_u16_vec(&mut self, units: Vec<u16>) -> Result<GcString, VmError> {
    let new_bytes = JsString::heap_size_bytes_for_len(units.len());
    self.heap.ensure_can_allocate(new_bytes)?;

    let js = JsString::from_u16_vec(units);
    debug_assert_eq!(new_bytes, js.heap_size_bytes());
    let obj = HeapObject::String(js);
    Ok(GcString(self.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Convenience alias for [`Scope::alloc_string_from_utf8`].
  pub fn alloc_string(&mut self, s: &str) -> Result<GcString, VmError> {
    self.alloc_string_from_utf8(s)
  }

  /// Allocates a JavaScript symbol on the heap.
  pub fn new_symbol(&mut self, description: Option<GcString>) -> Result<GcSymbol, VmError> {
    // Root the description string during allocation in case `ensure_can_allocate` triggers a GC.
    //
    // Note: `description` does not need to remain rooted after allocation; the symbol itself
    // retains a handle and will trace it.
    let mut scope = self.reborrow();
    if let Some(desc) = description {
      scope.push_root(Value::String(desc));
    }

    let new_bytes = mem::size_of::<JsSymbol>();
    scope.heap.ensure_can_allocate(new_bytes)?;

    let id = scope.heap.next_symbol_id;
    scope.heap.next_symbol_id = scope.heap.next_symbol_id.wrapping_add(1);

    let obj = HeapObject::Symbol(JsSymbol::new(id, description));
    Ok(GcSymbol(scope.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Convenience allocation for `Symbol(description)` where `description` is UTF-8.
  pub fn alloc_symbol(&mut self, description: Option<&str>) -> Result<GcSymbol, VmError> {
    let description = match description {
      Some(s) => Some(self.alloc_string(s)?),
      None => None,
    };
    self.new_symbol(description)
  }

  /// Allocates an empty JavaScript object on the heap.
  pub fn alloc_object(&mut self) -> Result<GcObject, VmError> {
    let new_bytes = JsObject::heap_size_bytes_for_descriptor_count(0);
    self.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Object(JsObject::new());
    Ok(GcObject(self.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Allocates a JavaScript object with the provided owned property descriptors.
  pub fn alloc_object_with_descriptors(
    &mut self,
    descriptors: &[PropertyDescriptor],
  ) -> Result<GcObject, VmError> {
    let new_bytes = JsObject::heap_size_bytes_for_descriptor_count(descriptors.len());
    self.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Object(JsObject::from_descriptor_slice(descriptors)?);
    Ok(GcObject(self.heap.alloc_unchecked(obj, new_bytes)))
  }
}

#[derive(Debug)]
struct Slot {
  generation: u32,
  value: Option<HeapObject>,
  bytes: usize,
}

impl Slot {
  fn new() -> Self {
    Self {
      generation: 0,
      value: None,
      bytes: 0,
    }
  }
}

#[derive(Debug)]
enum HeapObject {
  String(JsString),
  Symbol(JsSymbol),
  Object(JsObject),
}

impl Trace for HeapObject {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    match self {
      HeapObject::String(s) => s.trace(tracer),
      HeapObject::Symbol(s) => s.trace(tracer),
      HeapObject::Object(o) => o.trace(tracer),
    }
  }
}

impl Trace for JsString {
  fn trace(&self, _tracer: &mut Tracer<'_>) {
    // Strings have no outgoing GC references.
  }
}

impl Trace for JsSymbol {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(desc) = self.description() {
      tracer.trace_heap_id(desc.0);
    }
  }
}

#[derive(Debug)]
struct JsObject {
  descriptors: Box<[PropertyDescriptor]>,
}

impl JsObject {
  fn new() -> Self {
    Self {
      descriptors: Box::default(),
    }
  }

  fn from_descriptor_slice(descriptors: &[PropertyDescriptor]) -> Result<Self, VmError> {
    // Avoid process abort on allocator OOM: allocate the descriptor buffer fallibly.
    let mut buf: Vec<PropertyDescriptor> = Vec::new();
    buf
      .try_reserve_exact(descriptors.len())
      .map_err(|_| VmError::OutOfMemory)?;
    buf.extend_from_slice(descriptors);

    Ok(Self {
      descriptors: buf.into_boxed_slice(),
    })
  }

  fn heap_size_bytes_for_descriptor_count(count: usize) -> usize {
    let desc_bytes = count
      .checked_mul(mem::size_of::<PropertyDescriptor>())
      .unwrap_or(usize::MAX);
    mem::size_of::<Self>()
      .checked_add(desc_bytes)
      .unwrap_or(usize::MAX)
  }
}

impl Trace for JsObject {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    for desc in self.descriptors.iter() {
      desc.trace(tracer);
    }
  }
}

pub(crate) trait Trace {
  fn trace(&self, tracer: &mut Tracer<'_>);
}

pub(crate) struct Tracer<'a> {
  slots: &'a [Slot],
  marks: &'a mut [u8],
  worklist: Vec<HeapId>,
}

impl<'a> Tracer<'a> {
  fn new(slots: &'a [Slot], marks: &'a mut [u8]) -> Self {
    Self {
      slots,
      marks,
      worklist: Vec::new(),
    }
  }

  fn pop_work(&mut self) -> Option<HeapId> {
    self.worklist.pop()
  }

  pub(crate) fn trace_value(&mut self, value: Value) {
    match value {
      Value::Undefined | Value::Null | Value::Bool(_) | Value::Number(_) => {}
      Value::String(s) => self.trace_heap_id(s.0),
      Value::Symbol(s) => self.trace_heap_id(s.0),
      Value::Object(o) => self.trace_heap_id(o.0),
    }
  }

  fn trace_heap_id(&mut self, id: HeapId) {
    let Some(idx) = self.validate(id) else {
      return;
    };
    if self.marks[idx] != 0 {
      return;
    }
    self.worklist.push(id);
  }

  fn validate(&self, id: HeapId) -> Option<usize> {
    let idx = id.index() as usize;
    let slot = self.slots.get(idx)?;
    if slot.generation != id.generation() {
      debug_assert!(false, "stale handle during GC: {id:?}");
      return None;
    }
    if slot.value.is_none() {
      debug_assert!(false, "handle points at a free slot during GC: {id:?}");
      return None;
    }
    Some(idx)
  }
}
