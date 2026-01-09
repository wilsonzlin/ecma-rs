use crate::env::{EnvBinding, EnvRecord};
use crate::function::{
  CallHandler, ConstructHandler, EcmaFunctionId, JsFunction, NativeConstructId, NativeFunctionId,
  ThisMode,
};
use crate::property::{PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind};
use crate::promise::{PromiseReaction, PromiseState};
use crate::string::JsString;
use crate::symbol::JsSymbol;
use crate::{EnvRootId, GcEnv, GcObject, GcString, GcSymbol, HeapId, RootId, Value, Vm, VmError};
use core::mem;
use std::collections::{BTreeMap, HashSet};

/// Hard upper bound for `[[Prototype]]` chain traversals.
///
/// This is a DoS resistance measure. Even though `object_set_prototype` prevents cycles,
/// embeddings (or unsafe internal helpers) can violate invariants.
pub const MAX_PROTOTYPE_CHAIN: usize = 10_000;

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
  pub(crate) env_root_stack: Vec<GcEnv>,
  persistent_roots: Vec<Option<Value>>,
  persistent_roots_free: Vec<u32>,
  persistent_env_roots: Vec<Option<GcEnv>>,
  persistent_env_roots_free: Vec<u32>,

  // Global symbol registry for `Symbol.for`-like behaviour.
  //
  // The registry is scanned during GC (as an additional root set) to keep
  // interned symbols alive.
  symbol_registry: BTreeMap<JsString, GcSymbol>,
}

/// RAII wrapper for a persistent GC root created by [`Heap::add_root`].
///
/// This is intended for host embeddings that need to keep VM values alive across calls but want to
/// avoid leaking roots on early returns.
///
/// While this guard is alive it holds a mutable borrow of the [`Heap`]. For long-lived roots stored
/// in host state, prefer storing the returned [`RootId`] from [`Heap::add_root`] directly.
pub struct PersistentRoot<'a> {
  heap: &'a mut Heap,
  id: RootId,
}

impl<'a> PersistentRoot<'a> {
  /// Adds `value` to the heap's persistent root set and returns a guard that removes it on drop.
  pub fn new(heap: &'a mut Heap, value: Value) -> Self {
    let id = heap.add_root(value);
    Self { heap, id }
  }

  /// The underlying [`RootId`].
  #[inline]
  pub fn id(&self) -> RootId {
    self.id
  }

  /// Returns the current rooted value.
  #[inline]
  pub fn get(&self) -> Option<Value> {
    self.heap.get_root(self.id)
  }

  /// Updates the rooted value.
  #[inline]
  pub fn set(&mut self, value: Value) {
    self.heap.set_root(self.id, value);
  }

  /// Borrows the underlying heap immutably.
  #[inline]
  pub fn heap(&self) -> &Heap {
    &*self.heap
  }

  /// Borrows the underlying heap mutably.
  #[inline]
  pub fn heap_mut(&mut self) -> &mut Heap {
    &mut *self.heap
  }
}

impl Drop for PersistentRoot<'_> {
  fn drop(&mut self) {
    self.heap.remove_root(self.id);
  }
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
      env_root_stack: Vec::new(),
      persistent_roots: Vec::new(),
      persistent_roots_free: Vec::new(),
      persistent_env_roots: Vec::new(),
      persistent_env_roots_free: Vec::new(),
      symbol_registry: BTreeMap::new(),
    }
  }

  /// Enters a stack-rooting scope.
  ///
  /// Stack roots pushed via [`Scope::push_root`] are removed when the returned `Scope` is dropped.
  pub fn scope(&mut self) -> Scope<'_> {
    let root_stack_len_at_entry = self.root_stack.len();
    let env_root_stack_len_at_entry = self.env_root_stack.len();
    Scope {
      heap: self,
      root_stack_len_at_entry,
      env_root_stack_len_at_entry,
    }
  }

  /// Bytes currently used by live heap allocations.
  pub fn used_bytes(&self) -> usize {
    self.used_bytes
  }

  #[cfg(debug_assertions)]
  fn debug_recompute_used_bytes(&self) -> usize {
    self
      .slots
      .iter()
      .filter(|slot| slot.value.is_some())
      .fold(0usize, |acc, slot| acc.saturating_add(slot.bytes))
  }

  #[cfg(debug_assertions)]
  fn debug_assert_used_bytes_is_correct(&self) {
    let recomputed = self.debug_recompute_used_bytes();
    debug_assert_eq!(
      self.used_bytes, recomputed,
      "Heap::used_bytes mismatch: used_bytes={}, recomputed={}",
      self.used_bytes, recomputed
    );
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
      for env in &self.env_root_stack {
        tracer.trace_env(*env);
      }
      for value in self.persistent_roots.iter().flatten() {
        tracer.trace_value(*value);
      }
      for env in self.persistent_env_roots.iter().flatten() {
        tracer.trace_env(*env);
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

    #[cfg(debug_assertions)]
    self.debug_assert_used_bytes_is_correct();
  }

  /// Adds a persistent root and returns an RAII guard that removes it on drop.
  #[inline]
  pub fn persistent_root(&mut self, value: Value) -> PersistentRoot<'_> {
    PersistentRoot::new(self, value)
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

  /// Returns the current value of a persistent root.
  pub fn get_root(&self, id: RootId) -> Option<Value> {
    self
      .persistent_roots
      .get(id.0 as usize)
      .and_then(|slot| *slot)
  }

  /// Updates a persistent root's value.
  ///
  /// Panics only in debug builds if `id` is invalid.
  pub fn set_root(&mut self, id: RootId, value: Value) {
    // Root sets should not contain stale handles; detect issues early in debug builds.
    debug_assert!(self.debug_value_is_valid_or_primitive(value));

    let idx = id.0 as usize;
    debug_assert!(idx < self.persistent_roots.len(), "invalid RootId");
    if idx >= self.persistent_roots.len() {
      return;
    }
    debug_assert!(
      self.persistent_roots[idx].is_some(),
      "RootId already removed"
    );
    if self.persistent_roots[idx].is_some() {
      self.persistent_roots[idx] = Some(value);
    }
  }

  /// Removes a persistent root previously created by [`Heap::add_root`].
  pub fn remove_root(&mut self, id: RootId) {
    let idx = id.0 as usize;
    debug_assert!(idx < self.persistent_roots.len(), "invalid RootId");
    if idx >= self.persistent_roots.len() {
      return;
    }
    debug_assert!(
      self.persistent_roots[idx].is_some(),
      "RootId already removed"
    );
    if self.persistent_roots[idx].take().is_some() {
      self.persistent_roots_free.push(id.0);
    }
  }

  pub(crate) fn add_env_root(&mut self, env: GcEnv) -> EnvRootId {
    debug_assert!(self.is_valid_env(env));

    let idx = match self.persistent_env_roots_free.pop() {
      Some(idx) => idx as usize,
      None => {
        self.persistent_env_roots.push(None);
        self.persistent_env_roots.len() - 1
      }
    };
    debug_assert!(self.persistent_env_roots[idx].is_none());
    self.persistent_env_roots[idx] = Some(env);
    EnvRootId(idx as u32)
  }

  #[allow(dead_code)]
  pub(crate) fn get_env_root(&self, id: EnvRootId) -> Option<GcEnv> {
    self
      .persistent_env_roots
      .get(id.0 as usize)
      .and_then(|slot| *slot)
  }

  pub(crate) fn set_env_root(&mut self, id: EnvRootId, env: GcEnv) {
    debug_assert!(self.is_valid_env(env));

    let idx = id.0 as usize;
    debug_assert!(
      idx < self.persistent_env_roots.len(),
      "invalid EnvRootId"
    );
    if idx >= self.persistent_env_roots.len() {
      return;
    }
    debug_assert!(
      self.persistent_env_roots[idx].is_some(),
      "EnvRootId already removed"
    );
    if self.persistent_env_roots[idx].is_some() {
      self.persistent_env_roots[idx] = Some(env);
    }
  }

  #[allow(dead_code)]
  pub(crate) fn remove_env_root(&mut self, id: EnvRootId) {
    let idx = id.0 as usize;
    debug_assert!(
      idx < self.persistent_env_roots.len(),
      "invalid EnvRootId"
    );
    if idx >= self.persistent_env_roots.len() {
      return;
    }
    debug_assert!(
      self.persistent_env_roots[idx].is_some(),
      "EnvRootId already removed"
    );
    if self.persistent_env_roots[idx].take().is_some() {
      self.persistent_env_roots_free.push(id.0);
    }
  }

  /// Returns `true` if `obj` currently points to a live object allocation.
  pub fn is_valid_object(&self, obj: GcObject) -> bool {
    matches!(
      self.get_heap_object(obj.0),
      Ok(HeapObject::Object(_) | HeapObject::Function(_) | HeapObject::Promise(_))
    )
  }

  /// Returns `true` if `obj` currently points to a live Promise object allocation.
  ///
  /// This is the spec-shaped "brand check" used by `IsPromise`: an object is a Promise if it has
  /// Promise internal slots (represented here by the `HeapObject::Promise` variant).
  pub fn is_promise_object(&self, obj: GcObject) -> bool {
    matches!(self.get_heap_object(obj.0), Ok(HeapObject::Promise(_)))
  }

  /// Returns `true` if `s` currently points to a live string allocation.
  pub fn is_valid_string(&self, s: GcString) -> bool {
    matches!(self.get_heap_object(s.0), Ok(HeapObject::String(_)))
  }

  /// Returns `true` if `sym` currently points to a live symbol allocation.
  pub fn is_valid_symbol(&self, sym: GcSymbol) -> bool {
    matches!(self.get_heap_object(sym.0), Ok(HeapObject::Symbol(_)))
  }

  pub fn is_valid_env(&self, env: GcEnv) -> bool {
    matches!(self.get_heap_object(env.0), Ok(HeapObject::Env(_)))
  }

  /// Returns `true` if `value` is callable (i.e. has an ECMAScript `[[Call]]` internal method).
  pub fn is_callable(&self, value: Value) -> Result<bool, VmError> {
    match value {
      Value::Object(obj) => match self.get_heap_object(obj.0)? {
        HeapObject::Function(_) => Ok(true),
        _ => Ok(false),
      },
      _ => Ok(false),
    }
  }

  /// Returns `true` if `value` is a constructor (i.e. has an ECMAScript `[[Construct]]` internal
  /// method).
  pub fn is_constructor(&self, value: Value) -> Result<bool, VmError> {
    match value {
      Value::Object(obj) => match self.get_heap_object(obj.0)? {
        HeapObject::Function(f) => Ok(f.construct.is_some()),
        _ => Ok(false),
      },
      _ => Ok(false),
    }
  }

  /// Calls `callee` with the provided `this` value and arguments.
  ///
  /// This is a convenience wrapper around [`Vm::call`] for host embeddings: it creates a temporary
  /// stack-rooting [`Scope`] to keep `callee`, `this`, and `args` alive for the duration of the
  /// call.
  ///
  /// Invalid handles are rejected up-front with [`VmError::InvalidHandle`] (rather than tripping
  /// debug assertions when rooting).
  pub fn call(
    &mut self,
    vm: &mut Vm,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    if !self.debug_value_is_valid_or_primitive(callee) {
      return Err(VmError::InvalidHandle);
    }
    if !self.debug_value_is_valid_or_primitive(this) {
      return Err(VmError::InvalidHandle);
    }
    for &arg in args {
      if !self.debug_value_is_valid_or_primitive(arg) {
        return Err(VmError::InvalidHandle);
      }
    }

    let mut scope = self.scope();
    vm.call(&mut scope, callee, this, args)
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

  fn get_object_base(&self, obj: GcObject) -> Result<&ObjectBase, VmError> {
    match self.get_heap_object(obj.0)? {
      HeapObject::Object(o) => Ok(&o.base),
      HeapObject::Function(f) => Ok(&f.base),
      HeapObject::Promise(p) => Ok(&p.object.base),
      _ => Err(VmError::InvalidHandle),
    }
  }

  fn get_object_base_mut(&mut self, obj: GcObject) -> Result<&mut ObjectBase, VmError> {
    match self.get_heap_object_mut(obj.0)? {
      HeapObject::Object(o) => Ok(&mut o.base),
      HeapObject::Function(f) => Ok(&mut f.base),
      HeapObject::Promise(p) => Ok(&mut p.object.base),
      _ => Err(VmError::InvalidHandle),
    }
  }
  fn get_env(&self, env: GcEnv) -> Result<&EnvRecord, VmError> {
    match self.get_heap_object(env.0)? {
      HeapObject::Env(e) => Ok(e),
      _ => Err(VmError::InvalidHandle),
    }
  }

  fn get_env_mut(&mut self, env: GcEnv) -> Result<&mut EnvRecord, VmError> {
    match self.get_heap_object_mut(env.0)? {
      HeapObject::Env(e) => Ok(e),
      _ => Err(VmError::InvalidHandle),
    }
  }
  /// Gets an object's `[[Prototype]]`.
  pub fn object_prototype(&self, obj: GcObject) -> Result<Option<GcObject>, VmError> {
    Ok(self.get_object_base(obj)?.prototype)
  }

  /// Sets an object's `[[Prototype]]`.
  pub fn object_set_prototype(
    &mut self,
    obj: GcObject,
    prototype: Option<GcObject>,
  ) -> Result<(), VmError> {
    // Validate `obj` early so we don't silently accept stale handles.
    let _ = self.get_object_base(obj)?;

    // Direct self-cycle.
    if prototype == Some(obj) {
      return Err(VmError::PrototypeCycle);
    }

    // Reject indirect cycles by walking `prototype`'s chain and checking whether it contains `obj`.
    //
    // Also guard against hostile chains (very deep or cyclic) even if an invariant was violated.
    let mut current = prototype;
    let mut steps = 0usize;
    let mut visited: HashSet<GcObject> = HashSet::new();
    while let Some(p) = current {
      if steps >= MAX_PROTOTYPE_CHAIN {
        return Err(VmError::PrototypeChainTooDeep);
      }
      steps += 1;

      if !visited.insert(p) {
        return Err(VmError::PrototypeCycle);
      }
      if p == obj {
        return Err(VmError::PrototypeCycle);
      }

      current = self.object_prototype(p)?;
    }

    self.get_object_base_mut(obj)?.prototype = prototype;
    Ok(())
  }

  /// Forcefully sets an object's `[[Prototype]]` without cycle checks.
  ///
  /// # Safety
  ///
  /// This can violate VM invariants (create prototype cycles, etc). Intended for low-level host
  /// embeddings and tests.
  pub unsafe fn object_set_prototype_unchecked(
    &mut self,
    obj: GcObject,
    prototype: Option<GcObject>,
  ) -> Result<(), VmError> {
    self.get_object_base_mut(obj)?.prototype = prototype;
    Ok(())
  }

  pub(crate) fn object_is_extensible(&self, obj: GcObject) -> Result<bool, VmError> {
    Ok(self.get_object_base(obj)?.extensible)
  }

  pub(crate) fn object_set_extensible(
    &mut self,
    obj: GcObject,
    extensible: bool,
  ) -> Result<(), VmError> {
    self.get_object_base_mut(obj)?.extensible = extensible;
    Ok(())
  }

  /// Gets an own property descriptor from an object.
  pub fn object_get_own_property(
    &self,
    obj: GcObject,
    key: &PropertyKey,
  ) -> Result<Option<PropertyDescriptor>, VmError> {
    let obj = self.get_object_base(obj)?;
    for prop in obj.properties.iter() {
      if self.property_key_eq(&prop.key, key) {
        return Ok(Some(prop.desc));
      }
    }
    Ok(None)
  }

  pub(crate) fn object_delete_own_property(
    &mut self,
    obj: GcObject,
    key: &PropertyKey,
  ) -> Result<bool, VmError> {
    let slot_idx = self.validate(obj.0).ok_or(VmError::InvalidHandle)?;

    // Two-phase borrow to avoid holding `&mut HeapObject` while calling back into `&self` for
    // string comparisons in `property_key_eq`.
    let (idx, is_function, bound_args_len, property_count) = {
      let slot = &self.slots[slot_idx];
      let Some(obj) = slot.value.as_ref() else {
        return Err(VmError::InvalidHandle);
      };
      match obj {
        HeapObject::Object(obj) => (
          obj
            .base
            .properties
            .iter()
            .position(|prop| self.property_key_eq(&prop.key, key)),
          false,
          0usize,
          obj.base.properties.len(),
        ),
        HeapObject::Function(func) => (
          func
            .base
            .properties
            .iter()
            .position(|prop| self.property_key_eq(&prop.key, key)),
          true,
          func.bound_args.as_ref().map(|args| args.len()).unwrap_or(0),
          func.base.properties.len(),
        ),
        _ => return Err(VmError::InvalidHandle),
      }
    };

    let Some(idx) = idx else {
      return Ok(false);
    };

    let new_property_count = property_count.saturating_sub(1);
    let new_bytes = if is_function {
      JsFunction::heap_size_bytes_for_bound_args_len_and_property_count(
        bound_args_len,
        new_property_count,
      )
    } else {
      JsObject::heap_size_bytes_for_property_count(new_property_count)
    };

    // Allocate the new property table fallibly so hostile inputs cannot abort the host process
    // on allocator OOM (even though this is a net-shrinking operation).
    let mut buf: Vec<PropertyEntry> = Vec::new();
    buf
      .try_reserve_exact(new_property_count)
      .map_err(|_| VmError::OutOfMemory)?;

    {
      let slot = &self.slots[slot_idx];
      match slot.value.as_ref() {
        Some(HeapObject::Object(obj)) => {
          buf.extend_from_slice(&obj.base.properties[..idx]);
          buf.extend_from_slice(&obj.base.properties[idx + 1..]);
        }
        Some(HeapObject::Function(func)) => {
          buf.extend_from_slice(&func.base.properties[..idx]);
          buf.extend_from_slice(&func.base.properties[idx + 1..]);
        }
        _ => return Err(VmError::InvalidHandle),
      }
    }

    let properties = buf.into_boxed_slice();
    let Some(obj) = self.slots[slot_idx].value.as_mut() else {
      return Err(VmError::InvalidHandle);
    };
    match obj {
      HeapObject::Object(obj) => obj.base.properties = properties,
      HeapObject::Function(func) => func.base.properties = properties,
      _ => return Err(VmError::InvalidHandle),
    }

    // This is a net-shrinking operation, so no `ensure_can_allocate` call is needed.
    self.update_slot_bytes(slot_idx, new_bytes);

    #[cfg(debug_assertions)]
    self.debug_assert_used_bytes_is_correct();

    Ok(true)
  }

  /// Convenience: returns the value of an own data property, if present.
  pub fn object_get_own_data_property_value(
    &self,
    obj: GcObject,
    key: &PropertyKey,
  ) -> Result<Option<Value>, VmError> {
    let Some(desc) = self.object_get_own_property(obj, key)? else {
      return Ok(None);
    };
    match desc.kind {
      PropertyKind::Data { value, .. } => Ok(Some(value)),
      PropertyKind::Accessor { .. } => Err(VmError::PropertyNotData),
    }
  }

  /// Updates the `value` of an existing own data property.
  pub fn object_set_existing_data_property_value(
    &mut self,
    obj: GcObject,
    key: &PropertyKey,
    value: Value,
  ) -> Result<(), VmError> {
    // Two-phase borrow to avoid holding `&mut ObjectBase` while calling back into `&self` for
    // string comparisons in `property_key_eq`.
    let idx = {
      let obj = self.get_object_base(obj)?;
      obj
        .properties
        .iter()
        .position(|prop| self.property_key_eq(&prop.key, key))
    };

    let Some(idx) = idx else {
      return Err(VmError::PropertyNotFound);
    };

    let obj = self.get_object_base_mut(obj)?;
    let prop = obj
      .properties
      .get_mut(idx)
      .ok_or(VmError::PropertyNotFound)?;
    match &mut prop.desc.kind {
      PropertyKind::Data { value: slot, .. } => {
        *slot = value;
        Ok(())
      }
      PropertyKind::Accessor { .. } => Err(VmError::PropertyNotData),
    }
  }

  pub fn define_own_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<bool, VmError> {
    let mut scope = self.scope();
    scope.ordinary_define_own_property(obj, key, desc)
  }

  pub fn define_own_property_or_throw(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<(), VmError> {
    let ok = self.define_own_property(obj, key, desc)?;
    if ok {
      Ok(())
    } else {
      Err(VmError::TypeError("DefineOwnProperty rejected"))
    }
  }

  /// ECMAScript `DefinePropertyOrThrow`.
  ///
  /// This is a convenience wrapper around [`Heap::define_own_property`]. If the definition is
  /// rejected (`false`), this returns a `TypeError`.
  pub fn define_property_or_throw(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<(), VmError> {
    self.define_own_property_or_throw(obj, key, desc)
  }

  pub fn create_data_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
  ) -> Result<bool, VmError> {
    let mut scope = self.scope();
    scope.create_data_property(obj, key, value)
  }

  pub fn create_data_property_or_throw(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
  ) -> Result<(), VmError> {
    let ok = self.create_data_property(obj, key, value)?;
    if ok {
      Ok(())
    } else {
      Err(VmError::TypeError("CreateDataProperty rejected"))
    }
  }

  /// Gets a property descriptor from `obj` or its prototype chain.
  pub fn get_property(
    &self,
    obj: GcObject,
    key: &PropertyKey,
  ) -> Result<Option<PropertyDescriptor>, VmError> {
    let mut current = Some(obj);
    let mut steps = 0usize;
    let mut visited: HashSet<GcObject> = HashSet::new();

    while let Some(obj) = current {
      if steps >= MAX_PROTOTYPE_CHAIN {
        return Err(VmError::PrototypeChainTooDeep);
      }
      steps += 1;

      if !visited.insert(obj) {
        return Err(VmError::PrototypeCycle);
      }

      if let Some(desc) = self.object_get_own_property(obj, key)? {
        return Ok(Some(desc));
      }

      current = self.object_prototype(obj)?;
    }

    Ok(None)
  }

  /// Returns whether a property exists on `obj` or its prototype chain.
  pub fn has_property(&self, obj: GcObject, key: &PropertyKey) -> Result<bool, VmError> {
    Ok(self.get_property(obj, key)?.is_some())
  }

  /// Implements a minimal `[[Get]]` internal method for objects.
  ///
  /// This is currently limited to data properties (sufficient for WebIDL sequence/record
  /// conversions and early scaffolding). Accessor properties return
  /// [`VmError::Unimplemented`], except that an accessor with an `undefined` getter returns
  /// `undefined`.
  pub fn get(&self, obj: GcObject, key: &PropertyKey) -> Result<Value, VmError> {
    let Some(desc) = self.get_property(obj, key)? else {
      return Ok(Value::Undefined);
    };
    match desc.kind {
      PropertyKind::Data { value, .. } => Ok(value),
      PropertyKind::Accessor { get, .. } => {
        if matches!(get, Value::Undefined) {
          Ok(Value::Undefined)
        } else {
          Err(VmError::Unimplemented(
            "Heap::get accessor properties require a VM to call getters",
          ))
        }
      }
    }
  }

  /// Implements the `OwnPropertyKeys` internal method (ECMA-262) for ordinary objects.
  ///
  /// This orders keys as:
  /// 1. array index keys, in ascending numeric order,
  /// 2. other string keys, in insertion order,
  /// 3. symbol keys, in insertion order.
  pub fn own_property_keys(&self, obj: GcObject) -> Result<Vec<PropertyKey>, VmError> {
    let props = &self.get_object_base(obj)?.properties;

    let mut array_keys: Vec<(u32, PropertyKey)> = Vec::new();
    let mut string_keys: Vec<PropertyKey> = Vec::new();
    let mut symbol_keys: Vec<PropertyKey> = Vec::new();

    for prop in props.iter() {
      match prop.key {
        PropertyKey::String(s) => {
          if let Some(idx) = self.string_to_array_index(s) {
            array_keys.push((idx, prop.key));
          } else {
            string_keys.push(prop.key);
          }
        }
        PropertyKey::Symbol(_) => symbol_keys.push(prop.key),
      }
    }

    array_keys.sort_by_key(|(idx, _)| *idx);

    let mut out = Vec::with_capacity(array_keys.len() + string_keys.len() + symbol_keys.len());
    out.extend(array_keys.into_iter().map(|(_, k)| k));
    out.extend(string_keys);
    out.extend(symbol_keys);
    Ok(out)
  }

  fn string_to_array_index(&self, s: GcString) -> Option<u32> {
    let js = self.get_string(s).ok()?;
    let units = js.as_code_units();
    if units.is_empty() {
      return None;
    }
    if units.len() > 1 && units[0] == b'0' as u16 {
      return None;
    }
    let mut n: u64 = 0;
    for &u in units {
      if !(b'0' as u16..=b'9' as u16).contains(&u) {
        return None;
      }
      n = n.checked_mul(10)?;
      n = n.checked_add((u - b'0' as u16) as u64)?;
      if n > u32::MAX as u64 {
        return None;
      }
    }
    // Array index is uint32 < 2^32 - 1.
    if n == u32::MAX as u64 {
      return None;
    }
    Some(n as u32)
  }

  fn get_promise(&self, promise: GcObject) -> Result<&JsPromise, VmError> {
    match self.get_heap_object(promise.0)? {
      HeapObject::Promise(p) => Ok(p),
      _ => Err(VmError::InvalidHandle),
    }
  }

  fn get_promise_mut(&mut self, promise: GcObject) -> Result<&mut JsPromise, VmError> {
    match self.get_heap_object_mut(promise.0)? {
      HeapObject::Promise(p) => Ok(p),
      _ => Err(VmError::InvalidHandle),
    }
  }

  /// Returns `promise.[[PromiseState]]`.
  pub fn promise_state(&self, promise: GcObject) -> Result<PromiseState, VmError> {
    Ok(self.get_promise(promise)?.state)
  }

  /// Returns `promise.[[PromiseResult]]`.
  pub fn promise_result(&self, promise: GcObject) -> Result<Value, VmError> {
    Ok(self.get_promise(promise)?.result)
  }

  /// Returns `promise.[[PromiseIsHandled]]`.
  pub fn promise_is_handled(&self, promise: GcObject) -> Result<bool, VmError> {
    Ok(self.get_promise(promise)?.is_handled)
  }

  /// Sets `promise.[[PromiseIsHandled]]`.
  pub fn promise_set_is_handled(&mut self, promise: GcObject, handled: bool) -> Result<(), VmError> {
    self.get_promise_mut(promise)?.is_handled = handled;
    Ok(())
  }

  /// Returns the length of `promise.[[PromiseFulfillReactions]]`.
  pub fn promise_fulfill_reactions_len(&self, promise: GcObject) -> Result<usize, VmError> {
    Ok(self.get_promise(promise)?.fulfill_reactions.len())
  }

  /// Returns the length of `promise.[[PromiseRejectReactions]]`.
  pub fn promise_reject_reactions_len(&self, promise: GcObject) -> Result<usize, VmError> {
    Ok(self.get_promise(promise)?.reject_reactions.len())
  }

  /// Sets `promise.[[PromiseState]]` and `promise.[[PromiseResult]]`.
  ///
  /// If `state` is not [`PromiseState::Pending`], this is a settlement operation and the Promise's
  /// reaction lists are cleared as required by ECMA-262.
  pub fn promise_set_state_and_result(
    &mut self,
    promise: GcObject,
    state: PromiseState,
    result: Value,
  ) -> Result<(), VmError> {
    let idx = self.validate(promise.0).ok_or(VmError::InvalidHandle)?;

    let new_bytes = {
      let promise = match self.slots[idx].value.as_mut() {
        Some(HeapObject::Promise(p)) => p,
        _ => return Err(VmError::InvalidHandle),
      };

      promise.state = state;
      promise.result = result;

      if state != PromiseState::Pending {
        promise.fulfill_reactions = Box::default();
        promise.reject_reactions = Box::default();
      }

      promise.heap_size_bytes()
    };

    self.update_slot_bytes(idx, new_bytes);
    #[cfg(debug_assertions)]
    self.debug_assert_used_bytes_is_correct();
    Ok(())
  }

  /// Settles a pending Promise as fulfilled.
  pub fn promise_fulfill(&mut self, promise: GcObject, value: Value) -> Result<(), VmError> {
    self.promise_set_state_and_result(promise, PromiseState::Fulfilled, value)
  }

  /// Settles a pending Promise as rejected.
  pub fn promise_reject(&mut self, promise: GcObject, reason: Value) -> Result<(), VmError> {
    self.promise_set_state_and_result(promise, PromiseState::Rejected, reason)
  }

  fn promise_append_reaction(
    &mut self,
    promise: GcObject,
    is_fulfill_list: bool,
    reaction: PromiseReaction,
  ) -> Result<(), VmError> {
    let idx = self.validate(promise.0).ok_or(VmError::InvalidHandle)?;

    let (property_count, fulfill_count, reject_count, old_bytes, state) = {
      let slot = &self.slots[idx];
      let Some(obj) = slot.value.as_ref() else {
        return Err(VmError::InvalidHandle);
      };
      let HeapObject::Promise(p) = obj else {
        return Err(VmError::InvalidHandle);
      };
      (
        p.object.base.properties.len(),
        p.fulfill_reactions.len(),
        p.reject_reactions.len(),
        slot.bytes,
        p.state,
      )
    };

    if state != PromiseState::Pending {
      return Err(VmError::InvalidHandle);
    }

    let new_fulfill_count = if is_fulfill_list {
      fulfill_count.checked_add(1).ok_or(VmError::OutOfMemory)?
    } else {
      fulfill_count
    };
    let new_reject_count = if is_fulfill_list {
      reject_count
    } else {
      reject_count.checked_add(1).ok_or(VmError::OutOfMemory)?
    };

    let new_bytes =
      JsPromise::heap_size_bytes_for_counts(property_count, new_fulfill_count, new_reject_count);

    // Before allocating, enforce heap limits based on the net growth of this object.
    let grow_by = new_bytes.saturating_sub(old_bytes);
    self.ensure_can_allocate(grow_by)?;

    // Allocate the new reaction list fallibly so hostile inputs cannot abort the host process on
    // allocator OOM.
    let new_list_len = if is_fulfill_list {
      new_fulfill_count
    } else {
      new_reject_count
    };

    let mut buf: Vec<PromiseReaction> = Vec::new();
    buf
      .try_reserve_exact(new_list_len)
      .map_err(|_| VmError::OutOfMemory)?;

    {
      let slot = &self.slots[idx];
      let Some(HeapObject::Promise(p)) = slot.value.as_ref() else {
        return Err(VmError::InvalidHandle);
      };
      if is_fulfill_list {
        buf.extend_from_slice(&p.fulfill_reactions);
      } else {
        buf.extend_from_slice(&p.reject_reactions);
      }
    }

    buf.push(reaction);
    let new_list = buf.into_boxed_slice();

    {
      let promise = match self.slots[idx].value.as_mut() {
        Some(HeapObject::Promise(p)) => p,
        _ => return Err(VmError::InvalidHandle),
      };
      if is_fulfill_list {
        promise.fulfill_reactions = new_list;
      } else {
        promise.reject_reactions = new_list;
      }
    }

    self.update_slot_bytes(idx, new_bytes);
    #[cfg(debug_assertions)]
    self.debug_assert_used_bytes_is_correct();
    Ok(())
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

  /// Gets an object's own property descriptor.
  ///
  /// This does not currently walk the prototype chain.
  pub fn get_own_property(
    &self,
    obj: GcObject,
    key: PropertyKey,
  ) -> Result<Option<PropertyDescriptor>, VmError> {
    self.object_get_own_property(obj, &key)
  }

  /// ECMAScript `OrdinaryDelete` / `[[Delete]]` for ordinary objects.
  ///
  /// Spec: https://tc39.es/ecma262/#sec-ordinarydelete
  pub fn ordinary_delete(&mut self, obj: GcObject, key: PropertyKey) -> Result<bool, VmError> {
    let Some(current) = self.get_own_property(obj, key)? else {
      return Ok(true);
    };

    if !current.configurable {
      return Ok(false);
    }

    let _deleted = self.object_delete_own_property(obj, &key)?;
    Ok(true)
  }

  /// ECMAScript `OrdinaryOwnPropertyKeys` / `[[OwnPropertyKeys]]` for ordinary objects.
  ///
  /// Spec: https://tc39.es/ecma262/#sec-ordinaryownpropertykeys
  pub fn ordinary_own_property_keys(&self, obj: GcObject) -> Result<Vec<PropertyKey>, VmError> {
    let properties = &self.get_object_base(obj)?.properties;

    let property_count = properties.len();

    // 1. Array indices (String keys that are array indices) in ascending numeric order.
    let mut index_keys: Vec<(u32, PropertyKey)> = Vec::new();
    index_keys
      .try_reserve_exact(property_count)
      .map_err(|_| VmError::OutOfMemory)?;
    for prop in properties.iter() {
      if matches!(prop.key, PropertyKey::String(_)) {
        if let Some(idx) = self.array_index(&prop.key) {
          index_keys.push((idx, prop.key));
        }
      }
    }
    index_keys.sort_by_key(|(idx, _)| *idx);

    // 2. String keys that are not array indices, in chronological creation order.
    // 3. Symbol keys, in chronological creation order.
    let mut out: Vec<PropertyKey> = Vec::new();
    out
      .try_reserve_exact(property_count)
      .map_err(|_| VmError::OutOfMemory)?;

    for (_, key) in index_keys.iter() {
      out.push(*key);
    }

    for prop in properties.iter() {
      let PropertyKey::String(_) = prop.key else {
        continue;
      };
      if self.array_index(&prop.key).is_none() {
        out.push(prop.key);
      }
    }

    for prop in properties.iter() {
      if matches!(prop.key, PropertyKey::Symbol(_)) {
        out.push(prop.key);
      }
    }

    Ok(out)
  }

  pub(crate) fn set_function_name_metadata(
    &mut self,
    func: GcObject,
    name: GcString,
  ) -> Result<(), VmError> {
    let idx = self.validate(func.0).ok_or(VmError::InvalidHandle)?;
    let Some(obj) = self.slots[idx].value.as_mut() else {
      return Err(VmError::InvalidHandle);
    };
    let HeapObject::Function(func) = obj else {
      return Err(VmError::InvalidHandle);
    };
    func.name = name;
    Ok(())
  }

  pub(crate) fn set_function_length_metadata(
    &mut self,
    func: GcObject,
    length: u32,
  ) -> Result<(), VmError> {
    let idx = self.validate(func.0).ok_or(VmError::InvalidHandle)?;
    let Some(obj) = self.slots[idx].value.as_mut() else {
      return Err(VmError::InvalidHandle);
    };
    let HeapObject::Function(func) = obj else {
      return Err(VmError::InvalidHandle);
    };
    func.length = length;
    Ok(())
  }

  pub(crate) fn env_outer(&self, env: GcEnv) -> Result<Option<GcEnv>, VmError> {
    Ok(self.get_env(env)?.outer)
  }

  pub(crate) fn env_has_binding(&self, env: GcEnv, name: &str) -> Result<bool, VmError> {
    Ok(self.get_env(env)?.find_binding_index(self, name)?.is_some())
  }

  pub(crate) fn env_initialize_binding(
    &mut self,
    env: GcEnv,
    name: &str,
    value: Value,
  ) -> Result<(), VmError> {
    debug_assert!(self.debug_value_is_valid_or_primitive(value));

    let idx = {
      let rec = self.get_env(env)?;
      rec
        .find_binding_index(self, name)?
        .ok_or(VmError::Unimplemented("unbound identifier"))?
    };

    let rec = self.get_env_mut(env)?;
    let binding = rec
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

  pub(crate) fn env_get_binding_value(
    &self,
    env: GcEnv,
    name: &str,
    _strict: bool,
  ) -> Result<Value, VmError> {
    let rec = self.get_env(env)?;
    let Some(idx) = rec.find_binding_index(self, name)? else {
      return Err(VmError::Unimplemented("unbound identifier"));
    };
    let binding = rec.bindings.get(idx).ok_or(VmError::Unimplemented(
      "environment record binding index out of bounds",
    ))?;
    if !binding.initialized {
      // TDZ.
      return Err(VmError::Throw(Value::Undefined));
    }
    Ok(binding.value)
  }

  pub(crate) fn env_set_mutable_binding(
    &mut self,
    env: GcEnv,
    name: &str,
    value: Value,
    _strict: bool,
  ) -> Result<(), VmError> {
    debug_assert!(self.debug_value_is_valid_or_primitive(value));

    let idx = {
      let rec = self.get_env(env)?;
      rec
        .find_binding_index(self, name)?
        .ok_or(VmError::Unimplemented("unbound identifier"))?
    };

    let rec = self.get_env_mut(env)?;
    let binding = rec
      .bindings
      .get_mut(idx)
      .ok_or(VmError::Unimplemented(
        "environment record binding index out of bounds",
      ))?;

    if !binding.initialized {
      // TDZ.
      return Err(VmError::Throw(Value::Undefined));
    }

    if !binding.mutable {
      // Assignment to const.
      return Err(VmError::Throw(Value::Undefined));
    }

    binding.value = value;
    Ok(())
  }

  fn env_add_binding(&mut self, env: GcEnv, binding: EnvBinding) -> Result<(), VmError> {
    let idx = self.validate(env.0).ok_or(VmError::InvalidHandle)?;

    let (binding_count, old_bytes) = {
      let slot = &self.slots[idx];
      let Some(HeapObject::Env(env)) = slot.value.as_ref() else {
        return Err(VmError::InvalidHandle);
      };
      (env.bindings.len(), slot.bytes)
    };

    let new_binding_count = binding_count.checked_add(1).ok_or(VmError::OutOfMemory)?;
    let new_bytes = EnvRecord::heap_size_bytes_for_binding_count(new_binding_count);

    // Before allocating, enforce heap limits based on the net growth of this environment record.
    let grow_by = new_bytes.saturating_sub(old_bytes);
    self.ensure_can_allocate(grow_by)?;

    // Allocate the new binding table fallibly so hostile inputs cannot abort the host process
    // on allocator OOM.
    let mut buf: Vec<EnvBinding> = Vec::new();
    buf
      .try_reserve_exact(new_binding_count)
      .map_err(|_| VmError::OutOfMemory)?;

    {
      let slot = &self.slots[idx];
      let Some(HeapObject::Env(env)) = slot.value.as_ref() else {
        return Err(VmError::InvalidHandle);
      };
      buf.extend_from_slice(&env.bindings);
    }

    buf.push(binding);
    let bindings = buf.into_boxed_slice();

    let Some(HeapObject::Env(env)) = self.slots[idx].value.as_mut() else {
      return Err(VmError::InvalidHandle);
    };
    env.bindings = bindings;

    self.update_slot_bytes(idx, new_bytes);

    #[cfg(debug_assertions)]
    self.debug_assert_used_bytes_is_correct();
    Ok(())
  }

  fn define_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptor,
  ) -> Result<(), VmError> {
    let idx = self.validate(obj.0).ok_or(VmError::InvalidHandle)?;

    #[derive(Clone, Copy)]
    enum TargetKind {
      OrdinaryObject,
      Function { bound_args_len: usize },
      Promise {
        fulfill_reaction_count: usize,
        reject_reaction_count: usize,
      },
    }

    let (target_kind, property_count, old_bytes, existing_idx) = {
      let slot = &self.slots[idx];
      let Some(obj) = slot.value.as_ref() else {
        return Err(VmError::InvalidHandle);
      };
      match obj {
        HeapObject::Object(obj) => {
          let existing_idx = obj
            .base
            .properties
            .iter()
            .position(|entry| self.property_key_eq(&entry.key, &key));
          (
            TargetKind::OrdinaryObject,
            obj.base.properties.len(),
            slot.bytes,
            existing_idx,
          )
        }
        HeapObject::Function(func) => {
          let existing_idx = func
            .base
            .properties
            .iter()
            .position(|entry| self.property_key_eq(&entry.key, &key));
          let bound_args_len = func.bound_args.as_ref().map(|args| args.len()).unwrap_or(0);
          (
            TargetKind::Function { bound_args_len },
            func.base.properties.len(),
            slot.bytes,
            existing_idx,
          )
        }
        HeapObject::Promise(p) => {
          let existing_idx = p
            .object
            .base
            .properties
            .iter()
            .position(|entry| self.property_key_eq(&entry.key, &key));
          (
            TargetKind::Promise {
              fulfill_reaction_count: p.fulfill_reactions.len(),
              reject_reaction_count: p.reject_reactions.len(),
            },
            p.object.base.properties.len(),
            slot.bytes,
            existing_idx,
          )
        }
        _ => return Err(VmError::InvalidHandle),
      }
    };

    match existing_idx {
      Some(existing_idx) => {
        // Replace in-place (no change to heap size).
        match self.slots[idx].value.as_mut() {
          Some(HeapObject::Object(obj)) => obj.base.properties[existing_idx].desc = desc,
          Some(HeapObject::Function(func)) => func.base.properties[existing_idx].desc = desc,
          Some(HeapObject::Promise(p)) => p.object.base.properties[existing_idx].desc = desc,
          _ => return Err(VmError::InvalidHandle),
        }
        Ok(())
      }
      None => {
        let new_property_count = property_count
          .checked_add(1)
          .ok_or(VmError::OutOfMemory)?;
        let new_bytes = match target_kind {
          TargetKind::OrdinaryObject => JsObject::heap_size_bytes_for_property_count(new_property_count),
          TargetKind::Function { bound_args_len } => {
            JsFunction::heap_size_bytes_for_bound_args_len_and_property_count(
              bound_args_len,
              new_property_count,
            )
          }
          TargetKind::Promise {
            fulfill_reaction_count,
            reject_reaction_count,
          } => JsPromise::heap_size_bytes_for_counts(
            new_property_count,
            fulfill_reaction_count,
            reject_reaction_count,
          ),
        };

        // Before allocating, enforce heap limits based on the net growth of this object.
        let grow_by = new_bytes.saturating_sub(old_bytes);
        self.ensure_can_allocate(grow_by)?;

        // Allocate the new property table fallibly so hostile inputs cannot abort the host process
        // on allocator OOM.
        let mut buf: Vec<PropertyEntry> = Vec::new();
        buf
          .try_reserve_exact(new_property_count)
          .map_err(|_| VmError::OutOfMemory)?;

        {
          let slot = &self.slots[idx];
          match slot.value.as_ref() {
            Some(HeapObject::Object(obj)) => buf.extend_from_slice(&obj.base.properties),
            Some(HeapObject::Function(func)) => buf.extend_from_slice(&func.base.properties),
            Some(HeapObject::Promise(p)) => buf.extend_from_slice(&p.object.base.properties),
            _ => return Err(VmError::InvalidHandle),
          }
        }

        buf.push(PropertyEntry { key, desc });
        let properties = buf.into_boxed_slice();

        match self.slots[idx].value.as_mut() {
          Some(HeapObject::Object(obj)) => obj.base.properties = properties,
          Some(HeapObject::Function(func)) => func.base.properties = properties,
          Some(HeapObject::Promise(p)) => p.object.base.properties = properties,
          _ => return Err(VmError::InvalidHandle),
        }

        self.update_slot_bytes(idx, new_bytes);

        #[cfg(debug_assertions)]
        self.debug_assert_used_bytes_is_correct();
        Ok(())
      }
    }
  }

  fn get_heap_object(&self, id: HeapId) -> Result<&HeapObject, VmError> {
    let idx = self.validate(id).ok_or(VmError::InvalidHandle)?;
    self.slots[idx].value.as_ref().ok_or(VmError::InvalidHandle)
  }

  fn get_heap_object_mut(&mut self, id: HeapId) -> Result<&mut HeapObject, VmError> {
    let idx = self.validate(id).ok_or(VmError::InvalidHandle)?;
    self.slots[idx].value.as_mut().ok_or(VmError::InvalidHandle)
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

  fn update_slot_bytes(&mut self, idx: usize, new_bytes: usize) {
    let slot = &mut self.slots[idx];
    let old_bytes = slot.bytes;

    if new_bytes >= old_bytes {
      self.used_bytes = self.used_bytes.saturating_add(new_bytes - old_bytes);
    } else {
      self.used_bytes = self.used_bytes.saturating_sub(old_bytes - new_bytes);
    }

    slot.bytes = new_bytes;
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

    let id = HeapId::from_parts(idx as u32, slot.generation);

    #[cfg(debug_assertions)]
    self.debug_assert_used_bytes_is_correct();

    id
  }

  fn debug_value_is_valid_or_primitive(&self, value: Value) -> bool {
    match value {
      Value::Undefined | Value::Null | Value::Bool(_) | Value::Number(_) => true,
      Value::String(s) => self.is_valid_string(s),
      Value::Symbol(s) => self.is_valid_symbol(s),
      Value::Object(o) => self.is_valid_object(o),
    }
  }

  pub(crate) fn get_function_call_handler(&self, func: GcObject) -> Result<CallHandler, VmError> {
    match self.get_heap_object(func.0)? {
      HeapObject::Function(f) => Ok(f.call),
      _ => Err(VmError::NotCallable),
    }
  }

  pub(crate) fn get_function_construct_handler(
    &self,
    func: GcObject,
  ) -> Result<Option<ConstructHandler>, VmError> {
    match self.get_heap_object(func.0)? {
      HeapObject::Function(f) => Ok(f.construct),
      _ => Err(VmError::NotConstructable),
    }
  }

  pub(crate) fn get_function_name(&self, func: GcObject) -> Result<GcString, VmError> {
    match self.get_heap_object(func.0)? {
      HeapObject::Function(f) => Ok(f.name),
      _ => Err(VmError::InvalidHandle),
    }
  }
}

/// A stack-rooting scope.
///
/// All stack roots pushed via [`Scope::push_root`] are removed when the scope is dropped.
pub struct Scope<'a> {
  heap: &'a mut Heap,
  root_stack_len_at_entry: usize,
  env_root_stack_len_at_entry: usize,
}

impl Drop for Scope<'_> {
  fn drop(&mut self) {
    self.heap.root_stack.truncate(self.root_stack_len_at_entry);
    self
      .heap
      .env_root_stack
      .truncate(self.env_root_stack_len_at_entry);
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

  pub(crate) fn push_env_root(&mut self, env: GcEnv) -> GcEnv {
    debug_assert!(self.heap.is_valid_env(env));
    self.heap.env_root_stack.push(env);
    env
  }

  /// Creates a nested child scope that borrows the same heap.
  pub fn reborrow(&mut self) -> Scope<'_> {
    let root_stack_len_at_entry = self.heap.root_stack.len();
    let env_root_stack_len_at_entry = self.heap.env_root_stack.len();
    Scope {
      heap: &mut *self.heap,
      root_stack_len_at_entry,
      env_root_stack_len_at_entry,
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
    let new_bytes = JsObject::heap_size_bytes_for_property_count(0);
    self.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Object(JsObject::new(None));
    Ok(GcObject(self.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Allocates an ordinary object with the provided `[[Prototype]]` and own properties.
  pub fn alloc_object_with_properties(
    &mut self,
    proto: Option<GcObject>,
    props: &[(PropertyKey, PropertyDescriptor)],
  ) -> Result<GcObject, VmError> {
    // Root the prototype and all keys/values during allocation in case `ensure_can_allocate`
    // triggers a GC cycle.
    //
    // Note: these roots are temporary; once the object is allocated, it will retain handles and
    // trace them.
    let mut scope = self.reborrow();
    if let Some(proto) = proto {
      scope.push_root(Value::Object(proto));
    }
    for (key, desc) in props {
      match key {
        PropertyKey::String(s) => {
          scope.push_root(Value::String(*s));
        }
        PropertyKey::Symbol(s) => {
          scope.push_root(Value::Symbol(*s));
        }
      }
      match desc.kind {
        PropertyKind::Data { value, .. } => {
          scope.push_root(value);
        }
        PropertyKind::Accessor { get, set } => {
          scope.push_root(get);
          scope.push_root(set);
        }
      }
    }

    let new_bytes = JsObject::heap_size_bytes_for_property_count(props.len());
    scope.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Object(JsObject::from_property_slice(proto, props)?);
    Ok(GcObject(scope.heap.alloc_unchecked(obj, new_bytes)))
  }

  /// Allocates an empty JavaScript object on the heap with an explicit internal prototype.
  pub fn alloc_object_with_prototype(
    &mut self,
    prototype: Option<GcObject>,
  ) -> Result<GcObject, VmError> {
    self.alloc_object_with_properties(prototype, &[])
  }

  /// Allocates a new JavaScript Array object on the heap.
  ///
  /// This is a minimal stub for WebIDL conversions. The returned object is an ordinary object with
  /// an own `length` data property.
  pub fn alloc_array(&mut self, len: usize) -> Result<GcObject, VmError> {
    // Root the array object while creating the `length` property so that intermediate allocations
    // (creating the key string, growing the property table) cannot collect it.
    let arr = self.alloc_object()?;
    let mut scope = self.reborrow();
    scope.push_root(Value::Object(arr));

    let length_key = scope.alloc_string("length")?;
    let desc = PropertyDescriptor {
      enumerable: false,
      configurable: false,
      kind: PropertyKind::Data {
        value: Value::Number(len as f64),
        writable: true,
      },
    };
    scope.define_property(arr, PropertyKey::from_string(length_key), desc)?;
    Ok(arr)
  }
  /// Allocates a new pending Promise object on the heap.
  pub fn alloc_promise(&mut self) -> Result<GcObject, VmError> {
    self.alloc_promise_with_prototype(None)
  }

  /// Allocates a new pending Promise object on the heap with an explicit `[[Prototype]]`.
  pub fn alloc_promise_with_prototype(
    &mut self,
    prototype: Option<GcObject>,
  ) -> Result<GcObject, VmError> {
    // Root inputs during allocation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    if let Some(proto) = prototype {
      scope.push_root(Value::Object(proto));
    }

    let new_bytes = JsPromise::heap_size_bytes_for_counts(0, 0, 0);
    scope.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Promise(JsPromise::new(prototype));
    Ok(GcObject(scope.heap.alloc_unchecked(obj, new_bytes)))
  }
  /// Defines (adds or replaces) an own property on `obj`.
  pub fn define_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptor,
  ) -> Result<(), VmError> {
    // Root inputs for the duration of the operation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    scope.push_root(Value::Object(obj));

    match key {
      PropertyKey::String(s) => {
        scope.push_root(Value::String(s));
      }
      PropertyKey::Symbol(s) => {
        scope.push_root(Value::Symbol(s));
      }
    }

    match desc.kind {
      PropertyKind::Data { value, .. } => {
        scope.push_root(value);
      }
      PropertyKind::Accessor { get, set } => {
        scope.push_root(get);
        scope.push_root(set);
      }
    }

    scope.heap.define_property(obj, key, desc)
  }

  fn root_promise_reaction(&mut self, reaction: &PromiseReaction) {
    if let Some(handler) = reaction.handler {
      self.push_root(handler);
    }
    if let Some(cap) = &reaction.capability {
      self.push_root(Value::Object(cap.promise));
      self.push_root(cap.resolve);
      self.push_root(cap.reject);
    }
  }

  /// Appends a reaction record to `promise.[[PromiseFulfillReactions]]`.
  pub fn promise_append_fulfill_reaction(
    &mut self,
    promise: GcObject,
    reaction: PromiseReaction,
  ) -> Result<(), VmError> {
    // Root inputs for the duration of the operation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    scope.push_root(Value::Object(promise));
    scope.root_promise_reaction(&reaction);

    scope.heap.promise_append_reaction(promise, true, reaction)
  }

  /// Appends a reaction record to `promise.[[PromiseRejectReactions]]`.
  pub fn promise_append_reject_reaction(
    &mut self,
    promise: GcObject,
    reaction: PromiseReaction,
  ) -> Result<(), VmError> {
    // Root inputs for the duration of the operation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    scope.push_root(Value::Object(promise));
    scope.root_promise_reaction(&reaction);

    scope.heap.promise_append_reaction(promise, false, reaction)
  }

  /// Allocates a native JavaScript function object on the heap.
  pub fn alloc_native_function(
    &mut self,
    call: NativeFunctionId,
    construct: Option<NativeConstructId>,
    name: GcString,
    length: u32,
  ) -> Result<GcObject, VmError> {
    // Root inputs during allocation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    scope.push_root(Value::String(name));

    let func = JsFunction::new_native(call, construct, name, length);
    let new_bytes = func.heap_size_bytes();
    scope.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Function(func);
    let func = GcObject(scope.heap.alloc_unchecked(obj, new_bytes));

    // Define standard function properties.
    crate::function_properties::set_function_name(
      &mut scope,
      func,
      PropertyKey::String(name),
      None,
    )?;
    crate::function_properties::set_function_length(&mut scope, func, length)?;

    // Constructors get a `.prototype` object.
    if construct.is_some() {
      crate::function_properties::make_constructor(&mut scope, func)?;
    }

    Ok(func)
  }

  pub fn env_create(&mut self, outer: Option<GcEnv>) -> Result<GcEnv, VmError> {
    // Root `outer` during allocation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    if let Some(outer) = outer {
      scope.push_env_root(outer);
    }

    let new_bytes = EnvRecord::heap_size_bytes_for_binding_count(0);
    scope.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Env(EnvRecord::new(outer));
    Ok(GcEnv(scope.heap.alloc_unchecked(obj, new_bytes)))
  }

  pub(crate) fn env_create_mutable_binding(&mut self, env: GcEnv, name: &str) -> Result<(), VmError> {
    if self.heap().env_has_binding(env, name)? {
      return Err(VmError::Unimplemented("duplicate binding"));
    }

    let mut scope = self.reborrow();
    scope.push_env_root(env);

    let name = scope.alloc_string(name)?;
    scope.push_root(Value::String(name));

    scope.heap.env_add_binding(
      env,
      EnvBinding {
        name,
        value: Value::Undefined,
        mutable: true,
        initialized: false,
      },
    )
  }

  pub(crate) fn env_create_immutable_binding(&mut self, env: GcEnv, name: &str) -> Result<(), VmError> {
    if self.heap().env_has_binding(env, name)? {
      return Err(VmError::Unimplemented("duplicate binding"));
    }

    let mut scope = self.reborrow();
    scope.push_env_root(env);

    let name = scope.alloc_string(name)?;
    scope.push_root(Value::String(name));

    scope.heap.env_add_binding(
      env,
      EnvBinding {
        name,
        value: Value::Undefined,
        mutable: false,
        initialized: false,
      },
    )
  }

  /// Allocates an ECMAScript (user-defined) function object on the heap.
  pub fn alloc_ecma_function(
    &mut self,
    code: EcmaFunctionId,
    is_constructable: bool,
    name: GcString,
    length: u32,
    this_mode: ThisMode,
    is_strict: bool,
    closure_env: Option<GcEnv>,
  ) -> Result<GcObject, VmError> {
    // Root inputs during allocation in case `ensure_can_allocate` triggers a GC.
    let mut scope = self.reborrow();
    scope.push_root(Value::String(name));
    if let Some(env) = closure_env {
      scope.push_env_root(env);
    }

    let func = JsFunction::new_ecma(
      code,
      is_constructable,
      name,
      length,
      this_mode,
      is_strict,
      closure_env,
    );
    let new_bytes = func.heap_size_bytes();
    scope.heap.ensure_can_allocate(new_bytes)?;

    let obj = HeapObject::Function(func);
    let func = GcObject(scope.heap.alloc_unchecked(obj, new_bytes));

    // Define standard function properties.
    crate::function_properties::set_function_name(
      &mut scope,
      func,
      PropertyKey::String(name),
      None,
    )?;
    crate::function_properties::set_function_length(&mut scope, func, length)?;

    // Constructors get a `.prototype` object.
    if is_constructable {
      crate::function_properties::make_constructor(&mut scope, func)?;
    }

    Ok(func)
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
  Function(JsFunction),
  Env(EnvRecord),
  Promise(JsPromise),
}

impl Trace for HeapObject {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    match self {
      HeapObject::String(s) => s.trace(tracer),
      HeapObject::Symbol(s) => s.trace(tracer),
      HeapObject::Object(o) => o.trace(tracer),
      HeapObject::Function(f) => f.trace(tracer),
      HeapObject::Env(e) => e.trace(tracer),
      HeapObject::Promise(p) => p.trace(tracer),
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
pub(crate) struct ObjectBase {
  prototype: Option<GcObject>,
  extensible: bool,
  properties: Box<[PropertyEntry]>,
}

impl ObjectBase {
  pub(crate) fn new(prototype: Option<GcObject>) -> Self {
    Self {
      prototype,
      extensible: true,
      properties: Box::default(),
    }
  }

  fn from_property_slice(
    prototype: Option<GcObject>,
    props: &[(PropertyKey, PropertyDescriptor)],
  ) -> Result<Self, VmError> {
    // Avoid process abort on allocator OOM: allocate the property buffer fallibly.
    let mut buf: Vec<PropertyEntry> = Vec::new();
    buf
      .try_reserve_exact(props.len())
      .map_err(|_| VmError::OutOfMemory)?;
    buf.extend(props.iter().map(|(key, desc)| PropertyEntry {
      key: *key,
      desc: *desc,
    }));

    Ok(Self {
      prototype,
      extensible: true,
      properties: buf.into_boxed_slice(),
    })
  }

  pub(crate) fn property_count(&self) -> usize {
    self.properties.len()
  }

  pub(crate) fn properties_heap_size_bytes_for_count(count: usize) -> usize {
    count
      .checked_mul(mem::size_of::<PropertyEntry>())
      .unwrap_or(usize::MAX)
  }
}

impl Trace for ObjectBase {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    if let Some(proto) = self.prototype {
      tracer.trace_value(Value::Object(proto));
    }
    for prop in self.properties.iter() {
      prop.trace(tracer);
    }
  }
}

#[derive(Debug)]
struct JsObject {
  base: ObjectBase,
}

impl JsObject {
  fn new(prototype: Option<GcObject>) -> Self {
    Self {
      base: ObjectBase::new(prototype),
    }
  }

  fn from_property_slice(
    prototype: Option<GcObject>,
    props: &[(PropertyKey, PropertyDescriptor)],
  ) -> Result<Self, VmError> {
    Ok(Self {
      base: ObjectBase::from_property_slice(prototype, props)?,
    })
  }

  fn heap_size_bytes_for_property_count(count: usize) -> usize {
    let props_bytes = ObjectBase::properties_heap_size_bytes_for_count(count);
    mem::size_of::<Self>()
      .checked_add(props_bytes)
      .unwrap_or(usize::MAX)
  }
}

impl Trace for JsObject {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    self.base.trace(tracer);
  }
}

#[derive(Debug)]
struct JsPromise {
  object: JsObject,
  state: PromiseState,
  result: Value,
  fulfill_reactions: Box<[PromiseReaction]>,
  reject_reactions: Box<[PromiseReaction]>,
  is_handled: bool,
}

impl JsPromise {
  fn new(prototype: Option<GcObject>) -> Self {
    Self {
      object: JsObject::new(prototype),
      state: PromiseState::Pending,
      result: Value::Undefined,
      fulfill_reactions: Box::default(),
      reject_reactions: Box::default(),
      is_handled: false,
    }
  }

  fn heap_size_bytes(&self) -> usize {
    Self::heap_size_bytes_for_counts(
      self.object.base.properties.len(),
      self.fulfill_reactions.len(),
      self.reject_reactions.len(),
    )
  }

  fn heap_size_bytes_for_counts(
    property_count: usize,
    fulfill_reaction_count: usize,
    reject_reaction_count: usize,
  ) -> usize {
    let props_bytes = property_count
      .checked_mul(mem::size_of::<PropertyEntry>())
      .unwrap_or(usize::MAX);
    let fulfill_bytes = fulfill_reaction_count
      .checked_mul(mem::size_of::<PromiseReaction>())
      .unwrap_or(usize::MAX);
    let reject_bytes = reject_reaction_count
      .checked_mul(mem::size_of::<PromiseReaction>())
      .unwrap_or(usize::MAX);

    mem::size_of::<Self>()
      .checked_add(props_bytes)
      .and_then(|v| v.checked_add(fulfill_bytes))
      .and_then(|v| v.checked_add(reject_bytes))
      .unwrap_or(usize::MAX)
  }
}

impl Trace for JsPromise {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    self.object.trace(tracer);
    tracer.trace_value(self.result);
    for reaction in self.fulfill_reactions.iter() {
      reaction.trace(tracer);
    }
    for reaction in self.reject_reactions.iter() {
      reaction.trace(tracer);
    }
  }
}

#[derive(Debug, Clone, Copy)]
pub(crate) struct PropertyEntry {
  key: PropertyKey,
  desc: PropertyDescriptor,
}

impl Trace for PropertyEntry {
  fn trace(&self, tracer: &mut Tracer<'_>) {
    self.key.trace(tracer);
    self.desc.trace(tracer);
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

  pub(crate) fn trace_env(&mut self, env: GcEnv) {
    self.trace_heap_id(env.0);
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
