use core::fmt;

use crate::Heap;

/// A stable identifier for an allocation in the [`Heap`](crate::Heap).
///
/// This is a packed `{ index: u32, generation: u32 }`.
/// - `index` selects a slot in the heap's slot vector.
/// - `generation` is incremented each time that slot is freed.
///
/// A `HeapId` is **only valid** if:
/// - `index` is in-bounds for the current heap,
/// - the slot at `index` is occupied, and
/// - the slot's generation matches this handle's generation.
#[derive(Clone, Copy, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct HeapId(pub(crate) u64);

impl HeapId {
  pub(crate) fn from_parts(index: u32, generation: u32) -> Self {
    Self((index as u64) | ((generation as u64) << 32))
  }

  /// The slot index within the heap.
  #[inline]
  pub fn index(self) -> u32 {
    self.0 as u32
  }

  /// The generation of the slot when this handle was created.
  #[inline]
  pub fn generation(self) -> u32 {
    (self.0 >> 32) as u32
  }
}

impl fmt::Debug for HeapId {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("HeapId")
      .field("index", &self.index())
      .field("generation", &self.generation())
      .finish()
  }
}

/// A GC-managed JavaScript object.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct GcObject(pub(crate) HeapId);

impl GcObject {
  /// The underlying [`HeapId`].
  #[inline]
  pub fn id(self) -> HeapId {
    self.0
  }

  /// The slot index within the heap.
  #[inline]
  pub fn index(self) -> u32 {
    self.0.index()
  }

  /// The slot generation within the heap.
  #[inline]
  pub fn generation(self) -> u32 {
    self.0.generation()
  }
}

/// A weak, generation-checked handle to a GC-managed JavaScript object.
///
/// This is intended for host-side wrapper identity maps (e.g. DOM/WebIDL bindings): a host can
/// store `WeakGcObject` values in a `HashMap<NodeId, WeakGcObject>` without accidentally keeping
/// wrappers alive. On lookup, call [`WeakGcObject::upgrade`] to check whether the wrapper is still
/// alive; if not, create a new wrapper and overwrite the entry.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct WeakGcObject(HeapId);

impl WeakGcObject {
  /// Creates a weak handle pointing at `obj`.
  #[inline]
  pub fn new(obj: GcObject) -> Self {
    Self(obj.id())
  }

  /// Attempts to upgrade this weak handle to a strong [`GcObject`].
  ///
  /// Returns `Some(GcObject)` only if the handle still points to a currently-live object
  /// allocation.
  #[inline]
  pub fn upgrade(self, heap: &Heap) -> Option<GcObject> {
    let obj = GcObject(self.0);
    heap.is_valid_object(obj).then_some(obj)
  }

  /// The underlying [`HeapId`].
  #[inline]
  pub fn id(self) -> HeapId {
    self.0
  }

  /// The slot index within the heap.
  #[inline]
  pub fn index(self) -> u32 {
    self.0.index()
  }

  /// The slot generation within the heap.
  #[inline]
  pub fn generation(self) -> u32 {
    self.0.generation()
  }
}

impl From<GcObject> for WeakGcObject {
  #[inline]
  fn from(obj: GcObject) -> Self {
    Self::new(obj)
  }
}

/// A GC-managed JavaScript string.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct GcString(pub(crate) HeapId);

impl GcString {
  /// The underlying [`HeapId`].
  #[inline]
  pub fn id(self) -> HeapId {
    self.0
  }

  /// The slot index within the heap.
  #[inline]
  pub fn index(self) -> u32 {
    self.0.index()
  }

  /// The slot generation within the heap.
  #[inline]
  pub fn generation(self) -> u32 {
    self.0.generation()
  }
}

/// A GC-managed JavaScript symbol.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct GcSymbol(pub(crate) HeapId);

impl GcSymbol {
  /// The underlying [`HeapId`].
  #[inline]
  pub fn id(self) -> HeapId {
    self.0
  }

  /// The slot index within the heap.
  #[inline]
  pub fn index(self) -> u32 {
    self.0.index()
  }

  /// The slot generation within the heap.
  #[inline]
  pub fn generation(self) -> u32 {
    self.0.generation()
  }
}

/// A GC-managed internal environment record.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub(crate) struct GcEnv(pub(crate) HeapId);

#[allow(dead_code)]
impl GcEnv {
  /// The underlying [`HeapId`].
  #[inline]
  pub fn id(self) -> HeapId {
    self.0
  }

  /// The slot index within the heap.
  #[inline]
  pub fn index(self) -> u32 {
    self.0.index()
  }

  /// The slot generation within the heap.
  #[inline]
  pub fn generation(self) -> u32 {
    self.0.generation()
  }
}

/// An ID for a persistent root stored in the heap.
///
/// Returned by [`Heap::add_root`](crate::Heap::add_root) and later passed to
/// [`Heap::remove_root`](crate::Heap::remove_root).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub struct RootId(pub(crate) u32);

impl RootId {
  /// The underlying index into the heap's persistent root table.
  #[inline]
  pub fn index(self) -> u32 {
    self.0
  }
}

/// An ID for a persistent environment root stored in the heap.
///
/// This is used to keep internal environment records alive across GC cycles.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(transparent)]
pub(crate) struct EnvRootId(pub(crate) u32);

#[allow(dead_code)]
impl EnvRootId {
  /// The underlying index into the heap's persistent env root table.
  #[inline]
  pub fn index(self) -> u32 {
    self.0
  }
}
