use core::fmt;

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
