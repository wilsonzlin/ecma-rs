use crate::{GcObject, Heap, Intrinsics, RootId, Value, VmError};

/// An ECMAScript realm: global object + intrinsics.
///
/// This type owns a set of **persistent GC roots** registered with the [`Heap`]. Call
/// [`Realm::teardown`] to unregister those roots when the embedding is finished with the realm (for
/// example, when running many `test262` tests by creating a fresh realm per test while reusing a
/// single heap).
#[derive(Debug)]
pub struct Realm {
  global_object: GcObject,
  intrinsics: Intrinsics,
  roots: Vec<RootId>,
  torn_down: bool,
}

impl Realm {
  /// Creates a new realm on `heap`.
  pub fn new(heap: &mut Heap) -> Result<Self, VmError> {
    let mut roots = Vec::new();

    let mut scope = heap.scope();
    let global_object = scope.alloc_object()?;
    roots.push(scope.heap_mut().add_root(Value::Object(global_object)));

    let intrinsics = match Intrinsics::init(&mut scope, &mut roots) {
      Ok(intrinsics) => intrinsics,
      Err(err) => {
        // Avoid leaking persistent roots when realm initialization fails.
        for root in roots.drain(..) {
          scope.heap_mut().remove_root(root);
        }
        return Err(err);
      }
    };

    Ok(Self {
      global_object,
      intrinsics,
      roots,
      torn_down: false,
    })
  }

  /// The realm's global object.
  pub fn global_object(&self) -> GcObject {
    self.global_object
  }

  /// The realm's intrinsic objects.
  pub fn intrinsics(&self) -> &Intrinsics {
    &self.intrinsics
  }

  /// Unregisters all realm roots from the heap.
  ///
  /// # Safety contract
  ///
  /// After teardown, the realm must not be used for execution. Any GC handles retained by the
  /// realm (including the global object and intrinsics) may become invalid after the next GC cycle.
  ///
  /// This method is **idempotent**.
  pub fn teardown(&mut self, heap: &mut Heap) {
    if self.torn_down {
      return;
    }
    self.torn_down = true;

    for root in self.roots.drain(..) {
      heap.remove_root(root);
    }
  }
}

impl Drop for Realm {
  fn drop(&mut self) {
    debug_assert!(
      self.torn_down,
      "Realm dropped without calling teardown(); this can leak persistent GC roots if the Heap is reused"
    );
  }
}
