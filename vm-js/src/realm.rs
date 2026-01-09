use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Heap, Intrinsics, RootId, Value, VmError, WellKnownSymbols};

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

fn global_data_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: false,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

impl Realm {
  /// Creates a new realm on `heap`.
  pub fn new(heap: &mut Heap) -> Result<Self, VmError> {
    let mut roots = Vec::new();

    let mut scope = heap.scope();
    let global_object = scope.alloc_object()?;
    scope.push_root(Value::Object(global_object));
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

    // Any error after this point should also unregister roots to avoid leaks.
    if let Err(err) = (|| -> Result<(), VmError> {
      // Make the global object spec-shaped:
      // `%GlobalObject%.[[Prototype]]` is `%Object.prototype%`.
      scope.heap_mut().object_set_prototype(
        global_object,
        Some(intrinsics.object_prototype()),
      )?;

      // `globalThis` is a writable, configurable, non-enumerable data property whose value is the
      // global object itself.
      let global_this_key = PropertyKey::from_string(scope.alloc_string("globalThis")?);
      scope.define_property(
        global_object,
        global_this_key,
        global_data_desc(Value::Object(global_object)),
      )?;

      // (Optional but useful) Define a global `undefined` binding. In the spec this property is
      // non-writable, non-enumerable, non-configurable.
      let undefined_key = PropertyKey::from_string(scope.alloc_string("undefined")?);
      scope.define_property(
        global_object,
        undefined_key,
        PropertyDescriptor {
          enumerable: false,
          configurable: false,
          kind: PropertyKind::Data {
            value: Value::Undefined,
            writable: false,
          },
        },
      )?;

      // Install the standard native Error constructors as non-enumerable global properties.
      let error_key = PropertyKey::from_string(scope.alloc_string("Error")?);
      scope.define_property(
        global_object,
        error_key,
        global_data_desc(Value::Object(intrinsics.error())),
      )?;

      let type_error_key = PropertyKey::from_string(scope.alloc_string("TypeError")?);
      scope.define_property(
        global_object,
        type_error_key,
        global_data_desc(Value::Object(intrinsics.type_error())),
      )?;

      let range_error_key = PropertyKey::from_string(scope.alloc_string("RangeError")?);
      scope.define_property(
        global_object,
        range_error_key,
        global_data_desc(Value::Object(intrinsics.range_error())),
      )?;

      let reference_error_key =
        PropertyKey::from_string(scope.alloc_string("ReferenceError")?);
      scope.define_property(
        global_object,
        reference_error_key,
        global_data_desc(Value::Object(intrinsics.reference_error())),
      )?;

      let syntax_error_key = PropertyKey::from_string(scope.alloc_string("SyntaxError")?);
      scope.define_property(
        global_object,
        syntax_error_key,
        global_data_desc(Value::Object(intrinsics.syntax_error())),
      )?;

      let eval_error_key = PropertyKey::from_string(scope.alloc_string("EvalError")?);
      scope.define_property(
        global_object,
        eval_error_key,
        global_data_desc(Value::Object(intrinsics.eval_error())),
      )?;

      let uri_error_key = PropertyKey::from_string(scope.alloc_string("URIError")?);
      scope.define_property(
        global_object,
        uri_error_key,
        global_data_desc(Value::Object(intrinsics.uri_error())),
      )?;

      let aggregate_error_key =
        PropertyKey::from_string(scope.alloc_string("AggregateError")?);
      scope.define_property(
        global_object,
        aggregate_error_key,
        global_data_desc(Value::Object(intrinsics.aggregate_error())),
      )?;

      Ok(())
    })() {
      for root in roots.drain(..) {
        scope.heap_mut().remove_root(root);
      }
      return Err(err);
    }

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

  pub fn well_known_symbols(&self) -> &WellKnownSymbols {
    self.intrinsics.well_known_symbols()
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

  /// Alias for [`Realm::teardown`].
  pub fn remove_roots(&mut self, heap: &mut Heap) {
    self.teardown(heap);
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
