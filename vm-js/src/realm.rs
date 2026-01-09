use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, Heap, Intrinsics, RealmId, RootId, Value, Vm, VmError, WellKnownSymbols};
use std::sync::atomic::{AtomicU64, Ordering};

static NEXT_REALM_ID: AtomicU64 = AtomicU64::new(1);

/// An ECMAScript realm: global object + intrinsics.
///
/// This type owns a set of **persistent GC roots** registered with the [`Heap`]. Call
/// [`Realm::teardown`] to unregister those roots when the embedding is finished with the realm (for
/// example, when running many `test262` tests by creating a fresh realm per test while reusing a
/// single heap).
#[derive(Debug)]
pub struct Realm {
  id: RealmId,
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
  /// Returns the host-facing [`RealmId`] token for this realm.
  ///
  /// This is used to tag Promise jobs and other host-scheduled work with the realm they should run
  /// in.
  pub fn id(&self) -> RealmId {
    self.id
  }

  /// Creates a new realm on `heap`.
  pub fn new(vm: &mut Vm, heap: &mut Heap) -> Result<Self, VmError> {
    let id = RealmId::from_raw(NEXT_REALM_ID.fetch_add(1, Ordering::Relaxed));
    let mut roots = Vec::new();

    let mut scope = heap.scope();
    let global_object = scope.alloc_object()?;
    scope.push_root(Value::Object(global_object))?;
    roots.push(scope.heap_mut().add_root(Value::Object(global_object))?);

    let intrinsics = match Intrinsics::init(vm, &mut scope, &mut roots) {
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

      // --- Global value properties ---
      let infinity_key = PropertyKey::from_string(scope.alloc_string("Infinity")?);
      scope.define_property(
        global_object,
        infinity_key,
        PropertyDescriptor {
          enumerable: false,
          configurable: false,
          kind: PropertyKind::Data {
            value: Value::Number(f64::INFINITY),
            writable: false,
          },
        },
      )?;

      let nan_key = PropertyKey::from_string(scope.alloc_string("NaN")?);
      scope.define_property(
        global_object,
        nan_key,
        PropertyDescriptor {
          enumerable: false,
          configurable: false,
          kind: PropertyKind::Data {
            value: Value::Number(f64::NAN),
            writable: false,
          },
        },
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

      // Install baseline global bindings as non-enumerable global properties.
      let object_key = PropertyKey::from_string(scope.alloc_string("Object")?);
      scope.define_property(
        global_object,
        object_key,
        global_data_desc(Value::Object(intrinsics.object_constructor())),
      )?;

      let function_key = PropertyKey::from_string(scope.alloc_string("Function")?);
      scope.define_property(
        global_object,
        function_key,
        global_data_desc(Value::Object(intrinsics.function_constructor())),
      )?;

      let array_key = PropertyKey::from_string(scope.alloc_string("Array")?);
      scope.define_property(
        global_object,
        array_key,
        global_data_desc(Value::Object(intrinsics.array_constructor())),
      )?;

      let string_key = PropertyKey::from_string(scope.alloc_string("String")?);
      scope.define_property(
        global_object,
        string_key,
        global_data_desc(Value::Object(intrinsics.string_constructor())),
      )?;

      let number_key = PropertyKey::from_string(scope.alloc_string("Number")?);
      scope.define_property(
        global_object,
        number_key,
        global_data_desc(Value::Object(intrinsics.number_constructor())),
      )?;

      let boolean_key = PropertyKey::from_string(scope.alloc_string("Boolean")?);
      scope.define_property(
        global_object,
        boolean_key,
        global_data_desc(Value::Object(intrinsics.boolean_constructor())),
      )?;

      let date_key = PropertyKey::from_string(scope.alloc_string("Date")?);
      scope.define_property(
        global_object,
        date_key,
        global_data_desc(Value::Object(intrinsics.date_constructor())),
      )?;

      let symbol_key = PropertyKey::from_string(scope.alloc_string("Symbol")?);
      scope.define_property(
        global_object,
        symbol_key,
        global_data_desc(Value::Object(intrinsics.symbol_constructor())),
      )?;

      let is_nan_key = PropertyKey::from_string(scope.alloc_string("isNaN")?);
      scope.define_property(
        global_object,
        is_nan_key,
        global_data_desc(Value::Object(intrinsics.is_nan())),
      )?;

      let json_key = PropertyKey::from_string(scope.alloc_string("JSON")?);
      scope.define_property(
        global_object,
        json_key,
        global_data_desc(Value::Object(intrinsics.json())),
      )?;

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

      // Promise
      let promise_key = PropertyKey::from_string(scope.alloc_string("Promise")?);
      scope.define_property(
        global_object,
        promise_key,
        global_data_desc(Value::Object(intrinsics.promise())),
      )?;

      Ok(())
    })() {
      for root in roots.drain(..) {
        scope.heap_mut().remove_root(root);
      }
      return Err(err);
    }

    vm.set_intrinsics(intrinsics);

    Ok(Self {
      id,
      global_object,
      intrinsics,
      roots,
      torn_down: false,
    })
  }

  pub fn id(&self) -> RealmId {
    self.id
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
