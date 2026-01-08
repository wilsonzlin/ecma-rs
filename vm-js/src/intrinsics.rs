use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{GcObject, RootId, Scope, Value, VmError};

/// The set of ECMAScript intrinsics for a realm.
///
/// These are kept alive independently of any global bindings so that deleting global properties
/// (e.g. `delete globalThis.TypeError`) does not allow the GC to collect the engine's intrinsic
/// graph.
#[derive(Debug, Clone, Copy)]
pub struct Intrinsics {
  object_prototype: GcObject,
  function_prototype: GcObject,
  array_prototype: GcObject,

  error: GcObject,
  error_prototype: GcObject,
  type_error: GcObject,
  type_error_prototype: GcObject,
  range_error: GcObject,
  range_error_prototype: GcObject,
  reference_error: GcObject,
  reference_error_prototype: GcObject,
  syntax_error: GcObject,
  syntax_error_prototype: GcObject,
  eval_error: GcObject,
  eval_error_prototype: GcObject,
  uri_error: GcObject,
  uri_error_prototype: GcObject,
  aggregate_error: GcObject,
  aggregate_error_prototype: GcObject,
}

#[derive(Clone, Copy)]
struct CommonKeys {
  constructor: PropertyKey,
  prototype: PropertyKey,
  name: PropertyKey,
  length: PropertyKey,
}

fn data_desc(value: Value, writable: bool, enumerable: bool, configurable: bool) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable,
    configurable,
    kind: PropertyKind::Data { value, writable },
  }
}

fn alloc_rooted_object(scope: &mut Scope<'_>, roots: &mut Vec<RootId>) -> Result<GcObject, VmError> {
  let obj = scope.alloc_object()?;
  roots.push(scope.heap_mut().add_root(Value::Object(obj)));
  Ok(obj)
}

fn init_native_error(
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  common: CommonKeys,
  function_prototype: GcObject,
  base_prototype: GcObject,
  name: &str,
  length: f64,
) -> Result<(GcObject, GcObject), VmError> {
  // `%X.prototype%`
  let prototype = alloc_rooted_object(scope, roots)?;
  scope
    .heap_mut()
    .object_set_prototype(prototype, Some(base_prototype))?;

  // `%X%`
  let constructor = alloc_rooted_object(scope, roots)?;
  scope
    .heap_mut()
    .object_set_prototype(constructor, Some(function_prototype))?;

  // Create (and store) the name string early so it is kept alive by the rooted objects before any
  // subsequent allocations/GC.
  let name_string = scope.alloc_string(name)?;

  // X.prototype.constructor
  scope.define_property(
    prototype,
    common.constructor,
    data_desc(Value::Object(constructor), true, false, true),
  )?;
  // X.prototype.name
  scope.define_property(
    prototype,
    common.name,
    data_desc(Value::String(name_string), true, false, true),
  )?;

  // X.prototype on the constructor
  scope.define_property(
    constructor,
    common.prototype,
    data_desc(Value::Object(prototype), false, false, false),
  )?;
  // X.name / X.length
  scope.define_property(
    constructor,
    common.name,
    data_desc(Value::String(name_string), false, false, true),
  )?;
  scope.define_property(
    constructor,
    common.length,
    data_desc(Value::Number(length), false, false, true),
  )?;

  Ok((constructor, prototype))
}

impl Intrinsics {
  pub(crate) fn init(scope: &mut Scope<'_>, roots: &mut Vec<RootId>) -> Result<Self, VmError> {
    // --- Base prototypes ---
    let object_prototype = alloc_rooted_object(scope, roots)?;

    let function_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(function_prototype, Some(object_prototype))?;

    let array_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(array_prototype, Some(object_prototype))?;

    // --- Common property keys used throughout the intrinsic graph ---
    //
    // Root these key strings for the duration of intrinsic initialization: subsequent allocations
    // may trigger GC before we store the keys on any rooted object.
    let constructor_key_s = scope.alloc_string("constructor")?;
    scope.push_root(Value::String(constructor_key_s));
    let prototype_key_s = scope.alloc_string("prototype")?;
    scope.push_root(Value::String(prototype_key_s));
    let name_key_s = scope.alloc_string("name")?;
    scope.push_root(Value::String(name_key_s));
    let length_key_s = scope.alloc_string("length")?;
    scope.push_root(Value::String(length_key_s));

    let common = CommonKeys {
      constructor: PropertyKey::from_string(constructor_key_s),
      prototype: PropertyKey::from_string(prototype_key_s),
      name: PropertyKey::from_string(name_key_s),
      length: PropertyKey::from_string(length_key_s),
    };

    // --- Error + subclasses ---
    let (error, error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      object_prototype,
      "Error",
      1.0,
    )?;

    let (type_error, type_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "TypeError",
      1.0,
    )?;

    let (range_error, range_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "RangeError",
      1.0,
    )?;

    let (reference_error, reference_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "ReferenceError",
      1.0,
    )?;

    let (syntax_error, syntax_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "SyntaxError",
      1.0,
    )?;

    let (eval_error, eval_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "EvalError",
      1.0,
    )?;

    let (uri_error, uri_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "URIError",
      1.0,
    )?;

    let (aggregate_error, aggregate_error_prototype) = init_native_error(
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      "AggregateError",
      2.0,
    )?;

    Ok(Self {
      object_prototype,
      function_prototype,
      array_prototype,
      error,
      error_prototype,
      type_error,
      type_error_prototype,
      range_error,
      range_error_prototype,
      reference_error,
      reference_error_prototype,
      syntax_error,
      syntax_error_prototype,
      eval_error,
      eval_error_prototype,
      uri_error,
      uri_error_prototype,
      aggregate_error,
      aggregate_error_prototype,
    })
  }

  pub fn object_prototype(&self) -> GcObject {
    self.object_prototype
  }

  pub fn function_prototype(&self) -> GcObject {
    self.function_prototype
  }

  pub fn array_prototype(&self) -> GcObject {
    self.array_prototype
  }

  pub fn error(&self) -> GcObject {
    self.error
  }

  pub fn error_prototype(&self) -> GcObject {
    self.error_prototype
  }

  pub fn type_error(&self) -> GcObject {
    self.type_error
  }

  pub fn type_error_prototype(&self) -> GcObject {
    self.type_error_prototype
  }

  pub fn range_error(&self) -> GcObject {
    self.range_error
  }

  pub fn range_error_prototype(&self) -> GcObject {
    self.range_error_prototype
  }

  pub fn reference_error(&self) -> GcObject {
    self.reference_error
  }

  pub fn reference_error_prototype(&self) -> GcObject {
    self.reference_error_prototype
  }

  pub fn syntax_error(&self) -> GcObject {
    self.syntax_error
  }

  pub fn syntax_error_prototype(&self) -> GcObject {
    self.syntax_error_prototype
  }

  pub fn eval_error(&self) -> GcObject {
    self.eval_error
  }

  pub fn eval_error_prototype(&self) -> GcObject {
    self.eval_error_prototype
  }

  pub fn uri_error(&self) -> GcObject {
    self.uri_error
  }

  pub fn uri_error_prototype(&self) -> GcObject {
    self.uri_error_prototype
  }

  pub fn aggregate_error(&self) -> GcObject {
    self.aggregate_error
  }

  pub fn aggregate_error_prototype(&self) -> GcObject {
    self.aggregate_error_prototype
  }
}

