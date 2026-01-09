use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{
  builtins, GcObject, GcString, GcSymbol, NativeConstructId, NativeFunctionId, RootId, Scope, Value,
  Vm, VmError,
};

/// ECMAScript well-known symbols (ECMA-262 "Well-known Symbols" table).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct WellKnownSymbols {
  pub async_iterator: GcSymbol,
  pub has_instance: GcSymbol,
  pub is_concat_spreadable: GcSymbol,
  pub iterator: GcSymbol,
  pub match_: GcSymbol,
  pub match_all: GcSymbol,
  pub replace: GcSymbol,
  pub search: GcSymbol,
  pub species: GcSymbol,
  pub split: GcSymbol,
  pub to_primitive: GcSymbol,
  pub to_string_tag: GcSymbol,
  pub unscopables: GcSymbol,
}

/// The set of ECMAScript intrinsics for a realm.
///
/// These are kept alive independently of any global bindings so that deleting global properties
/// (e.g. `delete globalThis.TypeError`) does not allow the GC to collect the engine's intrinsic
/// graph.
#[derive(Debug, Clone, Copy)]
pub struct Intrinsics {
  well_known_symbols: WellKnownSymbols,
  object_prototype: GcObject,
  function_prototype: GcObject,
  array_prototype: GcObject,
  object_constructor: GcObject,
  function_constructor: GcObject,
  array_constructor: GcObject,

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

fn data_desc(
  value: Value,
  writable: bool,
  enumerable: bool,
  configurable: bool,
) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable,
    configurable,
    kind: PropertyKind::Data { value, writable },
  }
}

fn alloc_rooted_object(
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
) -> Result<GcObject, VmError> {
  let obj = scope.alloc_object()?;
  roots.push(scope.heap_mut().add_root(Value::Object(obj)));
  Ok(obj)
}

fn alloc_rooted_native_function(
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  call: NativeFunctionId,
  construct: Option<NativeConstructId>,
  name: GcString,
  length: u32,
) -> Result<GcObject, VmError> {
  let func = scope.alloc_native_function(call, construct, name, length)?;
  roots.push(scope.heap_mut().add_root(Value::Object(func)));
  Ok(func)
}

fn alloc_rooted_symbol(
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  description: &str,
) -> Result<GcSymbol, VmError> {
  let desc_string = scope.alloc_string(description)?;
  let sym = scope.new_symbol(Some(desc_string))?;
  roots.push(scope.heap_mut().add_root(Value::Symbol(sym)));
  Ok(sym)
}

fn init_native_error(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  common: CommonKeys,
  function_prototype: GcObject,
  base_prototype: GcObject,
  call: NativeFunctionId,
  construct: NativeConstructId,
  name: &str,
  length: u32,
) -> Result<(GcObject, GcObject), VmError> {
  // `%X.prototype%`
  let prototype = alloc_rooted_object(scope, roots)?;
  scope
    .heap_mut()
    .object_set_prototype(prototype, Some(base_prototype))?;

  // Create (and store) the name string early so it is kept alive by the rooted objects before any
  // subsequent allocations/GC.
  let name_string = scope.alloc_string(name)?;

  let constructor = alloc_rooted_native_function(
    scope,
    roots,
    call,
    Some(construct),
    name_string,
    length,
  )?;
  scope
    .heap_mut()
    .object_set_prototype(constructor, Some(function_prototype))?;

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
    // Per ECMA-262, constructor `.prototype` properties are writable but non-configurable.
    data_desc(Value::Object(prototype), true, false, false),
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
    data_desc(Value::Number(length as f64), false, false, true),
  )?;

  Ok((constructor, prototype))
}

impl Intrinsics {
  pub(crate) fn init(
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    roots: &mut Vec<RootId>,
  ) -> Result<Self, VmError> {
    let well_known_symbols = WellKnownSymbols::init(scope, roots)?;

    // --- Base prototypes ---
    let object_prototype = alloc_rooted_object(scope, roots)?;

    let function_prototype_call = vm.register_native_call(builtins::function_prototype_call);
    let function_prototype_name = scope.alloc_string("")?;
    let function_prototype = alloc_rooted_native_function(
      scope,
      roots,
      function_prototype_call,
      None,
      function_prototype_name,
      0,
    )?;
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

    // --- Baseline constructors ---
    // `%Object%`
    let object_call = vm.register_native_call(builtins::object_constructor_call);
    let object_construct = vm.register_native_construct(builtins::object_constructor_construct);
    let object_name = scope.alloc_string("Object")?;
    let object_constructor = alloc_rooted_native_function(
      scope,
      roots,
      object_call,
      Some(object_construct),
      object_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(object_constructor, Some(function_prototype))?;
    scope.define_property(
      object_constructor,
      common.prototype,
      data_desc(Value::Object(object_prototype), false, false, false),
    )?;
    scope.define_property(
      object_constructor,
      common.name,
      data_desc(Value::String(object_name), false, false, true),
    )?;
    scope.define_property(
      object_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      object_prototype,
      common.constructor,
      data_desc(Value::Object(object_constructor), true, false, true),
    )?;

    // `%Function%`
    let function_call = vm.register_native_call(builtins::function_constructor_call);
    let function_construct = vm.register_native_construct(builtins::function_constructor_construct);
    let function_name = scope.alloc_string("Function")?;
    let function_constructor = alloc_rooted_native_function(
      scope,
      roots,
      function_call,
      Some(function_construct),
      function_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(function_constructor, Some(function_prototype))?;
    scope.define_property(
      function_constructor,
      common.prototype,
      data_desc(Value::Object(function_prototype), false, false, false),
    )?;
    scope.define_property(
      function_constructor,
      common.name,
      data_desc(Value::String(function_name), false, false, true),
    )?;
    scope.define_property(
      function_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      function_prototype,
      common.constructor,
      data_desc(Value::Object(function_constructor), true, false, true),
    )?;

    // `%Array%`
    let array_call = vm.register_native_call(builtins::array_constructor_call);
    let array_construct = vm.register_native_construct(builtins::array_constructor_construct);
    let array_name = scope.alloc_string("Array")?;
    let array_constructor = alloc_rooted_native_function(
      scope,
      roots,
      array_call,
      Some(array_construct),
      array_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(array_constructor, Some(function_prototype))?;
    scope.define_property(
      array_constructor,
      common.prototype,
      data_desc(Value::Object(array_prototype), false, false, false),
    )?;
    scope.define_property(
      array_constructor,
      common.name,
      data_desc(Value::String(array_name), false, false, true),
    )?;
    scope.define_property(
      array_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      array_prototype,
      common.constructor,
      data_desc(Value::Object(array_constructor), true, false, true),
    )?;

    // --- Error + subclasses ---
    let error_call = vm.register_native_call(builtins::error_constructor_call);
    let error_construct = vm.register_native_construct(builtins::error_constructor_construct);
    let (error, error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      object_prototype,
      error_call,
      error_construct,
      "Error",
      1,
    )?;

    let (type_error, type_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "TypeError",
      1,
    )?;

    let (range_error, range_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "RangeError",
      1,
    )?;

    let (reference_error, reference_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "ReferenceError",
      1,
    )?;

    let (syntax_error, syntax_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "SyntaxError",
      1,
    )?;

    let (eval_error, eval_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "EvalError",
      1,
    )?;

    let (uri_error, uri_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "URIError",
      1,
    )?;

    let (aggregate_error, aggregate_error_prototype) = init_native_error(
      vm,
      scope,
      roots,
      common,
      function_prototype,
      error_prototype,
      error_call,
      error_construct,
      "AggregateError",
      2,
    )?;
    Ok(Self {
      well_known_symbols,
      object_prototype,
      function_prototype,
      array_prototype,
      object_constructor,
      function_constructor,
      array_constructor,
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

  pub fn well_known_symbols(&self) -> &WellKnownSymbols {
    &self.well_known_symbols
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

  pub fn object_constructor(&self) -> GcObject {
    self.object_constructor
  }

  pub fn function_constructor(&self) -> GcObject {
    self.function_constructor
  }

  pub fn array_constructor(&self) -> GcObject {
    self.array_constructor
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

impl WellKnownSymbols {
  fn init(scope: &mut Scope<'_>, roots: &mut Vec<RootId>) -> Result<Self, VmError> {
    Ok(Self {
      async_iterator: alloc_rooted_symbol(scope, roots, "Symbol.asyncIterator")?,
      has_instance: alloc_rooted_symbol(scope, roots, "Symbol.hasInstance")?,
      is_concat_spreadable: alloc_rooted_symbol(scope, roots, "Symbol.isConcatSpreadable")?,
      iterator: alloc_rooted_symbol(scope, roots, "Symbol.iterator")?,
      match_: alloc_rooted_symbol(scope, roots, "Symbol.match")?,
      match_all: alloc_rooted_symbol(scope, roots, "Symbol.matchAll")?,
      replace: alloc_rooted_symbol(scope, roots, "Symbol.replace")?,
      search: alloc_rooted_symbol(scope, roots, "Symbol.search")?,
      species: alloc_rooted_symbol(scope, roots, "Symbol.species")?,
      split: alloc_rooted_symbol(scope, roots, "Symbol.split")?,
      to_primitive: alloc_rooted_symbol(scope, roots, "Symbol.toPrimitive")?,
      to_string_tag: alloc_rooted_symbol(scope, roots, "Symbol.toStringTag")?,
      unscopables: alloc_rooted_symbol(scope, roots, "Symbol.unscopables")?,
    })
  }
}
