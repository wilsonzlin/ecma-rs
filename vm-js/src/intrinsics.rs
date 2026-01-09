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
  string_prototype: GcObject,
  number_prototype: GcObject,
  boolean_prototype: GcObject,
  bigint_prototype: GcObject,
  date_prototype: GcObject,
  symbol_prototype: GcObject,
  object_constructor: GcObject,
  function_constructor: GcObject,
  array_constructor: GcObject,
  string_constructor: GcObject,
  number_constructor: GcObject,
  boolean_constructor: GcObject,
  date_constructor: GcObject,
  symbol_constructor: GcObject,
  is_nan: GcObject,
  json: GcObject,

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

  promise: GcObject,
  promise_prototype: GcObject,
  promise_resolving_function_call: NativeFunctionId,
  promise_finally_handler_call: NativeFunctionId,
  promise_finally_thunk_call: NativeFunctionId,
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
  roots.push(scope.heap_mut().add_root(Value::Object(obj))?);
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
  roots.push(scope.heap_mut().add_root(Value::Object(func))?);
  Ok(func)
}

fn alloc_rooted_symbol(
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  description: &str,
) -> Result<GcSymbol, VmError> {
  let desc_string = scope.alloc_string(description)?;
  let sym = scope.new_symbol(Some(desc_string))?;
  roots.push(scope.heap_mut().add_root(Value::Symbol(sym))?);
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

fn install_object_static_method(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  function_prototype: GcObject,
  object_constructor: GcObject,
  name: &str,
  length: u32,
  call: crate::vm::NativeCall,
) -> Result<(), VmError> {
  let call_id = vm.register_native_call(call)?;
  let name_string = scope.alloc_string(name)?;
  let func = alloc_rooted_native_function(scope, roots, call_id, None, name_string, length)?;
  scope
    .heap_mut()
    .object_set_prototype(func, Some(function_prototype))?;

  scope.define_property(
    object_constructor,
    PropertyKey::from_string(name_string),
    data_desc(Value::Object(func), true, false, true),
  )?;
  Ok(())
}

fn install_object_static_methods(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  roots: &mut Vec<RootId>,
  function_prototype: GcObject,
  object_constructor: GcObject,
) -> Result<(), VmError> {
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "defineProperty",
    3,
    builtins::object_define_property,
  )?;
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "create",
    2,
    builtins::object_create,
  )?;
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "keys",
    1,
    builtins::object_keys,
  )?;
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "assign",
    2,
    builtins::object_assign,
  )?;
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "getPrototypeOf",
    1,
    builtins::object_get_prototype_of,
  )?;
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "setPrototypeOf",
    2,
    builtins::object_set_prototype_of,
  )?;
  Ok(())
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

    let function_prototype_call = vm.register_native_call(builtins::function_prototype_call)?;
    // ECMA-262: %Function.prototype% has a "name" property whose value is the empty String.
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

    let string_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(string_prototype, Some(object_prototype))?;

    let number_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(number_prototype, Some(object_prototype))?;

    let boolean_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(boolean_prototype, Some(object_prototype))?;

    let bigint_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(bigint_prototype, Some(object_prototype))?;

    let date_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(date_prototype, Some(object_prototype))?;

    let symbol_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(symbol_prototype, Some(object_prototype))?;

    // --- Common property keys used throughout the intrinsic graph ---
    //
    // Root these key strings for the duration of intrinsic initialization: subsequent allocations
    // may trigger GC before we store the keys on any rooted object.
    let constructor_key_s = scope.alloc_string("constructor")?;
    scope.push_root(Value::String(constructor_key_s))?;
    let prototype_key_s = scope.alloc_string("prototype")?;
    scope.push_root(Value::String(prototype_key_s))?;
    let name_key_s = scope.alloc_string("name")?;
    scope.push_root(Value::String(name_key_s))?;
    let length_key_s = scope.alloc_string("length")?;
    scope.push_root(Value::String(length_key_s))?;

    let common = CommonKeys {
      constructor: PropertyKey::from_string(constructor_key_s),
      prototype: PropertyKey::from_string(prototype_key_s),
      name: PropertyKey::from_string(name_key_s),
      length: PropertyKey::from_string(length_key_s),
    };

    // --- Prototype/native method call handlers ---
    let object_prototype_to_string = vm.register_native_call(builtins::object_prototype_to_string)?;
    let function_prototype_call_method =
      vm.register_native_call(builtins::function_prototype_call_method)?;
    let function_prototype_apply_method =
      vm.register_native_call(builtins::function_prototype_apply)?;
    let function_prototype_bind_method =
      vm.register_native_call(builtins::function_prototype_bind)?;
    let array_prototype_map = vm.register_native_call(builtins::array_prototype_map)?;
    let array_prototype_join = vm.register_native_call(builtins::array_prototype_join)?;
    let string_prototype_to_string = vm.register_native_call(builtins::string_prototype_to_string)?;
    let number_prototype_value_of = vm.register_native_call(builtins::number_prototype_value_of)?;
    let boolean_prototype_value_of = vm.register_native_call(builtins::boolean_prototype_value_of)?;
    let bigint_prototype_value_of = vm.register_native_call(builtins::bigint_prototype_value_of)?;
    let date_prototype_to_string = vm.register_native_call(builtins::date_prototype_to_string)?;
    let date_prototype_value_of = vm.register_native_call(builtins::date_prototype_value_of)?;
    let date_prototype_to_primitive = vm.register_native_call(builtins::date_prototype_to_primitive)?;
    let symbol_prototype_value_of = vm.register_native_call(builtins::symbol_prototype_value_of)?;
    let error_prototype_to_string = vm.register_native_call(builtins::error_prototype_to_string)?;
    let json_stringify = vm.register_native_call(builtins::json_stringify)?;

    // `%Number%`, `%Boolean%`, `%Date%`, and global functions.
    let number_call = vm.register_native_call(builtins::number_constructor_call)?;
    let number_construct = vm.register_native_construct(builtins::number_constructor_construct)?;
    let boolean_call = vm.register_native_call(builtins::boolean_constructor_call)?;
    let boolean_construct = vm.register_native_construct(builtins::boolean_constructor_construct)?;
    let date_call = vm.register_native_call(builtins::date_constructor_call)?;
    let date_construct = vm.register_native_construct(builtins::date_constructor_construct)?;
    let is_nan_call = vm.register_native_call(builtins::global_is_nan)?;

    // --- Baseline constructors ---
    // `%Object%`
    let object_call = vm.register_native_call(builtins::object_constructor_call)?;
    let object_construct =
      vm.register_native_construct(builtins::object_constructor_construct)?;
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

    install_object_static_methods(vm, scope, roots, function_prototype, object_constructor)?;

      // Object.prototype.toString
      {
        let to_string_s = scope.alloc_string("toString")?;
        scope.push_root(Value::String(to_string_s))?;
        let key = PropertyKey::from_string(to_string_s);
        let func = scope.alloc_native_function(object_prototype_to_string, None, to_string_s, 0)?;
        scope.push_root(Value::Object(func))?;
        scope
          .heap_mut()
          .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        object_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // `%Function%`
    let function_call = vm.register_native_call(builtins::function_constructor_call)?;
    let function_construct =
      vm.register_native_construct(builtins::function_constructor_construct)?;
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

      // Function.prototype.call
      {
        let call_s = scope.alloc_string("call")?;
        scope.push_root(Value::String(call_s))?;
        let key = PropertyKey::from_string(call_s);
        let func =
          scope.alloc_native_function(function_prototype_call_method, None, call_s, 1)?;
        scope.push_root(Value::Object(func))?;
        scope
          .heap_mut()
          .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        function_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // Function.prototype.apply
    {
      let apply_s = scope.alloc_string("apply")?;
      scope.push_root(Value::String(apply_s))?;
      let key = PropertyKey::from_string(apply_s);
      let func =
        scope.alloc_native_function(function_prototype_apply_method, None, apply_s, 2)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        function_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // Function.prototype.bind
    {
      let bind_s = scope.alloc_string("bind")?;
      scope.push_root(Value::String(bind_s))?;
      let key = PropertyKey::from_string(bind_s);
      let func =
        scope.alloc_native_function(function_prototype_bind_method, None, bind_s, 1)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        function_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // `%Array%`
    let array_call = vm.register_native_call(builtins::array_constructor_call)?;
    let array_construct = vm.register_native_construct(builtins::array_constructor_construct)?;
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

      // Array.prototype.map / join
      {
        let map_s = scope.alloc_string("map")?;
        scope.push_root(Value::String(map_s))?;
        let map_key = PropertyKey::from_string(map_s);
        let map_fn = scope.alloc_native_function(array_prototype_map, None, map_s, 1)?;
        scope.push_root(Value::Object(map_fn))?;
        scope
          .heap_mut()
          .object_set_prototype(map_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        map_key,
        data_desc(Value::Object(map_fn), true, false, true),
      )?;

        let join_s = scope.alloc_string("join")?;
        scope.push_root(Value::String(join_s))?;
        let join_key = PropertyKey::from_string(join_s);
        let join_fn = scope.alloc_native_function(array_prototype_join, None, join_s, 1)?;
        scope.push_root(Value::Object(join_fn))?;
        scope
          .heap_mut()
          .object_set_prototype(join_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        join_key,
        data_desc(Value::Object(join_fn), true, false, true),
      )?;
    }

    // `%String%`
    let string_call = vm.register_native_call(builtins::string_constructor_call)?;
    let string_construct = vm.register_native_construct(builtins::string_constructor_construct)?;
    let string_name = scope.alloc_string("String")?;
    let string_constructor = alloc_rooted_native_function(
      scope,
      roots,
      string_call,
      Some(string_construct),
      string_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(string_constructor, Some(function_prototype))?;
    scope.define_property(
      string_constructor,
      common.prototype,
      data_desc(Value::Object(string_prototype), false, false, false),
    )?;
    scope.define_property(
      string_constructor,
      common.name,
      data_desc(Value::String(string_name), false, false, true),
    )?;
    scope.define_property(
      string_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      string_prototype,
      common.constructor,
      data_desc(Value::Object(string_constructor), true, false, true),
    )?;

      // String.prototype.toString
      {
        let to_string_s = scope.alloc_string("toString")?;
        scope.push_root(Value::String(to_string_s))?;
        let key = PropertyKey::from_string(to_string_s);
        let func =
          scope.alloc_native_function(string_prototype_to_string, None, to_string_s, 0)?;
        scope.push_root(Value::Object(func))?;
        scope
          .heap_mut()
          .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        string_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // `%Number%`
    let number_name = scope.alloc_string("Number")?;
    let number_constructor = alloc_rooted_native_function(
      scope,
      roots,
      number_call,
      Some(number_construct),
      number_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(number_constructor, Some(function_prototype))?;
    scope.define_property(
      number_constructor,
      common.prototype,
      data_desc(Value::Object(number_prototype), false, false, false),
    )?;
    scope.define_property(
      number_constructor,
      common.name,
      data_desc(Value::String(number_name), false, false, true),
    )?;
    scope.define_property(
      number_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      number_prototype,
      common.constructor,
      data_desc(Value::Object(number_constructor), true, false, true),
    )?;

    // Number.prototype.valueOf
    {
      let value_of_s = scope.alloc_string("valueOf")?;
      scope.push_root(Value::String(value_of_s))?;
      let key = PropertyKey::from_string(value_of_s);
      let func = scope.alloc_native_function(number_prototype_value_of, None, value_of_s, 0)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        number_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // Number static properties.
    {
      let cases: [(&str, Value); 5] = [
        ("NaN", Value::Number(f64::NAN)),
        ("POSITIVE_INFINITY", Value::Number(f64::INFINITY)),
        ("NEGATIVE_INFINITY", Value::Number(f64::NEG_INFINITY)),
        ("MAX_VALUE", Value::Number(f64::MAX)),
        // JS `Number.MIN_VALUE` is the smallest positive **subnormal** (`5e-324`), not
        // `f64::MIN_POSITIVE` (smallest positive normal).
        ("MIN_VALUE", Value::Number(f64::from_bits(1))),
      ];
      for (name, value) in cases {
        let key_s = scope.alloc_string(name)?;
        scope.push_root(Value::String(key_s))?;
        let key = PropertyKey::from_string(key_s);
        scope.define_property(number_constructor, key, data_desc(value, false, false, false))?;
      }
    }

    // `%Boolean%`
    let boolean_name = scope.alloc_string("Boolean")?;
    let boolean_constructor = alloc_rooted_native_function(
      scope,
      roots,
      boolean_call,
      Some(boolean_construct),
      boolean_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(boolean_constructor, Some(function_prototype))?;
    scope.define_property(
      boolean_constructor,
      common.prototype,
      data_desc(Value::Object(boolean_prototype), false, false, false),
    )?;
    scope.define_property(
      boolean_constructor,
      common.name,
      data_desc(Value::String(boolean_name), false, false, true),
    )?;
    scope.define_property(
      boolean_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      boolean_prototype,
      common.constructor,
      data_desc(Value::Object(boolean_constructor), true, false, true),
    )?;

    // Boolean.prototype.valueOf
    {
      let value_of_s = scope.alloc_string("valueOf")?;
      scope.push_root(Value::String(value_of_s))?;
      let key = PropertyKey::from_string(value_of_s);
      let func = scope.alloc_native_function(boolean_prototype_value_of, None, value_of_s, 0)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        boolean_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // BigInt.prototype.valueOf
    {
      let value_of_s = scope.alloc_string("valueOf")?;
      scope.push_root(Value::String(value_of_s))?;
      let key = PropertyKey::from_string(value_of_s);
      let func = scope.alloc_native_function(bigint_prototype_value_of, None, value_of_s, 0)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        bigint_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // `%Date%`
    let date_name = scope.alloc_string("Date")?;
    let date_constructor = alloc_rooted_native_function(
      scope,
      roots,
      date_call,
      Some(date_construct),
      date_name,
      7,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(date_constructor, Some(function_prototype))?;
    scope.define_property(
      date_constructor,
      common.prototype,
      data_desc(Value::Object(date_prototype), false, false, false),
    )?;
    scope.define_property(
      date_constructor,
      common.name,
      data_desc(Value::String(date_name), false, false, true),
    )?;
    scope.define_property(
      date_constructor,
      common.length,
      data_desc(Value::Number(7.0), false, false, true),
    )?;
    scope.define_property(
      date_prototype,
      common.constructor,
      data_desc(Value::Object(date_constructor), true, false, true),
    )?;

    // Date.prototype.toString / valueOf / @@toPrimitive
    {
      let to_string_s = scope.alloc_string("toString")?;
      scope.push_root(Value::String(to_string_s))?;
      let to_string_key = PropertyKey::from_string(to_string_s);
      let to_string_fn = scope.alloc_native_function(date_prototype_to_string, None, to_string_s, 0)?;
      scope.push_root(Value::Object(to_string_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(to_string_fn, Some(function_prototype))?;
      scope.define_property(
        date_prototype,
        to_string_key,
        data_desc(Value::Object(to_string_fn), true, false, true),
      )?;

      let value_of_s = scope.alloc_string("valueOf")?;
      scope.push_root(Value::String(value_of_s))?;
      let value_of_key = PropertyKey::from_string(value_of_s);
      let value_of_fn = scope.alloc_native_function(date_prototype_value_of, None, value_of_s, 0)?;
      scope.push_root(Value::Object(value_of_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(value_of_fn, Some(function_prototype))?;
      scope.define_property(
        date_prototype,
        value_of_key,
        data_desc(Value::Object(value_of_fn), true, false, true),
      )?;

      let to_prim_s = scope.alloc_string("[Symbol.toPrimitive]")?;
      scope.push_root(Value::String(to_prim_s))?;
      let to_prim_fn =
        scope.alloc_native_function(date_prototype_to_primitive, None, to_prim_s, 1)?;
      scope.push_root(Value::Object(to_prim_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(to_prim_fn, Some(function_prototype))?;
      scope.define_property(
        date_prototype,
        PropertyKey::Symbol(well_known_symbols.to_primitive),
        data_desc(Value::Object(to_prim_fn), true, false, true),
      )?;
    }

    // `%isNaN%` (global function)
    let is_nan_name = scope.alloc_string("isNaN")?;
    let is_nan = alloc_rooted_native_function(scope, roots, is_nan_call, None, is_nan_name, 1)?;
    scope
      .heap_mut()
      .object_set_prototype(is_nan, Some(function_prototype))?;

    // `%Symbol%`
    let symbol_call = vm.register_native_call(builtins::symbol_constructor_call)?;
    let symbol_name = scope.alloc_string("Symbol")?;
    let symbol_constructor =
      alloc_rooted_native_function(scope, roots, symbol_call, None, symbol_name, 1)?;
    scope
      .heap_mut()
      .object_set_prototype(symbol_constructor, Some(function_prototype))?;
    scope.define_property(
      symbol_constructor,
      common.prototype,
      data_desc(Value::Object(symbol_prototype), false, false, false),
    )?;
    scope.define_property(
      symbol_constructor,
      common.name,
      data_desc(Value::String(symbol_name), false, false, true),
    )?;
    scope.define_property(
      symbol_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      symbol_prototype,
      common.constructor,
      data_desc(Value::Object(symbol_constructor), true, false, true),
    )?;

    // Symbol.prototype.valueOf
    {
      let value_of_s = scope.alloc_string("valueOf")?;
      scope.push_root(Value::String(value_of_s))?;
      let key = PropertyKey::from_string(value_of_s);
      let func = scope.alloc_native_function(symbol_prototype_value_of, None, value_of_s, 0)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        symbol_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

    // Install well-known symbols as properties on the global `Symbol` constructor.
    {
      let wks = &well_known_symbols;
      let cases = [
        ("asyncIterator", wks.async_iterator),
        ("hasInstance", wks.has_instance),
        ("isConcatSpreadable", wks.is_concat_spreadable),
        ("iterator", wks.iterator),
        ("match", wks.match_),
        ("matchAll", wks.match_all),
        ("replace", wks.replace),
        ("search", wks.search),
        ("species", wks.species),
        ("split", wks.split),
        ("toPrimitive", wks.to_primitive),
        ("toStringTag", wks.to_string_tag),
        ("unscopables", wks.unscopables),
      ];
      for (name, sym) in cases {
        let key_s = scope.alloc_string(name)?;
        scope.push_root(Value::String(key_s))?;
        let key = PropertyKey::from_string(key_s);
        scope.define_property(
          symbol_constructor,
          key,
          data_desc(Value::Symbol(sym), false, false, false),
        )?;
      }
    }

    // `%JSON%`
    let json = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(json, Some(object_prototype))?;
    {
      let stringify_s = scope.alloc_string("stringify")?;
      scope.push_root(Value::String(stringify_s))?;
      let key = PropertyKey::from_string(stringify_s);
      let func = scope.alloc_native_function(json_stringify, None, stringify_s, 1)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(json, key, data_desc(Value::Object(func), true, false, true))?;
    }

    // --- Error + subclasses ---
    let error_call = vm.register_native_call(builtins::error_constructor_call)?;
    let error_construct = vm.register_native_construct(builtins::error_constructor_construct)?;
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

    // Error.prototype.toString
    {
      let to_string_s = scope.alloc_string("toString")?;
      scope.push_root(Value::String(to_string_s))?;
      let key = PropertyKey::from_string(to_string_s);
      let func = scope.alloc_native_function(error_prototype_to_string, None, to_string_s, 0)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        error_prototype,
        key,
        data_desc(Value::Object(func), true, false, true),
      )?;
    }

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

    // --- Promise ---
    let promise_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(promise_prototype, Some(object_prototype))?;

    let promise_resolving_function_call =
      vm.register_native_call(builtins::promise_resolving_function_call)?;
    let promise_finally_handler_call =
      vm.register_native_call(builtins::promise_finally_handler_call)?;
    let promise_finally_thunk_call =
      vm.register_native_call(builtins::promise_finally_thunk_call)?;

    let promise_call = vm.register_native_call(builtins::promise_constructor_call)?;
    let promise_construct = vm.register_native_construct(builtins::promise_constructor_construct)?;
    let promise_name = scope.alloc_string("Promise")?;
    let promise = alloc_rooted_native_function(
      scope,
      roots,
      promise_call,
      Some(promise_construct),
      promise_name,
      1,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(promise, Some(function_prototype))?;

    // Promise.prototype.constructor
    scope.define_property(
      promise_prototype,
      common.constructor,
      data_desc(Value::Object(promise), true, false, true),
    )?;

    // Promise.prototype on the constructor.
    scope.define_property(
      promise,
      common.prototype,
      data_desc(Value::Object(promise_prototype), true, false, false),
    )?;

    // Promise.name / Promise.length
    scope.define_property(
      promise,
      common.name,
      data_desc(Value::String(promise_name), false, false, true),
    )?;
    scope.define_property(
      promise,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;

    // Promise[@@species]
    //
    // Spec: `get Promise [ @@species ]` (ECMA-262).
    //
    // The getter returns the receiver and is used by `SpeciesConstructor`.
    let promise_species_call = vm.register_native_call(builtins::promise_species_get)?;
    let promise_species_name = scope.alloc_string("get [Symbol.species]")?;
    let promise_species_getter = alloc_rooted_native_function(
      scope,
      roots,
      promise_species_call,
      None,
      promise_species_name,
      0,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(promise_species_getter, Some(function_prototype))?;
    scope.define_property(
      promise,
      PropertyKey::Symbol(well_known_symbols.species),
      PropertyDescriptor {
        enumerable: false,
        configurable: true,
        kind: PropertyKind::Accessor {
          get: Value::Object(promise_species_getter),
          set: Value::Undefined,
        },
      },
    )?;

    // Promise.resolve / Promise.reject
    {
      let resolve_call = vm.register_native_call(builtins::promise_resolve)?;
      let resolve_name = scope.alloc_string("resolve")?;
      let resolve = alloc_rooted_native_function(scope, roots, resolve_call, None, resolve_name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(resolve, Some(function_prototype))?;

      let key = PropertyKey::from_string(scope.alloc_string("resolve")?);
      scope.define_property(
        promise,
        key,
        data_desc(Value::Object(resolve), true, false, true),
      )?;

      let reject_call = vm.register_native_call(builtins::promise_reject)?;
      let reject_name = scope.alloc_string("reject")?;
      let reject = alloc_rooted_native_function(scope, roots, reject_call, None, reject_name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(reject, Some(function_prototype))?;

      let key = PropertyKey::from_string(scope.alloc_string("reject")?);
      scope.define_property(
        promise,
        key,
        data_desc(Value::Object(reject), true, false, true),
      )?;
    }

    // Promise.try / Promise.withResolvers
    {
      let try_call = vm.register_native_call(builtins::promise_try)?;
      let try_name = scope.alloc_string("try")?;
      let try_ = alloc_rooted_native_function(scope, roots, try_call, None, try_name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(try_, Some(function_prototype))?;
      let key = PropertyKey::from_string(scope.alloc_string("try")?);
      scope.define_property(promise, key, data_desc(Value::Object(try_), true, false, true))?;

      let with_resolvers_call = vm.register_native_call(builtins::promise_with_resolvers)?;
      let with_resolvers_name = scope.alloc_string("withResolvers")?;
      let with_resolvers = alloc_rooted_native_function(
        scope,
        roots,
        with_resolvers_call,
        None,
        with_resolvers_name,
        0,
      )?;
      scope
        .heap_mut()
        .object_set_prototype(with_resolvers, Some(function_prototype))?;
      let key = PropertyKey::from_string(scope.alloc_string("withResolvers")?);
      scope.define_property(
        promise,
        key,
        data_desc(Value::Object(with_resolvers), true, false, true),
      )?;
    }

    // Promise.prototype.then / Promise.prototype.catch / Promise.prototype.finally / @@toStringTag
    {
      let then_call = vm.register_native_call(builtins::promise_prototype_then)?;
      let then_name = scope.alloc_string("then")?;
      let then = alloc_rooted_native_function(scope, roots, then_call, None, then_name, 2)?;
      scope
        .heap_mut()
        .object_set_prototype(then, Some(function_prototype))?;

      let key = PropertyKey::from_string(scope.alloc_string("then")?);
      scope.define_property(
        promise_prototype,
        key,
        data_desc(Value::Object(then), true, false, true),
      )?;

      let catch_call = vm.register_native_call(builtins::promise_prototype_catch)?;
      let catch_name = scope.alloc_string("catch")?;
      let catch_ = alloc_rooted_native_function(scope, roots, catch_call, None, catch_name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(catch_, Some(function_prototype))?;

      let key = PropertyKey::from_string(scope.alloc_string("catch")?);
      scope.define_property(
        promise_prototype,
        key,
        data_desc(Value::Object(catch_), true, false, true),
      )?;

      let finally_call = vm.register_native_call(builtins::promise_prototype_finally)?;
      let finally_name = scope.alloc_string("finally")?;
      let finally_ = alloc_rooted_native_function(scope, roots, finally_call, None, finally_name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(finally_, Some(function_prototype))?;
      let key = PropertyKey::from_string(scope.alloc_string("finally")?);
      scope.define_property(
        promise_prototype,
        key,
        data_desc(Value::Object(finally_), true, false, true),
      )?;

      let to_string_tag_value = scope.alloc_string("Promise")?;
      scope.define_property(
        promise_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(to_string_tag_value), false, false, true),
      )?;
    }
    Ok(Self {
      well_known_symbols,
      object_prototype,
      function_prototype,
      array_prototype,
      string_prototype,
      number_prototype,
      boolean_prototype,
      bigint_prototype,
      date_prototype,
      symbol_prototype,
      object_constructor,
      function_constructor,
      array_constructor,
      string_constructor,
      number_constructor,
      boolean_constructor,
      date_constructor,
      symbol_constructor,
      is_nan,
      json,
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

      promise,
      promise_prototype,
      promise_resolving_function_call,
      promise_finally_handler_call,
      promise_finally_thunk_call,
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

  pub fn string_prototype(&self) -> GcObject {
    self.string_prototype
  }

  pub fn number_prototype(&self) -> GcObject {
    self.number_prototype
  }

  pub fn boolean_prototype(&self) -> GcObject {
    self.boolean_prototype
  }

  pub fn bigint_prototype(&self) -> GcObject {
    self.bigint_prototype
  }

  pub fn date_prototype(&self) -> GcObject {
    self.date_prototype
  }

  pub fn symbol_prototype(&self) -> GcObject {
    self.symbol_prototype
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

  pub fn string_constructor(&self) -> GcObject {
    self.string_constructor
  }

  pub fn number_constructor(&self) -> GcObject {
    self.number_constructor
  }

  pub fn boolean_constructor(&self) -> GcObject {
    self.boolean_constructor
  }

  pub fn date_constructor(&self) -> GcObject {
    self.date_constructor
  }

  pub fn symbol_constructor(&self) -> GcObject {
    self.symbol_constructor
  }

  pub fn is_nan(&self) -> GcObject {
    self.is_nan
  }

  pub fn json(&self) -> GcObject {
    self.json
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

  pub fn promise(&self) -> GcObject {
    self.promise
  }

  pub fn promise_prototype(&self) -> GcObject {
    self.promise_prototype
  }

  pub(crate) fn promise_resolving_function_call(&self) -> NativeFunctionId {
    self.promise_resolving_function_call
  }

  pub(crate) fn promise_finally_handler_call(&self) -> NativeFunctionId {
    self.promise_finally_handler_call
  }

  pub(crate) fn promise_finally_thunk_call(&self) -> NativeFunctionId {
    self.promise_finally_thunk_call
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
