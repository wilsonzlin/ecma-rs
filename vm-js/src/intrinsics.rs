use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::{
  builtins, GcObject, GcString, GcSymbol, NativeConstructId, NativeFunctionId, RootId, Scope,
  Value, Vm, VmError,
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
  regexp_prototype: GcObject,
  symbol_prototype: GcObject,
  object_constructor: GcObject,
  function_constructor: GcObject,
  array_constructor: GcObject,
  string_constructor: GcObject,
  number_constructor: GcObject,
  boolean_constructor: GcObject,
  date_constructor: GcObject,
  regexp_constructor: GcObject,
  symbol_constructor: GcObject,
  proxy_constructor: GcObject,
  map_constructor: GcObject,
  map_prototype: GcObject,
  map_iterator_prototype: GcObject,
  set_constructor: GcObject,
  set_prototype: GcObject,
  set_iterator_prototype: GcObject,
  weakmap_constructor: GcObject,
  weakmap_prototype: GcObject,
  weakset_constructor: GcObject,
  weakset_prototype: GcObject,
  bigint_constructor: GcObject,
  /// `%eval%` (ECMA-262 §19.2.1) — installed on the global object; Evaluator intercepts
  /// calls for PerformEval (direct vs indirect).
  eval: GcObject,
  is_nan: GcObject,
  is_finite: GcObject,
  parse_int: GcObject,
  parse_float: GcObject,
  math: GcObject,
  json: GcObject,
  reflect: GcObject,

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
  promise_capability_executor_call: NativeFunctionId,
  promise_resolving_function_call: NativeFunctionId,
  promise_finally_handler_call: NativeFunctionId,
  promise_finally_thunk_call: NativeFunctionId,
  promise_all_resolve_element_call: NativeFunctionId,
  promise_all_settled_element_call: NativeFunctionId,
  promise_any_reject_element_call: NativeFunctionId,

  iterator_prototype: GcObject,
  array_iterator_prototype: GcObject,
  string_iterator_prototype: GcObject,
  async_iterator_prototype: GcObject,
  async_from_sync_iterator_prototype: GcObject,
  generator_prototype: GcObject,
  generator_function_prototype: GcObject,
  async_generator_prototype: GcObject,
  async_generator_function_prototype: GcObject,
  async_function_prototype: GcObject,
  await_continuation_call: NativeFunctionId,
  /// `MakeArgGetter` for mapped `arguments` exotic objects (ECMA-262 §10.4.4.7.1).
  arguments_arg_getter_call: NativeFunctionId,
  /// `MakeArgSetter` for mapped `arguments` exotic objects (ECMA-262 §10.4.4.7.2).
  arguments_arg_setter_call: NativeFunctionId,
  /// `[[Call]]` for class constructors (throws TypeError).
  class_constructor_call: NativeFunctionId,
  /// Default base-class `[[Construct]]` (`constructor() {}`).
  class_default_construct: NativeConstructId,
  /// Default derived-class `[[Construct]]` (`constructor(...args) { super(...args); }`).
  class_default_derived_construct: NativeConstructId,
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

/// Defines a native prototype method: a writable, non-enumerable, configurable data property
/// holding a native function whose `[[Prototype]]` is `Function.prototype` (the standard shape for
/// built-in prototype methods).
fn define_prototype_method(
  scope: &mut Scope<'_>,
  prototype: GcObject,
  function_prototype: GcObject,
  name: &str,
  call: NativeFunctionId,
  length: u32,
) -> Result<(), VmError> {
  let name_s = scope.alloc_string(name)?;
  scope.push_root(Value::String(name_s))?;
  let key = PropertyKey::from_string(name_s);
  let func = scope.alloc_native_function(call, None, name_s, length)?;
  scope.push_root(Value::Object(func))?;
  scope
    .heap_mut()
    .object_set_prototype(func, Some(function_prototype))?;
  scope.define_property(
    prototype,
    key,
    data_desc(Value::Object(func), true, false, true),
  )?;
  Ok(())
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

  let constructor =
    alloc_rooted_native_function(scope, roots, call, Some(construct), name_string, length)?;
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
    "defineProperties",
    2,
    builtins::object_define_properties,
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
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "preventExtensions",
    1,
    builtins::object_prevent_extensions,
  )?;
  install_object_static_method(
    vm,
    scope,
    roots,
    function_prototype,
    object_constructor,
    "isExtensible",
    1,
    builtins::object_is_extensible,
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
    // §21.1.3: `Number.prototype` is itself a Number object with [[NumberData]] = +0.
    builtins::install_wrapper_prototype_data(scope, number_prototype, Value::Number(0.0))?;

    let boolean_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(boolean_prototype, Some(object_prototype))?;
    // §20.3.3: `Boolean.prototype` is itself a Boolean object with [[BooleanData]] = false.
    builtins::install_wrapper_prototype_data(scope, boolean_prototype, Value::Bool(false))?;

    let bigint_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(bigint_prototype, Some(object_prototype))?;

    let date_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(date_prototype, Some(object_prototype))?;

    let regexp_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(regexp_prototype, Some(object_prototype))?;

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
    let object_prototype_to_string =
      vm.register_native_call(builtins::object_prototype_to_string)?;
    let object_prototype_value_of = vm.register_native_call(builtins::object_prototype_value_of)?;
    let function_prototype_call_method =
      vm.register_native_call(builtins::function_prototype_call_method)?;
    let function_prototype_apply_method =
      vm.register_native_call(builtins::function_prototype_apply)?;
    let function_prototype_bind_method =
      vm.register_native_call(builtins::function_prototype_bind)?;
    let array_prototype_map = vm.register_native_call(builtins::array_prototype_map)?;
    let array_prototype_join = vm.register_native_call(builtins::array_prototype_join)?;
    let array_prototype_to_string = vm.register_native_call(builtins::array_prototype_to_string)?;
    let array_prototype_push = vm.register_native_call(builtins::array_prototype_push)?;
    let array_prototype_pop = vm.register_native_call(builtins::array_prototype_pop)?;
    let array_prototype_shift = vm.register_native_call(builtins::array_prototype_shift)?;
    let array_prototype_index_of = vm.register_native_call(builtins::array_prototype_index_of)?;
    let array_prototype_includes = vm.register_native_call(builtins::array_prototype_includes)?;
    let string_prototype_to_string =
      vm.register_native_call(builtins::string_prototype_to_string)?;
    let string_prototype_value_of = vm.register_native_call(builtins::string_prototype_value_of)?;
    let string_prototype_char_at = vm.register_native_call(builtins::string_prototype_char_at)?;
    let string_prototype_char_code_at =
      vm.register_native_call(builtins::string_prototype_char_code_at)?;
    let string_prototype_index_of = vm.register_native_call(builtins::string_prototype_index_of)?;
    let string_prototype_includes = vm.register_native_call(builtins::string_prototype_includes)?;
    let string_prototype_slice = vm.register_native_call(builtins::string_prototype_slice)?;
    let string_prototype_substring =
      vm.register_native_call(builtins::string_prototype_substring)?;
    let string_prototype_concat = vm.register_native_call(builtins::string_prototype_concat)?;
    let string_prototype_to_upper_case =
      vm.register_native_call(builtins::string_prototype_to_upper_case)?;
    let string_prototype_to_lower_case =
      vm.register_native_call(builtins::string_prototype_to_lower_case)?;
    let number_prototype_to_string =
      vm.register_native_call(builtins::number_prototype_to_string)?;
    let number_prototype_to_fixed = vm.register_native_call(builtins::number_prototype_to_fixed)?;
    let number_prototype_to_exponential =
      vm.register_native_call(builtins::number_prototype_to_exponential)?;
    let number_prototype_to_precision =
      vm.register_native_call(builtins::number_prototype_to_precision)?;
    let number_prototype_to_locale_string =
      vm.register_native_call(builtins::number_prototype_to_locale_string)?;
    let string_prototype_split = vm.register_native_call(builtins::string_prototype_split)?;
    let boolean_prototype_to_string =
      vm.register_native_call(builtins::boolean_prototype_to_string)?;
    let number_prototype_value_of = vm.register_native_call(builtins::number_prototype_value_of)?;
    let boolean_prototype_value_of =
      vm.register_native_call(builtins::boolean_prototype_value_of)?;
    let array_is_array = vm.register_native_call(builtins::array_is_array)?;
    let bigint_prototype_value_of = vm.register_native_call(builtins::bigint_prototype_value_of)?;
    let date_prototype_to_string = vm.register_native_call(builtins::date_prototype_to_string)?;
    let date_prototype_value_of = vm.register_native_call(builtins::date_prototype_value_of)?;
    let date_prototype_to_primitive =
      vm.register_native_call(builtins::date_prototype_to_primitive)?;
    let symbol_prototype_value_of = vm.register_native_call(builtins::symbol_prototype_value_of)?;
    let error_prototype_to_string = vm.register_native_call(builtins::error_prototype_to_string)?;
    let json_stringify = vm.register_native_call(builtins::json_stringify)?;

    // `%Number%`, `%Boolean%`, `%Date%`, and global functions.
    let number_call = vm.register_native_call(builtins::number_constructor_call)?;
    let number_construct = vm.register_native_construct(builtins::number_constructor_construct)?;
    let boolean_call = vm.register_native_call(builtins::boolean_constructor_call)?;
    let boolean_construct =
      vm.register_native_construct(builtins::boolean_constructor_construct)?;
    let date_call = vm.register_native_call(builtins::date_constructor_call)?;
    let date_construct = vm.register_native_construct(builtins::date_constructor_construct)?;
    let regexp_call = vm.register_native_call(builtins::regexp_constructor_call)?;
    let regexp_construct = vm.register_native_construct(builtins::regexp_constructor_construct)?;
    let is_nan_call = vm.register_native_call(builtins::global_is_nan)?;

    // --- Baseline constructors ---
    // `%Object%`
    let object_call = vm.register_native_call(builtins::object_constructor_call)?;
    let object_construct = vm.register_native_construct(builtins::object_constructor_construct)?;
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

    // Object.prototype.toString / valueOf
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
    define_prototype_method(
      scope,
      object_prototype,
      function_prototype,
      "valueOf",
      object_prototype_value_of,
      0,
    )?;

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
      let func = scope.alloc_native_function(function_prototype_call_method, None, call_s, 1)?;
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
      let func = scope.alloc_native_function(function_prototype_apply_method, None, apply_s, 2)?;
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
      let func = scope.alloc_native_function(function_prototype_bind_method, None, bind_s, 1)?;
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

    // Array.isArray (§23.1.2.2) — high-leverage harness helper (test262 `assert(Array.isArray)`).
    {
      let name_s = scope.alloc_string("isArray")?;
      scope.push_root(Value::String(name_s))?;
      let func = scope.alloc_native_function(array_is_array, None, name_s, 1)?;
      scope.push_root(Value::Object(func))?;
      scope
        .heap_mut()
        .object_set_prototype(func, Some(function_prototype))?;
      scope.define_property(
        array_constructor,
        PropertyKey::from_string(name_s),
        data_desc(Value::Object(func), true, false, true),
      )?;
    }
    // Array.from (§23.1.2.1) — iterable path (Map.groupBy / compareArray helpers).
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      array_constructor,
      "from",
      1,
      builtins::array_from,
    )?;

    // Array.prototype.map / join / toString / push
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

      let to_string_s = scope.alloc_string("toString")?;
      scope.push_root(Value::String(to_string_s))?;
      let to_string_key = PropertyKey::from_string(to_string_s);
      let to_string_fn =
        scope.alloc_native_function(array_prototype_to_string, None, to_string_s, 0)?;
      scope.push_root(Value::Object(to_string_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(to_string_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        to_string_key,
        data_desc(Value::Object(to_string_fn), true, false, true),
      )?;

      let push_s = scope.alloc_string("push")?;
      scope.push_root(Value::String(push_s))?;
      let push_key = PropertyKey::from_string(push_s);
      let push_fn = scope.alloc_native_function(array_prototype_push, None, push_s, 1)?;
      scope.push_root(Value::Object(push_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(push_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        push_key,
        data_desc(Value::Object(push_fn), true, false, true),
      )?;

      let pop_s = scope.alloc_string("pop")?;
      scope.push_root(Value::String(pop_s))?;
      let pop_key = PropertyKey::from_string(pop_s);
      let pop_fn = scope.alloc_native_function(array_prototype_pop, None, pop_s, 0)?;
      scope.push_root(Value::Object(pop_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(pop_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        pop_key,
        data_desc(Value::Object(pop_fn), true, false, true),
      )?;

      let shift_s = scope.alloc_string("shift")?;
      scope.push_root(Value::String(shift_s))?;
      let shift_key = PropertyKey::from_string(shift_s);
      let shift_fn = scope.alloc_native_function(array_prototype_shift, None, shift_s, 0)?;
      scope.push_root(Value::Object(shift_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(shift_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        shift_key,
        data_desc(Value::Object(shift_fn), true, false, true),
      )?;

      let index_of_s = scope.alloc_string("indexOf")?;
      scope.push_root(Value::String(index_of_s))?;
      let index_of_key = PropertyKey::from_string(index_of_s);
      let index_of_fn =
        scope.alloc_native_function(array_prototype_index_of, None, index_of_s, 1)?;
      scope.push_root(Value::Object(index_of_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(index_of_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        index_of_key,
        data_desc(Value::Object(index_of_fn), true, false, true),
      )?;

      let includes_s = scope.alloc_string("includes")?;
      scope.push_root(Value::String(includes_s))?;
      let includes_key = PropertyKey::from_string(includes_s);
      let includes_fn =
        scope.alloc_native_function(array_prototype_includes, None, includes_s, 1)?;
      scope.push_root(Value::Object(includes_fn))?;
      scope
        .heap_mut()
        .object_set_prototype(includes_fn, Some(function_prototype))?;
      scope.define_property(
        array_prototype,
        includes_key,
        data_desc(Value::Object(includes_fn), true, false, true),
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
      let func = scope.alloc_native_function(string_prototype_to_string, None, to_string_s, 0)?;
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

    // String.prototype methods needed for primitive autoboxing (§22.1.3).
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "valueOf",
      string_prototype_value_of,
      0,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "charAt",
      string_prototype_char_at,
      1,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "charCodeAt",
      string_prototype_char_code_at,
      1,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "indexOf",
      string_prototype_index_of,
      1,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "includes",
      string_prototype_includes,
      1,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "slice",
      string_prototype_slice,
      2,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "substring",
      string_prototype_substring,
      2,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "concat",
      string_prototype_concat,
      1,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "toUpperCase",
      string_prototype_to_upper_case,
      0,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "toLowerCase",
      string_prototype_to_lower_case,
      0,
    )?;
    define_prototype_method(
      scope,
      string_prototype,
      function_prototype,
      "split",
      string_prototype_split,
      2,
    )?;

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

    // Number.prototype methods needed for primitive autoboxing (§21.1.3).
    define_prototype_method(
      scope,
      number_prototype,
      function_prototype,
      "toString",
      number_prototype_to_string,
      1,
    )?;
    define_prototype_method(
      scope,
      number_prototype,
      function_prototype,
      "toFixed",
      number_prototype_to_fixed,
      1,
    )?;
    define_prototype_method(
      scope,
      number_prototype,
      function_prototype,
      "toExponential",
      number_prototype_to_exponential,
      1,
    )?;
    define_prototype_method(
      scope,
      number_prototype,
      function_prototype,
      "toPrecision",
      number_prototype_to_precision,
      1,
    )?;
    define_prototype_method(
      scope,
      number_prototype,
      function_prototype,
      "toLocaleString",
      number_prototype_to_locale_string,
      0,
    )?;

    // Number static properties (§21.1.2).
    {
      let cases: [(&str, Value); 8] = [
        ("NaN", Value::Number(f64::NAN)),
        ("POSITIVE_INFINITY", Value::Number(f64::INFINITY)),
        ("NEGATIVE_INFINITY", Value::Number(f64::NEG_INFINITY)),
        ("MAX_VALUE", Value::Number(f64::MAX)),
        // JS `Number.MIN_VALUE` is the smallest positive **subnormal** (`5e-324`), not
        // `f64::MIN_POSITIVE` (smallest positive normal).
        ("MIN_VALUE", Value::Number(f64::from_bits(1))),
        // §21.1.2.6/8: the safe-integer bounds are ±(2^53 - 1).
        ("MAX_SAFE_INTEGER", Value::Number(9007199254740991.0)),
        ("MIN_SAFE_INTEGER", Value::Number(-9007199254740991.0)),
        // §21.1.2.1: `Number.EPSILON` is 2^-52.
        ("EPSILON", Value::Number(f64::EPSILON)),
      ];
      for (name, value) in cases {
        let key_s = scope.alloc_string(name)?;
        scope.push_root(Value::String(key_s))?;
        let key = PropertyKey::from_string(key_s);
        scope.define_property(
          number_constructor,
          key,
          data_desc(value, false, false, false),
        )?;
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

    // Boolean.prototype.toString (§20.3.3.3).
    define_prototype_method(
      scope,
      boolean_prototype,
      function_prototype,
      "toString",
      boolean_prototype_to_string,
      0,
    )?;

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

    // `%BigInt%` (§21.2.1) — not constructable.
    let bigint_call = vm.register_native_call(builtins::bigint_constructor_call)?;
    let bigint_name = scope.alloc_string("BigInt")?;
    let bigint_constructor =
      alloc_rooted_native_function(scope, roots, bigint_call, None, bigint_name, 1)?;
    scope
      .heap_mut()
      .object_set_prototype(bigint_constructor, Some(function_prototype))?;
    scope.define_property(
      bigint_constructor,
      common.prototype,
      data_desc(Value::Object(bigint_prototype), false, false, false),
    )?;
    scope.define_property(
      bigint_constructor,
      common.name,
      data_desc(Value::String(bigint_name), false, false, true),
    )?;
    scope.define_property(
      bigint_constructor,
      common.length,
      data_desc(Value::Number(1.0), false, false, true),
    )?;
    scope.define_property(
      bigint_prototype,
      common.constructor,
      data_desc(Value::Object(bigint_constructor), true, false, true),
    )?;

    // `%Date%`
    let date_name = scope.alloc_string("Date")?;
    let date_constructor =
      alloc_rooted_native_function(scope, roots, date_call, Some(date_construct), date_name, 7)?;
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
      let to_string_fn =
        scope.alloc_native_function(date_prototype_to_string, None, to_string_s, 0)?;
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
      let value_of_fn =
        scope.alloc_native_function(date_prototype_value_of, None, value_of_s, 0)?;
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

    // `%RegExp%` (minimal: callable/constructable for typeof/identity; no regex engine)
    let regexp_name = scope.alloc_string("RegExp")?;
    let regexp_constructor = alloc_rooted_native_function(
      scope,
      roots,
      regexp_call,
      Some(regexp_construct),
      regexp_name,
      2,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(regexp_constructor, Some(function_prototype))?;
    scope.define_property(
      regexp_constructor,
      common.prototype,
      data_desc(Value::Object(regexp_prototype), false, false, false),
    )?;
    scope.define_property(
      regexp_constructor,
      common.name,
      data_desc(Value::String(regexp_name), false, false, true),
    )?;
    scope.define_property(
      regexp_constructor,
      common.length,
      data_desc(Value::Number(2.0), false, false, true),
    )?;
    scope.define_property(
      regexp_prototype,
      common.constructor,
      data_desc(Value::Object(regexp_constructor), true, false, true),
    )?;
    {
      let tag = scope.alloc_string("RegExp")?;
      scope.define_property(
        regexp_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    // Minimal `RegExp.prototype.exec` — always returns `null` (no matching engine). Unblocks
    // typeof/null.js's `RegExp("0").exec("1")` check.
    {
      let exec = vm.register_native_call(builtins::regexp_prototype_exec)?;
      define_prototype_method(scope, regexp_prototype, function_prototype, "exec", exec, 1)?;
      let test = vm.register_native_call(builtins::regexp_prototype_test)?;
      define_prototype_method(scope, regexp_prototype, function_prototype, "test", test, 1)?;
    }

    // AddRestrictedFunctionProperties (%Function.prototype%, realm) — `caller`/`arguments`
    // accessors that throw TypeError (§10.2.4). Inherited by generator/async function objects.
    {
      let thrower_id = vm.register_native_call(builtins::throw_type_error_restricted)?;
      let thrower_name = scope.alloc_string("")?;
      scope.push_root(Value::String(thrower_name))?;
      let thrower = scope.alloc_native_function(thrower_id, None, thrower_name, 0)?;
      scope.push_root(Value::Object(thrower))?;
      scope
        .heap_mut()
        .object_set_prototype(thrower, Some(function_prototype))?;
      // Non-configurable / non-writable name+length is fine; accessors themselves are configurable.
      for prop in ["caller", "arguments"] {
        let key_s = scope.alloc_string(prop)?;
        scope.push_root(Value::String(key_s))?;
        scope.define_property(
          function_prototype,
          PropertyKey::from_string(key_s),
          PropertyDescriptor {
            enumerable: false,
            configurable: true,
            kind: PropertyKind::Accessor {
              get: Value::Object(thrower),
              set: Value::Object(thrower),
            },
          },
        )?;
      }
    }

    // `%Proxy%` (minimal exotic: typeof + [[Set]] trap + revocable).
    // Spec: Proxy is constructable but must NOT gain a `.prototype` via MakeConstructor.
    let proxy_name = scope.alloc_string("Proxy")?;
    let proxy_call = vm.register_native_call(crate::proxy::proxy_constructor_call)?;
    let proxy_construct_id =
      vm.register_native_construct(crate::proxy::proxy_constructor_construct)?;
    let proxy_constructor =
      alloc_rooted_native_function(scope, roots, proxy_call, None, proxy_name, 2)?;
    scope
      .heap_mut()
      .object_set_prototype(proxy_constructor, Some(function_prototype))?;
    scope
      .heap_mut()
      .set_function_construct_handler(proxy_constructor, proxy_construct_id)?;
    scope.define_property(
      proxy_constructor,
      common.name,
      data_desc(Value::String(proxy_name), false, false, true),
    )?;
    scope.define_property(
      proxy_constructor,
      common.length,
      data_desc(Value::Number(2.0), false, false, true),
    )?;
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      proxy_constructor,
      "revocable",
      2,
      crate::proxy::proxy_revocable,
    )?;

    // `%isNaN%` (global function)
    let is_nan_name = scope.alloc_string("isNaN")?;
    let is_nan = alloc_rooted_native_function(scope, roots, is_nan_call, None, is_nan_name, 1)?;
    scope
      .heap_mut()
      .object_set_prototype(is_nan, Some(function_prototype))?;

    // `%eval%` (§19.2.1) — Evaluator intercepts calls for PerformEval; the native
    // body is a fallback for exotic call paths (apply/bound) not yet routed.
    let eval_call = vm.register_native_call(builtins::global_eval_call)?;
    let eval_name = scope.alloc_string("eval")?;
    let eval = alloc_rooted_native_function(scope, roots, eval_call, None, eval_name, 1)?;
    scope
      .heap_mut()
      .object_set_prototype(eval, Some(function_prototype))?;

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
    // `Symbol.for` / `Symbol.keyFor` (needed by WeakMap/WeakSet CanBeHeldWeakly tests).
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      symbol_constructor,
      "for",
      1,
      builtins::symbol_for,
    )?;
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      symbol_constructor,
      "keyFor",
      1,
      builtins::symbol_key_for,
    )?;

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

    // `%Reflect%` (minimal: `construct` for new.target / optional-call tests)
    let reflect = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(reflect, Some(object_prototype))?;
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      reflect,
      "construct",
      2,
      builtins::reflect_construct,
    )?;
    {
      let tag = scope.alloc_string("Reflect")?;
      scope.define_property(
        reflect,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }

    // --- Object introspection: Object.prototype.hasOwnProperty + Object statics ---
    {
      let has_own = vm.register_native_call(builtins::object_prototype_has_own_property)?;
      define_prototype_method(
        scope,
        object_prototype,
        function_prototype,
        "hasOwnProperty",
        has_own,
        1,
      )?;
      let prop_enum = vm.register_native_call(builtins::object_prototype_property_is_enumerable)?;
      define_prototype_method(
        scope,
        object_prototype,
        function_prototype,
        "propertyIsEnumerable",
        prop_enum,
        1,
      )?;
      let is_proto = vm.register_native_call(builtins::object_prototype_is_prototype_of)?;
      define_prototype_method(
        scope,
        object_prototype,
        function_prototype,
        "isPrototypeOf",
        is_proto,
        1,
      )?;
    }
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      object_constructor,
      "getOwnPropertyDescriptor",
      2,
      builtins::object_get_own_property_descriptor,
    )?;
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      object_constructor,
      "getOwnPropertyNames",
      1,
      builtins::object_get_own_property_names,
    )?;

    // --- Number statics (§21.1.2) ---
    // `Number.isNaN`/`isFinite` are distinct from the global `isNaN`/`isFinite` (they do not coerce),
    // so they get their own function objects. `Number.parseInt`/`parseFloat`, by contrast, are the
    // *same object* as the global functions (§21.1.2.12/.13) and are wired up below.
    for (name, length, call) in [
      (
        "isNaN",
        1u32,
        builtins::number_is_nan as crate::vm::NativeCall,
      ),
      ("isFinite", 1, builtins::number_is_finite),
      ("isInteger", 1, builtins::number_is_integer),
      ("isSafeInteger", 1, builtins::number_is_safe_integer),
    ] {
      install_object_static_method(
        vm,
        scope,
        roots,
        function_prototype,
        number_constructor,
        name,
        length,
        call,
      )?;
    }

    // --- String.fromCharCode (§22.1.2.1) ---
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      string_constructor,
      "fromCharCode",
      1,
      builtins::string_from_char_code,
    )?;

    // --- Global numeric functions (§19.2) ---
    let parse_int = {
      let call = vm.register_native_call(builtins::global_parse_int)?;
      let name = scope.alloc_string("parseInt")?;
      let f = alloc_rooted_native_function(scope, roots, call, None, name, 2)?;
      scope
        .heap_mut()
        .object_set_prototype(f, Some(function_prototype))?;
      f
    };
    let parse_float = {
      let call = vm.register_native_call(builtins::global_parse_float)?;
      let name = scope.alloc_string("parseFloat")?;
      let f = alloc_rooted_native_function(scope, roots, call, None, name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(f, Some(function_prototype))?;
      f
    };
    let is_finite = {
      let call = vm.register_native_call(builtins::global_is_finite)?;
      let name = scope.alloc_string("isFinite")?;
      let f = alloc_rooted_native_function(scope, roots, call, None, name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(f, Some(function_prototype))?;
      f
    };

    // §21.1.2.12/.13: `Number.parseFloat`/`Number.parseInt` are the same function objects as the
    // global `parseFloat`/`parseInt`.
    {
      let key = PropertyKey::from_string(scope.alloc_string("parseInt")?);
      scope.define_property(
        number_constructor,
        key,
        data_desc(Value::Object(parse_int), true, false, true),
      )?;
      let key = PropertyKey::from_string(scope.alloc_string("parseFloat")?);
      scope.define_property(
        number_constructor,
        key,
        data_desc(Value::Object(parse_float), true, false, true),
      )?;
    }

    // --- Math (§21.3) ---
    let math = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(math, Some(object_prototype))?;
    {
      // §21.3.1 constant values (non-writable, non-enumerable, non-configurable).
      let constants: [(&str, f64); 8] = [
        ("E", std::f64::consts::E),
        ("LN10", std::f64::consts::LN_10),
        ("LN2", std::f64::consts::LN_2),
        ("LOG10E", std::f64::consts::LOG10_E),
        ("LOG2E", std::f64::consts::LOG2_E),
        ("PI", std::f64::consts::PI),
        ("SQRT1_2", std::f64::consts::FRAC_1_SQRT_2),
        ("SQRT2", std::f64::consts::SQRT_2),
      ];
      for (name, value) in constants {
        let key_s = scope.alloc_string(name)?;
        scope.push_root(Value::String(key_s))?;
        scope.define_property(
          math,
          PropertyKey::from_string(key_s),
          data_desc(Value::Number(value), false, false, false),
        )?;
      }

      // §21.3.2 function properties.
      let methods: [(&str, u32, crate::vm::NativeCall); 33] = [
        ("abs", 1, builtins::math_abs),
        ("floor", 1, builtins::math_floor),
        ("ceil", 1, builtins::math_ceil),
        ("round", 1, builtins::math_round),
        ("trunc", 1, builtins::math_trunc),
        ("sign", 1, builtins::math_sign),
        ("sqrt", 1, builtins::math_sqrt),
        ("cbrt", 1, builtins::math_cbrt),
        ("exp", 1, builtins::math_exp),
        ("expm1", 1, builtins::math_expm1),
        ("log", 1, builtins::math_log),
        ("log2", 1, builtins::math_log2),
        ("log10", 1, builtins::math_log10),
        ("log1p", 1, builtins::math_log1p),
        ("sin", 1, builtins::math_sin),
        ("cos", 1, builtins::math_cos),
        ("tan", 1, builtins::math_tan),
        ("asin", 1, builtins::math_asin),
        ("acos", 1, builtins::math_acos),
        ("atan", 1, builtins::math_atan),
        ("sinh", 1, builtins::math_sinh),
        ("cosh", 1, builtins::math_cosh),
        ("tanh", 1, builtins::math_tanh),
        ("asinh", 1, builtins::math_asinh),
        ("acosh", 1, builtins::math_acosh),
        ("atanh", 1, builtins::math_atanh),
        ("fround", 1, builtins::math_fround),
        ("clz32", 1, builtins::math_clz32),
        ("pow", 2, builtins::math_pow),
        ("atan2", 2, builtins::math_atan2),
        ("hypot", 2, builtins::math_hypot),
        ("max", 2, builtins::math_max),
        ("min", 2, builtins::math_min),
      ];
      for (name, length, call) in methods {
        install_object_static_method(
          vm,
          scope,
          roots,
          function_prototype,
          math,
          name,
          length,
          call,
        )?;
      }
      // `Math.random` (§21.3.2.27).
      install_object_static_method(
        vm,
        scope,
        roots,
        function_prototype,
        math,
        "random",
        0,
        builtins::math_random,
      )?;

      // §21.3.1.9: `Math[@@toStringTag]` is the String "Math".
      let tag = scope.alloc_string("Math")?;
      scope.define_property(
        math,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
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

    let promise_capability_executor_call =
      vm.register_native_call(builtins::promise_capability_executor_call)?;
    let promise_resolving_function_call =
      vm.register_native_call(builtins::promise_resolving_function_call)?;
    let promise_finally_handler_call =
      vm.register_native_call(builtins::promise_finally_handler_call)?;
    let promise_finally_thunk_call =
      vm.register_native_call(builtins::promise_finally_thunk_call)?;
    let promise_all_resolve_element_call =
      vm.register_native_call(builtins::promise_all_resolve_element_call)?;
    let promise_all_settled_element_call =
      vm.register_native_call(builtins::promise_all_settled_element_call)?;
    let promise_any_reject_element_call =
      vm.register_native_call(builtins::promise_any_reject_element_call)?;

    let promise_call = vm.register_native_call(builtins::promise_constructor_call)?;
    let promise_construct =
      vm.register_native_construct(builtins::promise_constructor_construct)?;
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
      let resolve =
        alloc_rooted_native_function(scope, roots, resolve_call, None, resolve_name, 1)?;
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
      scope.define_property(
        promise,
        key,
        data_desc(Value::Object(try_), true, false, true),
      )?;

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
      let finally_ =
        alloc_rooted_native_function(scope, roots, finally_call, None, finally_name, 1)?;
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

    // --- %IteratorPrototype% / generators / async functions ---
    let iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(iterator_prototype, Some(object_prototype))?;
    {
      // %IteratorPrototype%[@@iterator]() { return this; }
      let call = vm.register_native_call(crate::generator::iterator_prototype_iterator)?;
      let name = scope.alloc_string("[Symbol.iterator]")?;
      let f = alloc_rooted_native_function(scope, roots, call, None, name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(f, Some(function_prototype))?;
      scope.define_property(
        iterator_prototype,
        PropertyKey::Symbol(well_known_symbols.iterator),
        data_desc(Value::Object(f), true, false, true),
      )?;
    }

    // %ArrayIteratorPrototype% + Array.prototype.values / @@iterator
    let array_iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(array_iterator_prototype, Some(iterator_prototype))?;
    {
      let next_call = vm.register_native_call(crate::iterator::array_iterator_prototype_next)?;
      let next_name = scope.alloc_string("next")?;
      let next_fn = alloc_rooted_native_function(scope, roots, next_call, None, next_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(next_fn, Some(function_prototype))?;
      scope.define_property(
        array_iterator_prototype,
        PropertyKey::from_string(next_name),
        data_desc(Value::Object(next_fn), true, false, true),
      )?;

      let tag = scope.alloc_string("Array Iterator")?;
      scope.define_property(
        array_iterator_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    {
      let values_call = vm.register_native_call(crate::iterator::array_prototype_values)?;
      let values_name = scope.alloc_string("values")?;
      let values_fn =
        alloc_rooted_native_function(scope, roots, values_call, None, values_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(values_fn, Some(function_prototype))?;
      // Array.prototype.values
      scope.define_property(
        array_prototype,
        PropertyKey::from_string(values_name),
        data_desc(Value::Object(values_fn), true, false, true),
      )?;
      // Array.prototype[@@iterator] = values
      scope.define_property(
        array_prototype,
        PropertyKey::Symbol(well_known_symbols.iterator),
        data_desc(Value::Object(values_fn), true, false, true),
      )?;
    }

    // %StringIteratorPrototype% + String.prototype[@@iterator]
    let string_iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(string_iterator_prototype, Some(iterator_prototype))?;
    {
      let next_call = vm.register_native_call(crate::iterator::string_iterator_prototype_next)?;
      let next_name = scope.alloc_string("next")?;
      let next_fn = alloc_rooted_native_function(scope, roots, next_call, None, next_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(next_fn, Some(function_prototype))?;
      scope.define_property(
        string_iterator_prototype,
        PropertyKey::from_string(next_name),
        data_desc(Value::Object(next_fn), true, false, true),
      )?;

      let tag = scope.alloc_string("String Iterator")?;
      scope.define_property(
        string_iterator_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    {
      let iter_call = vm.register_native_call(crate::iterator::string_prototype_iterator)?;
      let iter_name = scope.alloc_string("[Symbol.iterator]")?;
      let iter_fn = alloc_rooted_native_function(scope, roots, iter_call, None, iter_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(iter_fn, Some(function_prototype))?;
      scope.define_property(
        string_prototype,
        PropertyKey::Symbol(well_known_symbols.iterator),
        data_desc(Value::Object(iter_fn), true, false, true),
      )?;
    }

    // %GeneratorPrototype% (a.k.a. %GeneratorFunction.prototype.prototype%)
    let generator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(generator_prototype, Some(iterator_prototype))?;
    // %GeneratorFunction.prototype% (a.k.a. %Generator%): the [[Prototype]] of generator functions.
    let generator_function_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(generator_function_prototype, Some(function_prototype))?;
    {
      for (name, call, len) in [
        (
          "next",
          vm.register_native_call(crate::generator::generator_prototype_next)?,
          1,
        ),
        (
          "return",
          vm.register_native_call(crate::generator::generator_prototype_return)?,
          1,
        ),
        (
          "throw",
          vm.register_native_call(crate::generator::generator_prototype_throw)?,
          1,
        ),
      ] {
        let name_s = scope.alloc_string(name)?;
        let f = alloc_rooted_native_function(scope, roots, call, None, name_s, len)?;
        scope
          .heap_mut()
          .object_set_prototype(f, Some(function_prototype))?;
        let key = PropertyKey::from_string(scope.alloc_string(name)?);
        scope.define_property(
          generator_prototype,
          key,
          data_desc(Value::Object(f), true, false, true),
        )?;
      }

      let tag = scope.alloc_string("Generator")?;
      scope.define_property(
        generator_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
      // %GeneratorPrototype%.constructor → %GeneratorFunction.prototype% (spec: non-writable,
      // configurable).
      scope.define_property(
        generator_prototype,
        common.constructor,
        data_desc(
          Value::Object(generator_function_prototype),
          false,
          false,
          true,
        ),
      )?;
      // %GeneratorFunction.prototype%.prototype → %GeneratorPrototype%
      scope.define_property(
        generator_function_prototype,
        common.prototype,
        data_desc(Value::Object(generator_prototype), false, false, true),
      )?;
      let gf_tag = scope.alloc_string("GeneratorFunction")?;
      scope.define_property(
        generator_function_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(gf_tag), false, false, true),
      )?;
    }

    // `%Map%` / `%Map.prototype%` / `%MapIteratorPrototype%` (ECMA-262 §24.1).
    let map_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(map_prototype, Some(object_prototype))?;
    let map_name = scope.alloc_string("Map")?;
    let map_call = vm.register_native_call(crate::map_set::map_constructor_call)?;
    let map_construct_id =
      vm.register_native_construct(crate::map_set::map_constructor_construct)?;
    let map_constructor =
      alloc_rooted_native_function(scope, roots, map_call, Some(map_construct_id), map_name, 0)?;
    scope
      .heap_mut()
      .object_set_prototype(map_constructor, Some(function_prototype))?;
    scope.define_property(
      map_constructor,
      common.prototype,
      data_desc(Value::Object(map_prototype), false, false, false),
    )?;
    scope.define_property(
      map_constructor,
      common.name,
      data_desc(Value::String(map_name), false, false, true),
    )?;
    scope.define_property(
      map_constructor,
      common.length,
      data_desc(Value::Number(0.0), false, false, true),
    )?;
    scope.define_property(
      map_prototype,
      common.constructor,
      data_desc(Value::Object(map_constructor), true, false, true),
    )?;
    {
      let tag = scope.alloc_string("Map")?;
      scope.define_property(
        map_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    {
      let species_call = vm.register_native_call(crate::map_set::species_get)?;
      let species_name = scope.alloc_string("get [Symbol.species]")?;
      let species_getter =
        alloc_rooted_native_function(scope, roots, species_call, None, species_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(species_getter, Some(function_prototype))?;
      scope.define_property(
        map_constructor,
        PropertyKey::Symbol(well_known_symbols.species),
        PropertyDescriptor {
          enumerable: false,
          configurable: true,
          kind: PropertyKind::Accessor {
            get: Value::Object(species_getter),
            set: Value::Undefined,
          },
        },
      )?;
    }
    install_object_static_method(
      vm,
      scope,
      roots,
      function_prototype,
      map_constructor,
      "groupBy",
      2,
      crate::map_set::map_group_by,
    )?;
    for (name, call, len) in [
      (
        "set",
        vm.register_native_call(crate::map_set::map_prototype_set)?,
        2,
      ),
      (
        "get",
        vm.register_native_call(crate::map_set::map_prototype_get)?,
        1,
      ),
      (
        "has",
        vm.register_native_call(crate::map_set::map_prototype_has)?,
        1,
      ),
      (
        "delete",
        vm.register_native_call(crate::map_set::map_prototype_delete)?,
        1,
      ),
      (
        "clear",
        vm.register_native_call(crate::map_set::map_prototype_clear)?,
        0,
      ),
      (
        "keys",
        vm.register_native_call(crate::map_set::map_prototype_keys)?,
        0,
      ),
      (
        "values",
        vm.register_native_call(crate::map_set::map_prototype_values)?,
        0,
      ),
      (
        "entries",
        vm.register_native_call(crate::map_set::map_prototype_entries)?,
        0,
      ),
      (
        "forEach",
        vm.register_native_call(crate::map_set::map_prototype_for_each)?,
        1,
      ),
      (
        "getOrInsert",
        vm.register_native_call(crate::map_set::map_prototype_get_or_insert)?,
        2,
      ),
      (
        "getOrInsertComputed",
        vm.register_native_call(crate::map_set::map_prototype_get_or_insert_computed)?,
        2,
      ),
    ] {
      define_prototype_method(scope, map_prototype, function_prototype, name, call, len)?;
    }
    {
      let size_get = vm.register_native_call(crate::map_set::map_prototype_size_get)?;
      let size_name = scope.alloc_string("get size")?;
      let size_getter = alloc_rooted_native_function(scope, roots, size_get, None, size_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(size_getter, Some(function_prototype))?;
      let size_key = PropertyKey::from_string(scope.alloc_string("size")?);
      scope.define_property(
        map_prototype,
        size_key,
        PropertyDescriptor {
          enumerable: false,
          configurable: true,
          kind: PropertyKind::Accessor {
            get: Value::Object(size_getter),
            set: Value::Undefined,
          },
        },
      )?;
    }
    // Map.prototype[@@iterator] = entries
    {
      let entries_key = PropertyKey::from_string(scope.alloc_string("entries")?);
      let entries = scope
        .heap()
        .object_get_own_data_property_value(map_prototype, &entries_key)?
        .ok_or(VmError::InvariantViolation("Map.prototype.entries missing"))?;
      scope.define_property(
        map_prototype,
        PropertyKey::Symbol(well_known_symbols.iterator),
        data_desc(entries, true, false, true),
      )?;
    }

    let map_iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(map_iterator_prototype, Some(iterator_prototype))?;
    {
      let next_call = vm.register_native_call(crate::map_set::map_iterator_prototype_next)?;
      define_prototype_method(
        scope,
        map_iterator_prototype,
        function_prototype,
        "next",
        next_call,
        0,
      )?;
      let tag = scope.alloc_string("Map Iterator")?;
      scope.define_property(
        map_iterator_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }

    // `%Set%` / `%Set.prototype%` / `%SetIteratorPrototype%` (ECMA-262 §24.2).
    let set_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(set_prototype, Some(object_prototype))?;
    let set_name = scope.alloc_string("Set")?;
    let set_call = vm.register_native_call(crate::map_set::set_constructor_call)?;
    let set_construct_id =
      vm.register_native_construct(crate::map_set::set_constructor_construct)?;
    let set_constructor =
      alloc_rooted_native_function(scope, roots, set_call, Some(set_construct_id), set_name, 0)?;
    scope
      .heap_mut()
      .object_set_prototype(set_constructor, Some(function_prototype))?;
    scope.define_property(
      set_constructor,
      common.prototype,
      data_desc(Value::Object(set_prototype), false, false, false),
    )?;
    scope.define_property(
      set_constructor,
      common.name,
      data_desc(Value::String(set_name), false, false, true),
    )?;
    scope.define_property(
      set_constructor,
      common.length,
      data_desc(Value::Number(0.0), false, false, true),
    )?;
    scope.define_property(
      set_prototype,
      common.constructor,
      data_desc(Value::Object(set_constructor), true, false, true),
    )?;
    {
      let tag = scope.alloc_string("Set")?;
      scope.define_property(
        set_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    {
      let species_call = vm.register_native_call(crate::map_set::species_get)?;
      let species_name = scope.alloc_string("get [Symbol.species]")?;
      let species_getter =
        alloc_rooted_native_function(scope, roots, species_call, None, species_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(species_getter, Some(function_prototype))?;
      scope.define_property(
        set_constructor,
        PropertyKey::Symbol(well_known_symbols.species),
        PropertyDescriptor {
          enumerable: false,
          configurable: true,
          kind: PropertyKind::Accessor {
            get: Value::Object(species_getter),
            set: Value::Undefined,
          },
        },
      )?;
    }
    for (name, call, len) in [
      (
        "add",
        vm.register_native_call(crate::map_set::set_prototype_add)?,
        1,
      ),
      (
        "has",
        vm.register_native_call(crate::map_set::set_prototype_has)?,
        1,
      ),
      (
        "delete",
        vm.register_native_call(crate::map_set::set_prototype_delete)?,
        1,
      ),
      (
        "clear",
        vm.register_native_call(crate::map_set::set_prototype_clear)?,
        0,
      ),
      (
        "values",
        vm.register_native_call(crate::map_set::set_prototype_values)?,
        0,
      ),
      (
        "entries",
        vm.register_native_call(crate::map_set::set_prototype_entries)?,
        0,
      ),
      (
        "forEach",
        vm.register_native_call(crate::map_set::set_prototype_for_each)?,
        1,
      ),
      (
        "union",
        vm.register_native_call(crate::map_set::set_prototype_union)?,
        1,
      ),
      (
        "intersection",
        vm.register_native_call(crate::map_set::set_prototype_intersection)?,
        1,
      ),
      (
        "difference",
        vm.register_native_call(crate::map_set::set_prototype_difference)?,
        1,
      ),
      (
        "symmetricDifference",
        vm.register_native_call(crate::map_set::set_prototype_symmetric_difference)?,
        1,
      ),
      (
        "isDisjointFrom",
        vm.register_native_call(crate::map_set::set_prototype_is_disjoint_from)?,
        1,
      ),
      (
        "isSubsetOf",
        vm.register_native_call(crate::map_set::set_prototype_is_subset_of)?,
        1,
      ),
      (
        "isSupersetOf",
        vm.register_native_call(crate::map_set::set_prototype_is_superset_of)?,
        1,
      ),
    ] {
      define_prototype_method(scope, set_prototype, function_prototype, name, call, len)?;
    }
    // Set.prototype.keys = values (same function object per spec).
    {
      let values_key = PropertyKey::from_string(scope.alloc_string("values")?);
      let values = scope
        .heap()
        .object_get_own_data_property_value(set_prototype, &values_key)?
        .ok_or(VmError::InvariantViolation("Set.prototype.values missing"))?;
      let keys_key = PropertyKey::from_string(scope.alloc_string("keys")?);
      scope.define_property(
        set_prototype,
        keys_key,
        data_desc(values, true, false, true),
      )?;
      scope.define_property(
        set_prototype,
        PropertyKey::Symbol(well_known_symbols.iterator),
        data_desc(values, true, false, true),
      )?;
    }
    {
      let size_get = vm.register_native_call(crate::map_set::set_prototype_size_get)?;
      let size_name = scope.alloc_string("get size")?;
      let size_getter = alloc_rooted_native_function(scope, roots, size_get, None, size_name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(size_getter, Some(function_prototype))?;
      let size_key = PropertyKey::from_string(scope.alloc_string("size")?);
      scope.define_property(
        set_prototype,
        size_key,
        PropertyDescriptor {
          enumerable: false,
          configurable: true,
          kind: PropertyKind::Accessor {
            get: Value::Object(size_getter),
            set: Value::Undefined,
          },
        },
      )?;
    }

    let set_iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(set_iterator_prototype, Some(iterator_prototype))?;
    {
      let next_call = vm.register_native_call(crate::map_set::set_iterator_prototype_next)?;
      define_prototype_method(
        scope,
        set_iterator_prototype,
        function_prototype,
        "next",
        next_call,
        0,
      )?;
      let tag = scope.alloc_string("Set Iterator")?;
      scope.define_property(
        set_iterator_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }

    // `%WeakMap%` / `%WeakSet%` — get/set/has/delete (+ iterable ctor); strong entry storage.
    let weakmap_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(weakmap_prototype, Some(object_prototype))?;
    let weakmap_name = scope.alloc_string("WeakMap")?;
    let weakmap_call = vm.register_native_call(crate::map_set::weakmap_constructor_call)?;
    let weakmap_construct =
      vm.register_native_construct(crate::map_set::weakmap_constructor_construct)?;
    let weakmap_constructor = alloc_rooted_native_function(
      scope,
      roots,
      weakmap_call,
      Some(weakmap_construct),
      weakmap_name,
      0,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(weakmap_constructor, Some(function_prototype))?;
    scope.define_property(
      weakmap_constructor,
      common.prototype,
      data_desc(Value::Object(weakmap_prototype), false, false, false),
    )?;
    scope.define_property(
      weakmap_constructor,
      common.name,
      data_desc(Value::String(weakmap_name), false, false, true),
    )?;
    scope.define_property(
      weakmap_constructor,
      common.length,
      data_desc(Value::Number(0.0), false, false, true),
    )?;
    scope.define_property(
      weakmap_prototype,
      common.constructor,
      data_desc(Value::Object(weakmap_constructor), true, false, true),
    )?;
    {
      let tag = scope.alloc_string("WeakMap")?;
      scope.define_property(
        weakmap_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    for (name, call, len) in [
      (
        "set",
        vm.register_native_call(crate::map_set::weakmap_prototype_set)?,
        2,
      ),
      (
        "get",
        vm.register_native_call(crate::map_set::weakmap_prototype_get)?,
        1,
      ),
      (
        "has",
        vm.register_native_call(crate::map_set::weakmap_prototype_has)?,
        1,
      ),
      (
        "delete",
        vm.register_native_call(crate::map_set::weakmap_prototype_delete)?,
        1,
      ),
      (
        "getOrInsert",
        vm.register_native_call(crate::map_set::weakmap_prototype_get_or_insert)?,
        2,
      ),
      (
        "getOrInsertComputed",
        vm.register_native_call(crate::map_set::weakmap_prototype_get_or_insert_computed)?,
        2,
      ),
    ] {
      define_prototype_method(
        scope,
        weakmap_prototype,
        function_prototype,
        name,
        call,
        len,
      )?;
    }

    let weakset_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(weakset_prototype, Some(object_prototype))?;
    let weakset_name = scope.alloc_string("WeakSet")?;
    let weakset_call = vm.register_native_call(crate::map_set::weakset_constructor_call)?;
    let weakset_construct =
      vm.register_native_construct(crate::map_set::weakset_constructor_construct)?;
    let weakset_constructor = alloc_rooted_native_function(
      scope,
      roots,
      weakset_call,
      Some(weakset_construct),
      weakset_name,
      0,
    )?;
    scope
      .heap_mut()
      .object_set_prototype(weakset_constructor, Some(function_prototype))?;
    scope.define_property(
      weakset_constructor,
      common.prototype,
      data_desc(Value::Object(weakset_prototype), false, false, false),
    )?;
    scope.define_property(
      weakset_constructor,
      common.name,
      data_desc(Value::String(weakset_name), false, false, true),
    )?;
    scope.define_property(
      weakset_constructor,
      common.length,
      data_desc(Value::Number(0.0), false, false, true),
    )?;
    scope.define_property(
      weakset_prototype,
      common.constructor,
      data_desc(Value::Object(weakset_constructor), true, false, true),
    )?;
    {
      let tag = scope.alloc_string("WeakSet")?;
      scope.define_property(
        weakset_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }
    for (name, call, len) in [
      (
        "add",
        vm.register_native_call(crate::map_set::weakset_prototype_add)?,
        1,
      ),
      (
        "has",
        vm.register_native_call(crate::map_set::weakset_prototype_has)?,
        1,
      ),
      (
        "delete",
        vm.register_native_call(crate::map_set::weakset_prototype_delete)?,
        1,
      ),
    ] {
      define_prototype_method(
        scope,
        weakset_prototype,
        function_prototype,
        name,
        call,
        len,
      )?;
    }

    // %AsyncFunction.prototype%: the [[Prototype]] of async functions.
    let async_function_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(async_function_prototype, Some(function_prototype))?;
    {
      let tag = scope.alloc_string("AsyncFunction")?;
      scope.define_property(
        async_function_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
    }

    // %AsyncIteratorPrototype% / %AsyncGeneratorPrototype% / %AsyncGeneratorFunction.prototype%
    let async_iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(async_iterator_prototype, Some(object_prototype))?;
    {
      // %AsyncIteratorPrototype%[@@asyncIterator]() { return this; }
      let call = vm.register_native_call(crate::generator::iterator_prototype_iterator)?;
      let name = scope.alloc_string("[Symbol.asyncIterator]")?;
      let f = alloc_rooted_native_function(scope, roots, call, None, name, 0)?;
      scope
        .heap_mut()
        .object_set_prototype(f, Some(function_prototype))?;
      scope.define_property(
        async_iterator_prototype,
        PropertyKey::Symbol(well_known_symbols.async_iterator),
        data_desc(Value::Object(f), true, false, true),
      )?;
    }

    // %AsyncFromSyncIteratorPrototype% (§27.1.4.2): wraps sync iterators for `for await`.
    let async_from_sync_iterator_prototype = alloc_rooted_object(scope, roots)?;
    scope.heap_mut().object_set_prototype(
      async_from_sync_iterator_prototype,
      Some(async_iterator_prototype),
    )?;
    {
      let call =
        vm.register_native_call(crate::iterator::async_from_sync_iterator_prototype_next)?;
      let name = scope.alloc_string("next")?;
      let f = alloc_rooted_native_function(scope, roots, call, None, name, 1)?;
      scope
        .heap_mut()
        .object_set_prototype(f, Some(function_prototype))?;
      let key = PropertyKey::from_string(scope.alloc_string("next")?);
      scope.define_property(
        async_from_sync_iterator_prototype,
        key,
        data_desc(Value::Object(f), true, false, true),
      )?;
    }

    let async_generator_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(async_generator_prototype, Some(async_iterator_prototype))?;
    let async_generator_function_prototype = alloc_rooted_object(scope, roots)?;
    scope
      .heap_mut()
      .object_set_prototype(async_generator_function_prototype, Some(function_prototype))?;
    {
      for (name, call, len) in [
        (
          "next",
          vm.register_native_call(crate::generator::async_generator_prototype_next)?,
          1,
        ),
        (
          "return",
          vm.register_native_call(crate::generator::async_generator_prototype_return)?,
          1,
        ),
        (
          "throw",
          vm.register_native_call(crate::generator::async_generator_prototype_throw)?,
          1,
        ),
      ] {
        let name_s = scope.alloc_string(name)?;
        let f = alloc_rooted_native_function(scope, roots, call, None, name_s, len)?;
        scope
          .heap_mut()
          .object_set_prototype(f, Some(function_prototype))?;
        let key = PropertyKey::from_string(scope.alloc_string(name)?);
        scope.define_property(
          async_generator_prototype,
          key,
          data_desc(Value::Object(f), true, false, true),
        )?;
      }

      let tag = scope.alloc_string("AsyncGenerator")?;
      scope.define_property(
        async_generator_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(tag), false, false, true),
      )?;
      scope.define_property(
        async_generator_prototype,
        common.constructor,
        data_desc(
          Value::Object(async_generator_function_prototype),
          false,
          false,
          true,
        ),
      )?;
      scope.define_property(
        async_generator_function_prototype,
        common.prototype,
        data_desc(Value::Object(async_generator_prototype), false, false, true),
      )?;
      let agf_tag = scope.alloc_string("AsyncGeneratorFunction")?;
      scope.define_property(
        async_generator_function_prototype,
        PropertyKey::Symbol(well_known_symbols.to_string_tag),
        data_desc(Value::String(agf_tag), false, false, true),
      )?;
    }

    let await_continuation_call =
      vm.register_native_call(crate::generator::await_continuation_call)?;
    let arguments_arg_getter_call = vm.register_native_call(builtins::arguments_arg_getter_call)?;
    let arguments_arg_setter_call = vm.register_native_call(builtins::arguments_arg_setter_call)?;
    let class_constructor_call = vm.register_native_call(builtins::class_constructor_call)?;
    let class_default_construct =
      vm.register_native_construct(builtins::class_default_construct)?;
    let class_default_derived_construct =
      vm.register_native_construct(builtins::class_default_derived_construct)?;

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
      regexp_prototype,
      symbol_prototype,
      object_constructor,
      function_constructor,
      array_constructor,
      string_constructor,
      number_constructor,
      boolean_constructor,
      date_constructor,
      regexp_constructor,
      symbol_constructor,
      proxy_constructor,
      map_constructor,
      map_prototype,
      map_iterator_prototype,
      set_constructor,
      set_prototype,
      set_iterator_prototype,
      weakmap_constructor,
      weakmap_prototype,
      weakset_constructor,
      weakset_prototype,
      bigint_constructor,
      eval,
      is_nan,
      is_finite,
      parse_int,
      parse_float,
      math,
      json,
      reflect,
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
      promise_capability_executor_call,
      promise_resolving_function_call,
      promise_finally_handler_call,
      promise_finally_thunk_call,
      promise_all_resolve_element_call,
      promise_all_settled_element_call,
      promise_any_reject_element_call,

      iterator_prototype,
      array_iterator_prototype,
      string_iterator_prototype,
      async_iterator_prototype,
      async_from_sync_iterator_prototype,
      generator_prototype,
      generator_function_prototype,
      async_generator_prototype,
      async_generator_function_prototype,
      async_function_prototype,
      await_continuation_call,
      arguments_arg_getter_call,
      arguments_arg_setter_call,
      class_constructor_call,
      class_default_construct,
      class_default_derived_construct,
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

  pub fn bigint_constructor(&self) -> GcObject {
    self.bigint_constructor
  }

  pub fn eval(&self) -> GcObject {
    self.eval
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

  pub fn regexp_prototype(&self) -> GcObject {
    self.regexp_prototype
  }

  pub fn regexp_constructor(&self) -> GcObject {
    self.regexp_constructor
  }

  pub fn proxy_constructor(&self) -> GcObject {
    self.proxy_constructor
  }

  pub fn map_constructor(&self) -> GcObject {
    self.map_constructor
  }

  pub fn map_prototype(&self) -> GcObject {
    self.map_prototype
  }

  pub fn map_iterator_prototype(&self) -> GcObject {
    self.map_iterator_prototype
  }

  pub fn set_constructor(&self) -> GcObject {
    self.set_constructor
  }

  pub fn set_prototype(&self) -> GcObject {
    self.set_prototype
  }

  pub fn set_iterator_prototype(&self) -> GcObject {
    self.set_iterator_prototype
  }

  pub fn weakmap_constructor(&self) -> GcObject {
    self.weakmap_constructor
  }

  pub fn weakmap_prototype(&self) -> GcObject {
    self.weakmap_prototype
  }

  pub fn weakset_constructor(&self) -> GcObject {
    self.weakset_constructor
  }

  pub fn weakset_prototype(&self) -> GcObject {
    self.weakset_prototype
  }

  pub fn symbol_constructor(&self) -> GcObject {
    self.symbol_constructor
  }

  pub fn is_nan(&self) -> GcObject {
    self.is_nan
  }

  pub fn is_finite(&self) -> GcObject {
    self.is_finite
  }

  pub fn parse_int(&self) -> GcObject {
    self.parse_int
  }

  pub fn parse_float(&self) -> GcObject {
    self.parse_float
  }

  pub fn math(&self) -> GcObject {
    self.math
  }

  pub fn json(&self) -> GcObject {
    self.json
  }

  pub fn reflect(&self) -> GcObject {
    self.reflect
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

  pub(crate) fn promise_capability_executor_call(&self) -> NativeFunctionId {
    self.promise_capability_executor_call
  }

  pub fn iterator_prototype(&self) -> GcObject {
    self.iterator_prototype
  }

  pub fn array_iterator_prototype(&self) -> GcObject {
    self.array_iterator_prototype
  }

  pub fn string_iterator_prototype(&self) -> GcObject {
    self.string_iterator_prototype
  }

  pub fn generator_prototype(&self) -> GcObject {
    self.generator_prototype
  }

  pub fn generator_function_prototype(&self) -> GcObject {
    self.generator_function_prototype
  }

  pub fn async_function_prototype(&self) -> GcObject {
    self.async_function_prototype
  }

  pub fn async_iterator_prototype(&self) -> GcObject {
    self.async_iterator_prototype
  }

  pub fn async_from_sync_iterator_prototype(&self) -> GcObject {
    self.async_from_sync_iterator_prototype
  }

  pub fn async_generator_prototype(&self) -> GcObject {
    self.async_generator_prototype
  }

  pub fn async_generator_function_prototype(&self) -> GcObject {
    self.async_generator_function_prototype
  }

  pub(crate) fn await_continuation_call(&self) -> NativeFunctionId {
    self.await_continuation_call
  }

  pub(crate) fn arguments_arg_getter_call(&self) -> NativeFunctionId {
    self.arguments_arg_getter_call
  }

  pub(crate) fn arguments_arg_setter_call(&self) -> NativeFunctionId {
    self.arguments_arg_setter_call
  }

  pub(crate) fn class_constructor_call(&self) -> NativeFunctionId {
    self.class_constructor_call
  }

  pub(crate) fn class_default_construct(&self) -> NativeConstructId {
    self.class_default_construct
  }

  pub(crate) fn class_default_derived_construct(&self) -> NativeConstructId {
    self.class_default_derived_construct
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

  pub(crate) fn promise_all_resolve_element_call(&self) -> NativeFunctionId {
    self.promise_all_resolve_element_call
  }

  pub(crate) fn promise_all_settled_element_call(&self) -> NativeFunctionId {
    self.promise_all_settled_element_call
  }

  pub(crate) fn promise_any_reject_element_call(&self) -> NativeFunctionId {
    self.promise_any_reject_element_call
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
