use crate::function::FunctionData;
use crate::property::{PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind};
use crate::string::JsString;
use crate::{
  GcObject, Job, JobCallback, JobKind, PromiseCapability, PromiseReaction, PromiseReactionType,
  PromiseState, RootId, Scope, Value, Vm, VmError,
};

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

fn require_intrinsics(vm: &Vm) -> Result<crate::Intrinsics, VmError> {
  vm.intrinsics().ok_or(VmError::Unimplemented(
    "native builtins require Vm::intrinsics to be set",
  ))
}

fn require_object(value: Value) -> Result<GcObject, VmError> {
  match value {
    Value::Object(o) => Ok(o),
    _ => Err(VmError::TypeError("expected object")),
  }
}

fn root_property_key(scope: &mut Scope<'_>, key: PropertyKey) -> Result<(), VmError> {
  match key {
    PropertyKey::String(s) => {
      scope.push_root(Value::String(s))?;
    }
    PropertyKey::Symbol(s) => {
      scope.push_root(Value::Symbol(s))?;
    }
  }
  Ok(())
}

fn get_own_data_property_value_by_name(
  scope: &mut Scope<'_>,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj))?;
  let key = PropertyKey::from_string(scope.alloc_string(name)?);
  let Some(desc) = scope.heap().object_get_own_property(obj, &key)? else {
    return Ok(None);
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(Some(value)),
    PropertyKind::Accessor { .. } => Err(VmError::Unimplemented(
      "accessor properties are not yet supported",
    )),
  }
}

pub fn function_prototype_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Ok(Value::Undefined)
}

fn object_constructor_impl(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let arg0 = args.get(0).copied().unwrap_or(Value::Undefined);
  match arg0 {
    Value::Undefined | Value::Null => {
      let obj = scope.alloc_object()?;
      scope
        .heap_mut()
        .object_set_prototype(obj, Some(intr.object_prototype()))?;
      Ok(Value::Object(obj))
    }
    Value::Object(obj) => Ok(Value::Object(obj)),
    _ => Err(VmError::Unimplemented("ToObject boxing")),
  }
}

pub fn object_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, args)
}

pub fn object_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  object_constructor_impl(vm, scope, args)
}

pub fn object_define_property(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let mut scope = scope.reborrow();

  let target = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(target))?;

  let prop = args.get(1).copied().unwrap_or(Value::Undefined);
  let key = scope.heap_mut().to_property_key(prop)?;
  root_property_key(&mut scope, key)?;

  let desc_obj = require_object(args.get(2).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(desc_obj))?;

  let value = get_own_data_property_value_by_name(&mut scope, desc_obj, "value")?;
  let writable = get_own_data_property_value_by_name(&mut scope, desc_obj, "writable")?
    .map(|v| scope.heap().to_boolean(v))
    .transpose()?;
  let enumerable = get_own_data_property_value_by_name(&mut scope, desc_obj, "enumerable")?
    .map(|v| scope.heap().to_boolean(v))
    .transpose()?;
  let configurable = get_own_data_property_value_by_name(&mut scope, desc_obj, "configurable")?
    .map(|v| scope.heap().to_boolean(v))
    .transpose()?;
  let get = get_own_data_property_value_by_name(&mut scope, desc_obj, "get")?;
  let set = get_own_data_property_value_by_name(&mut scope, desc_obj, "set")?;

  let patch = PropertyDescriptorPatch {
    enumerable,
    configurable,
    value,
    writable,
    get,
    set,
  };
  patch.validate()?;

  let ok = scope.ordinary_define_own_property(target, key, patch)?;
  if !ok {
    return Err(VmError::TypeError("DefineOwnProperty rejected"));
  }
  Ok(Value::Object(target))
}

pub fn object_create(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let proto_val = args.get(0).copied().unwrap_or(Value::Undefined);
  let proto = match proto_val {
    Value::Object(o) => Some(o),
    Value::Null => None,
    _ => {
      return Err(VmError::TypeError(
        "Object.create prototype must be an object or null",
      ))
    }
  };

  if let Some(properties_object) = args.get(1).copied() {
    if !matches!(properties_object, Value::Undefined) {
      return Err(VmError::Unimplemented("Object.create propertiesObject"));
    }
  }

  let obj = scope.alloc_object()?;
  scope.heap_mut().object_set_prototype(obj, proto)?;
  Ok(Value::Object(obj))
}

pub fn object_keys(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;

  let own_keys = scope.heap().ordinary_own_property_keys(obj)?;
  let mut names: Vec<crate::GcString> = Vec::new();
  names
    .try_reserve_exact(own_keys.len())
    .map_err(|_| VmError::OutOfMemory)?;

  for key in own_keys {
    let PropertyKey::String(key_str) = key else {
      continue;
    };
    let Some(desc) = scope.heap().object_get_own_property(obj, &key)? else {
      continue;
    };
    if desc.enumerable {
      names.push(key_str);
    }
  }

  let len = u32::try_from(names.len()).map_err(|_| VmError::OutOfMemory)?;
  let array = create_array_object(vm, scope, len)?;

  for (i, name) in names.iter().copied().enumerate() {
    let mut idx_scope = scope.reborrow();
    idx_scope.push_root(Value::Object(array))?;
    idx_scope.push_root(Value::String(name))?;

    let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
    idx_scope.define_property(array, key, data_desc(Value::String(name), true, true, true))?;
  }

  Ok(Value::Object(array))
}

pub fn object_assign(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  // Spec: Object.assign performs `ToObject` on the target and each source. We only support objects
  // for now, but we still follow the `Get`/`Set` semantics (invoking accessors).
  let mut scope = scope.reborrow();
  let target = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(target))?;

  for source_val in args.iter().copied().skip(1) {
    let source = match source_val {
      Value::Undefined | Value::Null => continue,
      Value::Object(o) => o,
      _ => return Err(VmError::TypeError("Object.assign source must be an object")),
    };

    let keys = scope.heap().ordinary_own_property_keys(source)?;
    for key in keys {
      let Some(desc) = scope.heap().object_get_own_property(source, &key)? else {
        continue;
      };
      if !desc.enumerable {
        continue;
      }

      // Spec: `Get(from, key)` (invokes getters).
      let value = vm.get(&mut scope, source, key)?;
      // Spec: `Set(to, key, value, true)` (invokes setters, throws on failure).
      let ok = scope.ordinary_set(vm, target, key, value, Value::Object(target))?;
      if !ok {
        return Err(VmError::TypeError("Object.assign failed to set property"));
      }
    }
  }

  Ok(Value::Object(target))
}

pub fn object_get_prototype_of(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  match scope.heap().object_prototype(obj)? {
    Some(proto) => Ok(Value::Object(proto)),
    None => Ok(Value::Null),
  }
}

pub fn object_set_prototype_of(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let obj = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;
  let proto_val = args.get(1).copied().unwrap_or(Value::Undefined);
  let proto = match proto_val {
    Value::Object(o) => Some(o),
    Value::Null => None,
    _ => {
      return Err(VmError::TypeError(
        "Object.setPrototypeOf prototype must be an object or null",
      ))
    }
  };

  scope.heap_mut().object_set_prototype(obj, proto)?;
  Ok(Value::Object(obj))
}

fn create_array_object(vm: &mut Vm, scope: &mut Scope<'_>, len: u32) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;

  let array = scope.alloc_object()?;
  scope
    .heap_mut()
    .object_set_prototype(array, Some(intr.array_prototype()))?;

  let length_key = PropertyKey::from_string(scope.alloc_string("length")?);
  scope.define_property(
    array,
    length_key,
    data_desc(Value::Number(len as f64), true, false, false),
  )?;

  Ok(array)
}

fn array_constructor_impl(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  args: &[Value],
) -> Result<Value, VmError> {
  match args {
    [] => Ok(Value::Object(create_array_object(vm, scope, 0)?)),
    [Value::Number(n)] => {
      // Minimal `Array(len)` support (used by WebIDL sequence conversions).
      if !n.is_finite() || n.fract() != 0.0 || *n < 0.0 || *n > (u32::MAX as f64) {
        return Err(VmError::Unimplemented("Array(length) validation"));
      }
      Ok(Value::Object(create_array_object(vm, scope, *n as u32)?))
    }
    _ => {
      // Treat arguments as elements.
      let len = u32::try_from(args.len()).map_err(|_| VmError::OutOfMemory)?;
      let array = create_array_object(vm, scope, len)?;

      for (i, el) in args.iter().copied().enumerate() {
        // Root `array` and `el` during string allocation.
        let mut idx_scope = scope.reborrow();
        idx_scope.push_root(Value::Object(array))?;
        idx_scope.push_root(el)?;

        let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
        idx_scope.define_property(array, key, data_desc(el, true, true, true))?;
      }

      Ok(Value::Object(array))
    }
  }
}

pub fn array_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn array_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  array_constructor_impl(vm, scope, args)
}

pub fn function_constructor_call(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Function constructor"))
}

pub fn function_constructor_construct(
  _vm: &mut Vm,
  _scope: &mut Scope<'_>,
  _callee: GcObject,
  _args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  Err(VmError::Unimplemented("Function constructor"))
}

pub fn error_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  error_constructor_construct(vm, scope, callee, args, Value::Object(callee))
}

pub fn error_constructor_construct(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let name = scope.heap().get_function_name(callee)?;

  // `new Error(message)` uses `GetPrototypeFromConstructor(newTarget, defaultProto)`.
  // Approximate this by:
  // 1. Reading `callee.prototype` as the default.
  // 2. If `new_target` is an object, prefer `new_target.prototype` when it is an object.
  let prototype_key = PropertyKey::from_string(scope.alloc_string("prototype")?);
  let default_proto_value = scope
    .heap()
    .object_get_own_data_property_value(callee, &prototype_key)?
    .ok_or(VmError::Unimplemented(
      "Error constructor missing own prototype property",
    ))?;
  let Value::Object(default_prototype) = default_proto_value else {
    return Err(VmError::Unimplemented(
      "Error constructor prototype property is not an object",
    ));
  };

  let instance_prototype = match new_target {
    Value::Object(nt) => match scope.heap().get(nt, &prototype_key)? {
      Value::Object(p) => p,
      _ => default_prototype,
    },
    _ => default_prototype,
  };

  // Message argument: AggregateError(message is the second argument).
  let message_arg = if scope.heap().get_string(name)?.to_utf8_lossy() == "AggregateError" {
    args.get(1).copied().or_else(|| args.first().copied())
  } else {
    args.first().copied()
  };

  let message_string = match message_arg {
    Some(Value::Undefined) | None => scope.alloc_string("")?,
    Some(other) => scope.heap_mut().to_string(other)?,
  };
  scope.push_root(Value::String(message_string))?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(instance_prototype))?;

  let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
  scope.define_property(
    obj,
    name_key,
    data_desc(Value::String(name), true, false, true),
  )?;

  let message_key = PropertyKey::from_string(scope.alloc_string("message")?);
  scope.define_property(
    obj,
    message_key,
    data_desc(Value::String(message_string), true, false, true),
  )?;

  Ok(Value::Object(obj))
}

fn throw_type_error(vm: &mut Vm, scope: &mut Scope<'_>, message: &str) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let ctor = intr.type_error();

  let msg = scope.alloc_string(message)?;
  scope.push_root(Value::String(msg))?;

  let err =
    error_constructor_construct(vm, scope, ctor, &[Value::String(msg)], Value::Object(ctor))?;
  Err(VmError::Throw(err))
}

fn create_type_error(vm: &mut Vm, scope: &mut Scope<'_>, message: &str) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let ctor = intr.type_error();

  let msg = scope.alloc_string(message)?;
  scope.push_root(Value::String(msg))?;

  let err = error_constructor_construct(
    vm,
    scope,
    ctor,
    &[Value::String(msg)],
    Value::Object(ctor),
  )?;
  Ok(err)
}

fn new_promise(vm: &mut Vm, scope: &mut Scope<'_>) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;
  scope.alloc_promise_with_prototype(Some(intr.promise_prototype()))
}

fn new_promise_capability(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  constructor: Value,
) -> Result<PromiseCapability, VmError> {
  let intr = require_intrinsics(vm)?;

  let Value::Object(c) = constructor else {
    throw_type_error(vm, scope, "Promise capability constructor must be an object")?;
    unreachable!("throw_type_error always throws");
  };

  // Temporary `%Promise%`-only fallback: the VM does not yet support Promise subclassing /
  // `NewPromiseCapability` calling user-defined constructors.
  if c != intr.promise() {
    return Err(VmError::Unimplemented(
      "NewPromiseCapability for non-%Promise% constructors is not implemented",
    ));
  }

  let promise = new_promise(vm, scope)?;
  scope.push_root(Value::Object(promise))?;
  let (resolve, reject) = create_promise_resolving_functions(vm, scope, promise)?;
  Ok(PromiseCapability {
    promise,
    resolve,
    reject,
  })
}

fn create_promise_resolving_functions(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  promise: GcObject,
) -> Result<(Value, Value), VmError> {
  let intr = require_intrinsics(vm)?;
  let call_id = intr.promise_resolving_function_call();

  // Root the promise while allocating the resolving functions.
  scope.push_root(Value::Object(promise))?;

  let resolve_name = scope.alloc_string("resolve")?;
  let resolve = scope.alloc_native_function(call_id, None, resolve_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(resolve, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    resolve,
    FunctionData::PromiseResolvingFunction {
      promise,
      is_reject: false,
    },
  )?;

  let reject_name = scope.alloc_string("reject")?;
  let reject = scope.alloc_native_function(call_id, None, reject_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(reject, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    reject,
    FunctionData::PromiseResolvingFunction {
      promise,
      is_reject: true,
    },
  )?;

  Ok((Value::Object(resolve), Value::Object(reject)))
}

fn enqueue_promise_reaction_job(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  reaction: PromiseReaction,
  argument: Value,
) -> Result<(), VmError> {
  let handler_callback_object = reaction.handler.as_ref().map(|h| h.callback_object());
  let capability = reaction.capability;

  let job = Job::new(JobKind::Promise, move |ctx, host| {
    let Some(cap) = reaction.capability else {
      return Ok(());
    };

    match reaction.type_ {
      PromiseReactionType::Fulfill => {
        let handler_result = if let Some(handler) = &reaction.handler {
          match host.host_call_job_callback(ctx, handler, Value::Undefined, &[argument]) {
            Ok(v) => v,
            Err(VmError::Throw(e)) => {
              let _ = ctx.call(cap.reject, Value::Undefined, &[e])?;
              return Ok(());
            }
            Err(e) => return Err(e),
          }
        } else {
          argument
        };

        let _ = ctx.call(cap.resolve, Value::Undefined, &[handler_result])?;
        Ok(())
      }
      PromiseReactionType::Reject => {
        if let Some(handler) = &reaction.handler {
          match host.host_call_job_callback(ctx, handler, Value::Undefined, &[argument]) {
            Ok(v) => {
              let _ = ctx.call(cap.resolve, Value::Undefined, &[v])?;
              Ok(())
            }
            Err(VmError::Throw(e)) => {
              let _ = ctx.call(cap.reject, Value::Undefined, &[e])?;
              Ok(())
            }
            Err(e) => Err(e),
          }
        } else {
          let _ = ctx.call(cap.reject, Value::Undefined, &[argument])?;
          Ok(())
        }
      }
    }
  });

  // Root captured GC values while creating persistent roots: `Heap::add_root` can trigger a GC.
  // The resulting `RootId`s are transferred to the job so it can clean them up on run/discard.
  let mut root_scope = scope.reborrow();
  let mut values = [Value::Undefined; 5];
  let mut value_count = 0usize;
  values[value_count] = argument;
  value_count += 1;
  if let Some(handler) = handler_callback_object {
    values[value_count] = Value::Object(handler);
    value_count += 1;
  }
  if let Some(cap) = capability {
    values[value_count] = Value::Object(cap.promise);
    value_count += 1;
    values[value_count] = cap.resolve;
    value_count += 1;
    values[value_count] = cap.reject;
    value_count += 1;
  }
  root_scope.push_roots(&values[..value_count])?;

  let mut roots: Vec<RootId> = Vec::new();
  roots
    .try_reserve_exact(value_count)
    .map_err(|_| VmError::OutOfMemory)?;
  for value in values[..value_count].iter().copied() {
    let id = match root_scope.heap_mut().add_root(value) {
      Ok(id) => id,
      Err(e) => {
        for root in roots.drain(..) {
          root_scope.heap_mut().remove_root(root);
        }
        return Err(e);
      }
    };
    roots.push(id);
  }

  let job = job.with_roots(roots);
  vm.microtask_queue_mut().enqueue_promise_job(job, None);
  Ok(())
}

fn trigger_promise_reactions(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  reactions: Box<[PromiseReaction]>,
  argument: Value,
) -> Result<(), VmError> {
  for reaction in reactions.into_vec() {
    enqueue_promise_reaction_job(vm, scope, reaction, argument)?;
  }
  Ok(())
}

fn fulfill_promise(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  promise: GcObject,
  value: Value,
) -> Result<(), VmError> {
  let (fulfill_reactions, _reject_reactions) =
    scope
      .heap_mut()
      .promise_settle_and_take_reactions(promise, PromiseState::Fulfilled, value)?;
  trigger_promise_reactions(vm, scope, fulfill_reactions, value)
}

fn reject_promise(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  promise: GcObject,
  reason: Value,
) -> Result<(), VmError> {
  let (_fulfill_reactions, reject_reactions) =
    scope
      .heap_mut()
      .promise_settle_and_take_reactions(promise, PromiseState::Rejected, reason)?;
  trigger_promise_reactions(vm, scope, reject_reactions, reason)
}

pub fn promise_constructor_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  throw_type_error(vm, scope, "Promise constructor must be called with new")
}

pub fn promise_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  args: &[Value],
  _new_target: Value,
) -> Result<Value, VmError> {
  let executor = args.get(0).copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(executor)? {
    return throw_type_error(vm, scope, "Promise executor is not callable");
  }

  let promise = new_promise(vm, scope)?;
  scope.push_root(Value::Object(promise))?;

  let (resolve, reject) = create_promise_resolving_functions(vm, scope, promise)?;

  // Invoke executor(resolve, reject).
  match vm.call(scope, executor, Value::Undefined, &[resolve, reject]) {
    Ok(_) => {}
    Err(VmError::Throw(reason)) => {
      // If executor throws, reject the promise with the thrown value.
      reject_promise(vm, scope, promise, reason)?;
    }
    Err(e) => return Err(e),
  }

  Ok(Value::Object(promise))
}

pub fn promise_resolving_function_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let resolution = args.get(0).copied().unwrap_or(Value::Undefined);
  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseResolvingFunction { promise, is_reject } = data else {
    return Err(VmError::Unimplemented(
      "promise resolving function internal slots",
    ));
  };

  if is_reject {
    reject_promise(vm, scope, promise, resolution)?;
  } else {
    // Minimal Promise resolution procedure:
    // - adopt Promise resolution (Promise-to-Promise), needed for `then`/`finally` chaining;
    // - otherwise, fulfill with the provided value.
    if let Value::Object(resolution_obj) = resolution {
      if scope.heap().is_promise_object(resolution_obj) {
        if resolution_obj == promise {
          let err = create_type_error(vm, scope, "Cannot resolve a promise with itself")?;
          scope.push_root(err)?;
          reject_promise(vm, scope, promise, err)?;
          return Ok(Value::Undefined);
        }

        match scope.heap().promise_state(resolution_obj)? {
          PromiseState::Pending => {
            // Attach reactions that settle `promise` once `resolution_obj` settles.
            scope.push_root(Value::Object(promise))?;
            let (resolve, reject) = create_promise_resolving_functions(vm, scope, promise)?;
            let capability = PromiseCapability {
              promise,
              resolve,
              reject,
            };
            let fulfill_reaction = PromiseReaction {
              capability: Some(capability),
              type_: PromiseReactionType::Fulfill,
              handler: None,
            };
            let reject_reaction = PromiseReaction {
              capability: Some(capability),
              type_: PromiseReactionType::Reject,
              handler: None,
            };

            scope.promise_append_fulfill_reaction(resolution_obj, fulfill_reaction)?;
            scope.promise_append_reject_reaction(resolution_obj, reject_reaction)?;
          }
          PromiseState::Fulfilled => {
            let value = scope
              .heap()
              .promise_result(resolution_obj)?
              .unwrap_or(Value::Undefined);
            fulfill_promise(vm, scope, promise, value)?;
          }
          PromiseState::Rejected => {
            let reason = scope
              .heap()
              .promise_result(resolution_obj)?
              .unwrap_or(Value::Undefined);
            reject_promise(vm, scope, promise, reason)?;
          }
        }

        return Ok(Value::Undefined);
      }
    }

    fulfill_promise(vm, scope, promise, resolution)?;
  }
  Ok(Value::Undefined)
}

pub fn promise_resolve(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let x = args.get(0).copied().unwrap_or(Value::Undefined);

  if let Value::Object(obj) = x {
    if scope.heap().is_promise_object(obj)
      && scope.heap().object_prototype(obj)? == Some(intr.promise_prototype())
    {
      return Ok(Value::Object(obj));
    }
  }

  let p = new_promise(vm, scope)?;
  scope.heap_mut().promise_fulfill(p, x)?;
  Ok(Value::Object(p))
}

pub fn promise_reject(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let reason = args.get(0).copied().unwrap_or(Value::Undefined);
  let p = new_promise(vm, scope)?;
  reject_promise(vm, scope, p, reason)?;
  Ok(Value::Object(p))
}

fn promise_then_impl(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  this: Value,
  on_fulfilled: Value,
  on_rejected: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let Value::Object(promise) = this else {
    return throw_type_error(vm, scope, "Promise.prototype.then called on non-object");
  };
  if !scope.heap().is_promise_object(promise) {
    return throw_type_error(vm, scope, "Promise.prototype.then called on non-promise");
  }

  // `PerformPromiseThen` sets `[[PromiseIsHandled]] = true`.
  scope.heap_mut().promise_set_is_handled(promise, true)?;

  // Normalize handlers: use "empty" when not callable.
  let on_fulfilled = match on_fulfilled {
    Value::Object(obj) if scope.heap().is_callable(Value::Object(obj))? => {
      Some(JobCallback::new(obj))
    }
    _ => None,
  };
  let on_rejected = match on_rejected {
    Value::Object(obj) if scope.heap().is_callable(Value::Object(obj))? => {
      Some(JobCallback::new(obj))
    }
    _ => None,
  };

  // Create the derived promise + capability.
  let result_promise = scope
    .alloc_promise_with_prototype(Some(intr.promise_prototype()))?;
  scope.push_root(Value::Object(result_promise))?;
  let (resolve, reject) = create_promise_resolving_functions(vm, scope, result_promise)?;
  let capability = PromiseCapability {
    promise: result_promise,
    resolve,
    reject,
  };

  let fulfill_reaction = PromiseReaction {
    capability: Some(capability),
    type_: PromiseReactionType::Fulfill,
    handler: on_fulfilled,
  };
  let reject_reaction = PromiseReaction {
    capability: Some(capability),
    type_: PromiseReactionType::Reject,
    handler: on_rejected,
  };

  match scope.heap().promise_state(promise)? {
    PromiseState::Pending => {
      scope.promise_append_fulfill_reaction(promise, fulfill_reaction)?;
      scope.promise_append_reject_reaction(promise, reject_reaction)?;
    }
    PromiseState::Fulfilled => {
      let arg = scope
        .heap()
        .promise_result(promise)?
        .unwrap_or(Value::Undefined);
      enqueue_promise_reaction_job(vm, scope, fulfill_reaction, arg)?;
    }
    PromiseState::Rejected => {
      let arg = scope
        .heap()
        .promise_result(promise)?
        .unwrap_or(Value::Undefined);
      enqueue_promise_reaction_job(vm, scope, reject_reaction, arg)?;
    }
  }

  Ok(Value::Object(result_promise))
}

pub fn promise_prototype_then(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let on_fulfilled = args.get(0).copied().unwrap_or(Value::Undefined);
  let on_rejected = args.get(1).copied().unwrap_or(Value::Undefined);
  promise_then_impl(vm, scope, this, on_fulfilled, on_rejected)
}

pub fn promise_prototype_catch(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let on_rejected = args.get(0).copied().unwrap_or(Value::Undefined);
  promise_then_impl(vm, scope, this, Value::Undefined, on_rejected)
}

pub fn promise_prototype_finally(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let on_finally = args.get(0).copied().unwrap_or(Value::Undefined);

  let Value::Object(promise) = this else {
    return throw_type_error(vm, scope, "Promise.prototype.finally called on non-object");
  };
  if !scope.heap().is_promise_object(promise) {
    return throw_type_error(vm, scope, "Promise.prototype.finally called on non-promise");
  }

  if !scope.heap().is_callable(on_finally)? {
    return promise_then_impl(vm, scope, this, on_finally, on_finally);
  }

  scope.push_root(Value::Object(promise))?;
  scope.push_root(on_finally)?;

  let call_id = intr.promise_finally_handler_call();

  let then_finally_name = scope.alloc_string("thenFinally")?;
  let then_finally = scope.alloc_native_function(call_id, None, then_finally_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(then_finally, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    then_finally,
    FunctionData::PromiseFinallyHandler {
      on_finally,
      is_reject: false,
    },
  )?;

  let catch_finally_name = scope.alloc_string("catchFinally")?;
  let catch_finally = scope.alloc_native_function(call_id, None, catch_finally_name, 1)?;
  scope
    .heap_mut()
    .object_set_prototype(catch_finally, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    catch_finally,
    FunctionData::PromiseFinallyHandler {
      on_finally,
      is_reject: true,
    },
  )?;

  // Root the closure functions before calling `promise_then_impl`, which may allocate/GC.
  scope.push_root(Value::Object(then_finally))?;
  scope.push_root(Value::Object(catch_finally))?;

  promise_then_impl(
    vm,
    scope,
    this,
    Value::Object(then_finally),
    Value::Object(catch_finally),
  )
}

pub fn promise_finally_handler_call(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseFinallyHandler { on_finally, is_reject } = data else {
    return Err(VmError::Unimplemented(
      "Promise finally handler missing internal slots",
    ));
  };

  let captured = args.get(0).copied().unwrap_or(Value::Undefined);

  // Call onFinally() with no arguments.
  let result = vm.call(scope, on_finally, Value::Undefined, &[])?;
  let result = scope.push_root(result)?;

  // `PromiseResolve(%Promise%, result)`
  let promise_ctor = intr.promise();
  let p = promise_resolve(vm, scope, promise_ctor, Value::Object(promise_ctor), &[result])?;
  let Value::Object(promise_obj) = p else {
    return Err(VmError::Unimplemented("Promise.resolve did not return an object"));
  };

  // Create `valueThunk` or `thrower`.
  scope.push_root(Value::Object(promise_obj))?;
  scope.push_root(captured)?;
  let thunk_call = intr.promise_finally_thunk_call();
  let thunk_name = if is_reject { "thrower" } else { "valueThunk" };
  let thunk_name = scope.alloc_string(thunk_name)?;
  let thunk = scope.alloc_native_function(thunk_call, None, thunk_name, 0)?;
  scope
    .heap_mut()
    .object_set_prototype(thunk, Some(intr.function_prototype()))?;
  scope.heap_mut().set_function_data(
    thunk,
    FunctionData::PromiseFinallyThunk {
      value: captured,
      is_throw: is_reject,
    },
  )?;

  // Return `p.then(valueThunk)` / `p.then(thrower)`.
  scope.push_root(Value::Object(thunk))?;
  promise_then_impl(vm, scope, Value::Object(promise_obj), Value::Object(thunk), Value::Undefined)
}

pub fn promise_finally_thunk_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let data = scope.heap().get_function_data(callee)?;
  let FunctionData::PromiseFinallyThunk { value, is_throw } = data else {
    return Err(VmError::Unimplemented(
      "Promise finally thunk missing internal slots",
    ));
  };
  if is_throw {
    Err(VmError::Throw(value))
  } else {
    Ok(value)
  }
}

pub fn promise_try(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let callback = args.get(0).copied().unwrap_or(Value::Undefined);
  if !scope.heap().is_callable(callback)? {
    return throw_type_error(vm, scope, "Promise.try callback is not callable");
  }

  let capability = new_promise_capability(vm, scope, this)?;

  // Root the promise + resolving functions for the duration of the callback call.
  scope.push_root(Value::Object(capability.promise))?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let callback_args = args.get(1..).unwrap_or(&[]);
  match vm.call(scope, callback, Value::Undefined, callback_args) {
    Ok(v) => {
      let _ = vm.call(scope, capability.resolve, Value::Undefined, &[v])?;
    }
    Err(VmError::Throw(e)) => {
      let _ = vm.call(scope, capability.reject, Value::Undefined, &[e])?;
    }
    Err(e) => return Err(e),
  }

  Ok(Value::Object(capability.promise))
}

pub fn promise_with_resolvers(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;

  let capability = new_promise_capability(vm, scope, this)?;
  // Root the new promise and resolving functions before allocating the result object.
  scope.push_root(Value::Object(capability.promise))?;
  scope.push_root(capability.resolve)?;
  scope.push_root(capability.reject)?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.object_prototype()))?;

  let promise_key = PropertyKey::from_string(scope.alloc_string("promise")?);
  scope.define_property(
    obj,
    promise_key,
    data_desc(Value::Object(capability.promise), true, true, true),
  )?;

  let resolve_key = PropertyKey::from_string(scope.alloc_string("resolve")?);
  scope.define_property(
    obj,
    resolve_key,
    data_desc(capability.resolve, true, true, true),
  )?;

  let reject_key = PropertyKey::from_string(scope.alloc_string("reject")?);
  scope.define_property(
    obj,
    reject_key,
    data_desc(capability.reject, true, true, true),
  )?;

  Ok(Value::Object(obj))
}

fn string_key(scope: &mut Scope<'_>, s: &str) -> Result<PropertyKey, VmError> {
  let key_s = scope.alloc_string(s)?;
  scope.push_root(Value::String(key_s))?;
  Ok(PropertyKey::from_string(key_s))
}

fn get_data_property_value(
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: &PropertyKey,
) -> Result<Option<Value>, VmError> {
  let Some(desc) = scope.heap().get_property(obj, key)? else {
    return Ok(None);
  };
  match desc.kind {
    PropertyKind::Data { value, .. } => Ok(Some(value)),
    PropertyKind::Accessor { .. } => Err(VmError::PropertyNotData),
  }
}

fn to_length(value: Value) -> usize {
  let Value::Number(n) = value else {
    return 0;
  };
  if !n.is_finite() || n <= 0.0 {
    return 0;
  }
  if n >= usize::MAX as f64 {
    return usize::MAX;
  }
  n.floor() as usize
}

fn vec_try_push<T>(buf: &mut Vec<T>, value: T) -> Result<(), VmError> {
  if buf.len() == buf.capacity() {
    buf.try_reserve(1).map_err(|_| VmError::OutOfMemory)?;
  }
  buf.push(value);
  Ok(())
}

fn vec_try_extend_from_slice<T: Copy>(buf: &mut Vec<T>, slice: &[T]) -> Result<(), VmError> {
  let needed = slice.len().saturating_sub(buf.capacity().saturating_sub(buf.len()));
  if needed > 0 {
    buf.try_reserve(needed).map_err(|_| VmError::OutOfMemory)?;
  }
  buf.extend_from_slice(slice);
  Ok(())
}

/// `Function.prototype.call`.
pub fn function_prototype_call_method(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_arg = args.first().copied().unwrap_or(Value::Undefined);
  let rest = args.get(1..).unwrap_or(&[]);
  vm.call(scope, this, this_arg, rest)
}

/// `Object.prototype.toString` (partial).
pub fn object_prototype_to_string(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let s = match this {
    Value::Undefined => "[object Undefined]",
    Value::Null => "[object Null]",
    Value::Bool(_) => "[object Boolean]",
    Value::Number(_) => "[object Number]",
    Value::String(_) => "[object String]",
    Value::Symbol(_) => "[object Symbol]",
    Value::Object(obj) => {
      if scope.heap().is_callable(Value::Object(obj))? {
        "[object Function]"
      } else {
        "[object Object]"
      }
    }
  };
  Ok(Value::String(scope.alloc_string(s)?))
}

fn get_array_length(scope: &mut Scope<'_>, obj: GcObject) -> Result<usize, VmError> {
  let length_key = string_key(scope, "length")?;
  Ok(match get_data_property_value(scope, obj, &length_key)? {
    Some(v) => to_length(v),
    None => 0,
  })
}

fn define_array_length(scope: &mut Scope<'_>, obj: GcObject, len: usize) -> Result<(), VmError> {
  let length_key = string_key(scope, "length")?;
  scope.define_property(
    obj,
    length_key,
    data_desc(Value::Number(len as f64), true, false, false),
  )
}

/// `Array.prototype.map` (minimal).
pub fn array_prototype_map(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Array.prototype.map on non-object")),
  };

  let len = get_array_length(scope, this_obj)?;

  let callback = args.first().copied().unwrap_or(Value::Undefined);
  let this_arg = args.get(1).copied().unwrap_or(Value::Undefined);

  let intr = require_intrinsics(vm)?;
  let out = scope.alloc_object()?;
  scope.push_root(Value::Object(out))?;
  scope
    .heap_mut()
    .object_set_prototype(out, Some(intr.array_prototype()))?;
  define_array_length(scope, out, len)?;

  for i in 0..len {
    vm.tick()?;
    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let Some(value) = get_data_property_value(scope, this_obj, &key)? else {
      continue;
    };

    // callback(value, index, array)
    let call_args = [value, Value::Number(i as f64), Value::Object(this_obj)];
    let mapped = vm.call(scope, callback, this_arg, &call_args)?;

    scope.define_property(out, key, data_desc(mapped, true, true, true))?;
  }

  Ok(Value::Object(out))
}

/// `Array.prototype.join` (minimal).
pub fn array_prototype_join(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Array.prototype.join on non-object")),
  };

  let len = get_array_length(scope, this_obj)?;

  let sep = match args.first().copied() {
    None | Some(Value::Undefined) => scope.alloc_string(",")?,
    Some(v) => scope.heap_mut().to_string(v)?,
  };
  scope.push_root(Value::String(sep))?;
  let sep_slice = scope.heap().get_string(sep)?.as_code_units();
  let mut sep_units: Vec<u16> = Vec::new();
  sep_units
    .try_reserve_exact(sep_slice.len())
    .map_err(|_| VmError::OutOfMemory)?;
  vec_try_extend_from_slice(&mut sep_units, sep_slice)?;

  let empty = scope.alloc_string("")?;
  scope.push_root(Value::String(empty))?;

  let mut out: Vec<u16> = Vec::new();
  let max_bytes = scope.heap().limits().max_bytes;

  for i in 0..len {
    if i % 1024 == 0 {
      vm.tick()?;
    }

    if i > 0 {
      if JsString::heap_size_bytes_for_len(out.len().saturating_add(sep_units.len())) > max_bytes {
        return Err(VmError::OutOfMemory);
      }
      vec_try_extend_from_slice(&mut out, &sep_units)?;
    }

    let key = PropertyKey::from_string(scope.alloc_string(&i.to_string())?);
    let value = get_data_property_value(scope, this_obj, &key)?.unwrap_or(Value::Undefined);
    let part = match value {
      Value::Undefined | Value::Null => empty,
      other => scope.heap_mut().to_string(other)?,
    };

    let units = scope.heap().get_string(part)?.as_code_units();
    if JsString::heap_size_bytes_for_len(out.len().saturating_add(units.len())) > max_bytes {
      return Err(VmError::OutOfMemory);
    }
    vec_try_extend_from_slice(&mut out, units)?;
  }

  let s = scope.alloc_string_from_u16_vec(out)?;
  Ok(Value::String(s))
}

/// `String` constructor called as a function.
pub fn string_constructor_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let s = match args.first().copied() {
    None => scope.alloc_string("")?,
    Some(v) => scope.heap_mut().to_string(v)?,
  };
  Ok(Value::String(s))
}

/// `new String(value)` (minimal wrapper object).
pub fn string_constructor_construct(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  args: &[Value],
  new_target: Value,
) -> Result<Value, VmError> {
  let intr = require_intrinsics(vm)?;
  let prim = match args.first().copied() {
    None => scope.alloc_string("")?,
    Some(v) => scope.heap_mut().to_string(v)?,
  };
  scope.push_root(Value::String(prim))?;

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj))?;
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(intr.string_prototype()))?;

  // Store the primitive value on an internal symbol so `String.prototype.toString` can recover it.
  let marker = scope.alloc_string("vm-js.internal.StringData")?;
  let marker_sym = scope.heap_mut().symbol_for(marker)?;
  let marker_key = PropertyKey::from_symbol(marker_sym);
  scope.define_property(
    obj,
    marker_key,
    data_desc(Value::String(prim), true, false, false),
  )?;

  // Best-effort: if `new_target.prototype` is an object, use it.
  if let Value::Object(nt) = new_target {
    let proto_key = string_key(scope, "prototype")?;
    if let Ok(Value::Object(p)) = scope.heap().get(nt, &proto_key) {
      scope.heap_mut().object_set_prototype(obj, Some(p))?;
    }
  }

  Ok(Value::Object(obj))
}

/// `String.prototype.toString` (minimal).
pub fn string_prototype_to_string(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  match this {
    Value::String(s) => Ok(Value::String(s)),
    Value::Object(obj) => {
      let marker = scope.alloc_string("vm-js.internal.StringData")?;
      let marker_sym = scope.heap_mut().symbol_for(marker)?;
      let marker_key = PropertyKey::from_symbol(marker_sym);
      match scope.heap().object_get_own_data_property_value(obj, &marker_key)? {
        Some(Value::String(s)) => Ok(Value::String(s)),
        _ => Err(VmError::Unimplemented("String.prototype.toString on non-String object")),
      }
    }
    _ => Err(VmError::Unimplemented("String.prototype.toString on non-string")),
  }
}

/// `Symbol(description)`.
pub fn symbol_constructor_call(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let desc = match args.first().copied() {
    None | Some(Value::Undefined) => None,
    Some(v) => Some(scope.heap_mut().to_string(v)?),
  };
  let sym = scope.new_symbol(desc)?;
  Ok(Value::Symbol(sym))
}

fn concat_with_colon_space(name: &[u16], message: &[u16]) -> Result<Vec<u16>, VmError> {
  let mut out: Vec<u16> = Vec::new();
  out
    .try_reserve(name.len().saturating_add(2).saturating_add(message.len()))
    .map_err(|_| VmError::OutOfMemory)?;
  vec_try_extend_from_slice(&mut out, name)?;
  vec_try_push(&mut out, b':' as u16)?;
  vec_try_push(&mut out, b' ' as u16)?;
  vec_try_extend_from_slice(&mut out, message)?;
  Ok(out)
}

/// `Error.prototype.toString` (minimal).
pub fn error_prototype_to_string(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let this_obj = match this {
    Value::Object(o) => o,
    _ => return Err(VmError::Unimplemented("Error.prototype.toString on non-object")),
  };

  let name_key = string_key(scope, "name")?;
  let message_key = string_key(scope, "message")?;

  let name_value = get_data_property_value(scope, this_obj, &name_key)?.unwrap_or(Value::Undefined);
  let message_value =
    get_data_property_value(scope, this_obj, &message_key)?.unwrap_or(Value::Undefined);

  let name = match name_value {
    Value::Undefined => scope.alloc_string("Error")?,
    other => scope.heap_mut().to_string(other)?,
  };
  scope.push_root(Value::String(name))?;

  let message = match message_value {
    Value::Undefined => scope.alloc_string("")?,
    other => scope.heap_mut().to_string(other)?,
  };
  scope.push_root(Value::String(message))?;

  let name_units = scope.heap().get_string(name)?.as_code_units();
  let message_units = scope.heap().get_string(message)?.as_code_units();

  if name_units.is_empty() {
    return Ok(Value::String(message));
  }
  if message_units.is_empty() {
    return Ok(Value::String(name));
  }

  let out = concat_with_colon_space(name_units, message_units)?;
  let s = scope.alloc_string_from_u16_vec(out)?;
  Ok(Value::String(s))
}

/// `JSON.stringify` (minimal).
pub fn json_stringify(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  const QUOTE: u16 = b'"' as u16;
  const BACKSLASH: u16 = b'\\' as u16;

  fn push_u16_ascii(buf: &mut Vec<u16>, s: &[u8]) -> Result<(), VmError> {
    for &b in s {
      vec_try_push(buf, b as u16)?;
    }
    Ok(())
  }

  fn push_hex_escape(buf: &mut Vec<u16>, unit: u16) -> Result<(), VmError> {
    vec_try_push(buf, b'\\' as u16)?;
    vec_try_push(buf, b'u' as u16)?;
    let mut n = unit;
    let mut digits = [0u16; 4];
    for d in digits.iter_mut().rev() {
      let nibble = (n & 0xF) as u8;
      let c = match nibble {
        0..=9 => b'0' + nibble,
        10..=15 => b'a' + (nibble - 10),
        _ => b'0',
      };
      *d = c as u16;
      n >>= 4;
    }
    vec_try_extend_from_slice(buf, &digits)?;
    Ok(())
  }

  let value = args.first().copied().unwrap_or(Value::Undefined);

  let out = match value {
    Value::Undefined => return Ok(Value::Undefined),
    Value::Null => return Ok(Value::String(scope.alloc_string("null")?)),
    Value::Bool(true) => return Ok(Value::String(scope.alloc_string("true")?)),
    Value::Bool(false) => return Ok(Value::String(scope.alloc_string("false")?)),
    Value::Number(n) => {
      if n.is_nan() || n.is_infinite() {
        return Ok(Value::String(scope.alloc_string("null")?));
      }
      let s = n.to_string();
      return Ok(Value::String(scope.alloc_string(&s)?));
    }
    Value::String(s) => s,
    Value::Symbol(_) | Value::Object(_) => return Ok(Value::Undefined),
  };

  let max_bytes = scope.heap().limits().max_bytes;
  let units = scope.heap().get_string(out)?.as_code_units();

  let mut buf: Vec<u16> = Vec::new();
  vec_try_push(&mut buf, QUOTE)?;

  for (i, &unit) in units.iter().enumerate() {
    if i % 1024 == 0 {
      vm.tick()?;
    }
    if JsString::heap_size_bytes_for_len(buf.len().saturating_add(6)) > max_bytes {
      return Err(VmError::OutOfMemory);
    }

    match unit {
      QUOTE => push_u16_ascii(&mut buf, b"\\\"")?,
      BACKSLASH => push_u16_ascii(&mut buf, b"\\\\")?,
      0x08 => push_u16_ascii(&mut buf, b"\\b")?,
      0x0C => push_u16_ascii(&mut buf, b"\\f")?,
      0x0A => push_u16_ascii(&mut buf, b"\\n")?,
      0x0D => push_u16_ascii(&mut buf, b"\\r")?,
      0x09 => push_u16_ascii(&mut buf, b"\\t")?,
      0x0000..=0x001F => push_hex_escape(&mut buf, unit)?,
      0xD800..=0xDFFF => push_hex_escape(&mut buf, unit)?,
      other => vec_try_push(&mut buf, other)?,
    }
  }

  vec_try_push(&mut buf, QUOTE)?;
  if JsString::heap_size_bytes_for_len(buf.len()) > max_bytes {
    return Err(VmError::OutOfMemory);
  }
  let out = scope.alloc_string_from_u16_vec(buf)?;
  Ok(Value::String(out))
}
