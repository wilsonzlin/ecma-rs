use crate::function::FunctionData;
use crate::property::{PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind};
use crate::{
  GcObject, Job, JobCallback, JobKind, PromiseCapability, PromiseReaction, PromiseReactionType,
  PromiseState, Scope, Value, Vm, VmError,
};

fn data_desc(value: Value, writable: bool, enumerable: bool, configurable: bool) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable,
    configurable,
    kind: PropertyKind::Data { value, writable },
  }
}

fn require_intrinsics(vm: &Vm) -> Result<crate::Intrinsics, VmError> {
  vm.intrinsics()
    .ok_or(VmError::Unimplemented("native builtins require Vm::intrinsics to be set"))
}

fn require_object(value: Value) -> Result<GcObject, VmError> {
  match value {
    Value::Object(o) => Ok(o),
    _ => Err(VmError::TypeError("expected object")),
  }
}

fn root_property_key(scope: &mut Scope<'_>, key: PropertyKey) {
  match key {
    PropertyKey::String(s) => {
      scope.push_root(Value::String(s));
    }
    PropertyKey::Symbol(s) => {
      scope.push_root(Value::Symbol(s));
    }
  }
}

fn get_own_data_property_value_by_name(
  scope: &mut Scope<'_>,
  obj: GcObject,
  name: &str,
) -> Result<Option<Value>, VmError> {
  let mut scope = scope.reborrow();
  scope.push_root(Value::Object(obj));
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

fn object_constructor_impl(vm: &mut Vm, scope: &mut Scope<'_>, args: &[Value]) -> Result<Value, VmError> {
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
  scope.push_root(Value::Object(target));

  let prop = args.get(1).copied().unwrap_or(Value::Undefined);
  let key = scope.heap_mut().to_property_key(prop)?;
  root_property_key(&mut scope, key);

  let desc_obj = require_object(args.get(2).copied().unwrap_or(Value::Undefined))?;
  scope.push_root(Value::Object(desc_obj));

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
    _ => return Err(VmError::TypeError("Object.create prototype must be an object or null")),
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
    idx_scope.push_root(Value::Object(array));
    idx_scope.push_root(Value::String(name));

    let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
    idx_scope.define_property(array, key, data_desc(Value::String(name), true, true, true))?;
  }

  Ok(Value::Object(array))
}

pub fn object_assign(
  _vm: &mut Vm,
  scope: &mut Scope<'_>,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let target = require_object(args.get(0).copied().unwrap_or(Value::Undefined))?;

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

      let value = match desc.kind {
        PropertyKind::Data { value, .. } => value,
        PropertyKind::Accessor { .. } => {
          return Err(VmError::Unimplemented(
            "Object.assign does not yet support accessor properties",
          ));
        }
      };

      scope.define_property(target, key, data_desc(value, true, true, true))?;
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
    _ => return Err(VmError::TypeError("Object.setPrototypeOf prototype must be an object or null")),
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

fn array_constructor_impl(vm: &mut Vm, scope: &mut Scope<'_>, args: &[Value]) -> Result<Value, VmError> {
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
        idx_scope.push_root(Value::Object(array));
        idx_scope.push_root(el);

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
  scope.push_root(Value::String(message_string));

  let obj = scope.alloc_object()?;
  scope.push_root(Value::Object(obj));
  scope
    .heap_mut()
    .object_set_prototype(obj, Some(instance_prototype))?;

  let name_key = PropertyKey::from_string(scope.alloc_string("name")?);
  scope.define_property(obj, name_key, data_desc(Value::String(name), true, false, true))?;

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
  scope.push_root(Value::String(msg));

  let err = error_constructor_construct(
    vm,
    scope,
    ctor,
    &[Value::String(msg)],
    Value::Object(ctor),
  )?;
  Err(VmError::Throw(err))
}

fn new_promise(vm: &mut Vm, scope: &mut Scope<'_>) -> Result<GcObject, VmError> {
  let intr = require_intrinsics(vm)?;
  scope.alloc_promise_with_prototype(Some(intr.promise_prototype()))
}

fn create_promise_resolving_functions(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  promise: GcObject,
) -> Result<(Value, Value), VmError> {
  let intr = require_intrinsics(vm)?;
  let call_id = intr.promise_resolving_function_call();

  // Root the promise while allocating the resolving functions.
  scope.push_root(Value::Object(promise));

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

  let mut job = Job::new(JobKind::Promise, move |ctx, host| {
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

  // Root captured GC values for the lifetime of the queued job.
  job.push_root(scope.heap_mut().add_root(argument));
  if let Some(handler) = handler_callback_object {
    job.push_root(scope.heap_mut().add_root(Value::Object(handler)));
  }
  if let Some(cap) = capability {
    job.push_root(scope.heap_mut().add_root(Value::Object(cap.promise)));
    job.push_root(scope.heap_mut().add_root(cap.resolve));
    job.push_root(scope.heap_mut().add_root(cap.reject));
  }

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

fn fulfill_promise(vm: &mut Vm, scope: &mut Scope<'_>, promise: GcObject, value: Value) -> Result<(), VmError> {
  let (fulfill_reactions, _reject_reactions) = scope
    .heap_mut()
    .promise_settle_and_take_reactions(promise, PromiseState::Fulfilled, value)?;
  trigger_promise_reactions(vm, scope, fulfill_reactions, value)
}

fn reject_promise(vm: &mut Vm, scope: &mut Scope<'_>, promise: GcObject, reason: Value) -> Result<(), VmError> {
  let (_fulfill_reactions, reject_reactions) = scope
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
  scope.push_root(Value::Object(promise));

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
    return Err(VmError::Unimplemented("promise resolving function internal slots"));
  };

  if is_reject {
    reject_promise(vm, scope, promise, resolution)?;
  } else {
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
    Value::Object(obj) if scope.heap().is_callable(Value::Object(obj))? => Some(JobCallback::new(obj)),
    _ => None,
  };
  let on_rejected = match on_rejected {
    Value::Object(obj) if scope.heap().is_callable(Value::Object(obj))? => Some(JobCallback::new(obj)),
    _ => None,
  };

  // Create the derived promise + capability.
  let result_promise = scope
    .alloc_promise_with_prototype(Some(intr.promise_prototype()))?;
  scope.push_root(Value::Object(result_promise));
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
      let arg = scope.heap().promise_result(promise)?.unwrap_or(Value::Undefined);
      enqueue_promise_reaction_job(vm, scope, fulfill_reaction, arg)?;
    }
    PromiseState::Rejected => {
      let arg = scope.heap().promise_result(promise)?.unwrap_or(Value::Undefined);
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
