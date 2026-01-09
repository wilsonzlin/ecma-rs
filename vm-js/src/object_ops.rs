use crate::property::{PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind};
use crate::{GcObject, Scope, Value, Vm, VmError};

impl<'a> Scope<'a> {
  pub fn object_get_prototype(&self, obj: GcObject) -> Result<Option<GcObject>, VmError> {
    self.heap().object_prototype(obj)
  }

  pub fn object_set_prototype(
    &mut self,
    obj: GcObject,
    prototype: Option<GcObject>,
  ) -> Result<(), VmError> {
    self.heap_mut().object_set_prototype(obj, prototype)
  }

  pub fn object_is_extensible(&self, obj: GcObject) -> Result<bool, VmError> {
    self.heap().object_is_extensible(obj)
  }

  pub fn object_prevent_extensions(&mut self, obj: GcObject) -> Result<(), VmError> {
    self.heap_mut().object_set_extensible(obj, false)
  }

  /// ECMAScript `[[GetOwnProperty]]` for ordinary objects.
  pub fn ordinary_get_own_property(
    &self,
    obj: GcObject,
    key: PropertyKey,
  ) -> Result<Option<PropertyDescriptor>, VmError> {
    self.heap().object_get_own_property(obj, &key)
  }

  /// ECMAScript `[[DefineOwnProperty]]` for ordinary objects.
  pub fn ordinary_define_own_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<bool, VmError> {
    desc.validate()?;

    // Root all inputs that might be written into the heap before any allocation/GC.
    self.push_root(Value::Object(obj))?;
    root_property_key(self, key)?;
    root_descriptor_patch(self, &desc)?;

    let current = self.heap().object_get_own_property(obj, &key)?;
    let extensible = self.heap().object_is_extensible(obj)?;

    validate_and_apply_property_descriptor(self, Some(obj), key, extensible, desc, current)
  }

  /// ECMAScript `[[DefineOwnProperty]]`.
  ///
  /// This dispatches to the appropriate exotic object's `[[DefineOwnProperty]]` algorithm.
  pub fn define_own_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<bool, VmError> {
    if self.heap().object_is_array(obj)? {
      self.array_define_own_property(obj, key, desc)
    } else {
      self.ordinary_define_own_property(obj, key, desc)
    }
  }

  /// ECMAScript `DefinePropertyOrThrow`.
  ///
  /// This is a convenience wrapper around [`Scope::define_own_property`]. If the
  /// definition is rejected (`false`), this returns a `TypeError`.
  pub fn define_property_or_throw(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<(), VmError> {
    let ok = self.define_own_property(obj, key, desc)?;
    if ok {
      Ok(())
    } else {
      Err(VmError::TypeError("DefinePropertyOrThrow rejected"))
    }
  }

  /// ECMAScript `[[HasProperty]]` for ordinary objects.
  pub fn ordinary_has_property(&self, obj: GcObject, key: PropertyKey) -> Result<bool, VmError> {
    if self.ordinary_get_own_property(obj, key)?.is_some() {
      return Ok(true);
    }
    match self.object_get_prototype(obj)? {
      Some(parent) => self.ordinary_has_property(parent, key),
      None => Ok(false),
    }
  }

  /// ECMAScript `[[Get]]` for ordinary objects.
  pub fn ordinary_get(
    &mut self,
    vm: &mut Vm,
    mut obj: GcObject,
    key: PropertyKey,
    receiver: Value,
  ) -> Result<Value, VmError> {
    loop {
      let desc = self.ordinary_get_own_property(obj, key)?;
      let Some(desc) = desc else {
        match self.object_get_prototype(obj)? {
          Some(parent) => {
            obj = parent;
            continue;
          }
          None => return Ok(Value::Undefined),
        }
      };

      return match desc.kind {
        PropertyKind::Data { value, .. } => Ok(value),
        PropertyKind::Accessor { get, .. } => {
          if matches!(get, Value::Undefined) {
            Ok(Value::Undefined)
          } else {
            if !self.heap().is_callable(get)? {
              return Err(VmError::TypeError("accessor getter is not callable"));
            }
            vm.call(self, get, receiver, &[])
          }
        }
      };
    }
  }

  /// ECMAScript `[[Set]]` for ordinary objects.
  pub fn ordinary_set(
    &mut self,
    vm: &mut Vm,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
    receiver: Value,
  ) -> Result<bool, VmError> {
    self.push_root(Value::Object(obj))?;
    root_property_key(self, key)?;
    self.push_root(value)?;
    self.push_root(receiver)?;

    let own_desc = self.ordinary_get_own_property(obj, key)?;
    ordinary_set_with_own_descriptor(vm, self, obj, key, value, receiver, own_desc)
  }

  /// ECMAScript `[[Delete]]` for ordinary objects.
  pub fn ordinary_delete(&mut self, obj: GcObject, key: PropertyKey) -> Result<bool, VmError> {
    self.push_root(Value::Object(obj))?;
    root_property_key(self, key)?;
    self.heap_mut().ordinary_delete(obj, key)
  }

  /// ECMAScript `[[OwnPropertyKeys]]` for ordinary objects.
  pub fn ordinary_own_property_keys(&self, obj: GcObject) -> Result<Vec<PropertyKey>, VmError> {
    self.heap().ordinary_own_property_keys(obj)
  }

  pub fn create_data_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
  ) -> Result<bool, VmError> {
    self.define_own_property(
      obj,
      key,
      PropertyDescriptorPatch {
        value: Some(value),
        writable: Some(true),
        enumerable: Some(true),
        configurable: Some(true),
        ..Default::default()
      },
    )
  }

  pub fn create_data_property_or_throw(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
  ) -> Result<(), VmError> {
    let ok = self.create_data_property(obj, key, value)?;
    if ok {
      Ok(())
    } else {
      Err(VmError::TypeError("CreateDataProperty rejected"))
    }
  }

  fn array_define_own_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<bool, VmError> {
    desc.validate()?;

    // Root all inputs that might be written into the heap before any allocation/GC.
    self.push_root(Value::Object(obj))?;
    root_property_key(self, key)?;
    root_descriptor_patch(self, &desc)?;

    if self.heap().property_key_is_length(&key) {
      let length_key = self.heap().array_length_key(obj)?;
      return self.array_set_length(obj, length_key, desc);
    }

    if let Some(index) = self.heap().array_index(&key) {
      let old_len = self.heap().array_length(obj)?;
      if index >= old_len && !self.heap().array_length_writable(obj)? {
        return Ok(false);
      }

      let succeeded = self.ordinary_define_own_property(obj, key, desc)?;
      if !succeeded {
        return Ok(false);
      }

      if index >= old_len {
        let new_len = index
          .checked_add(1)
          .ok_or(VmError::InvariantViolation("array index overflow"))?;
        self.heap_mut().array_set_length(obj, new_len)?;
      }

      return Ok(true);
    }

    self.ordinary_define_own_property(obj, key, desc)
  }

  fn array_set_length(
    &mut self,
    obj: GcObject,
    length_key: PropertyKey,
    desc: PropertyDescriptorPatch,
  ) -> Result<bool, VmError> {
    // If `Desc` does not specify a new length value, this is just a property definition on the
    // existing `length` data property (typically toggling writability).
    let Some(value) = desc.value else {
      return self.ordinary_define_own_property(obj, length_key, desc);
    };

    let Some(new_len) = array_length_from_value(value) else {
      return Ok(false);
    };

    let old_len = self.heap().array_length(obj)?;

    // Extending `length` is just an ordinary property definition.
    if new_len >= old_len {
      let mut new_desc = desc;
      new_desc.value = Some(Value::Number(new_len as f64));
      return self.ordinary_define_own_property(obj, length_key, new_desc);
    }

    // Shrinking: reject if `length` is not writable.
    if !self.heap().array_length_writable(obj)? {
      return Ok(false);
    }

    // If the caller is requesting `writable: false`, the spec requires performing deletions while
    // `length` is still writable so we can restore `length` on failure.
    let mut new_writable = true;
    let mut new_len_desc = desc;
    if matches!(new_len_desc.writable, Some(false)) {
      new_writable = false;
      new_len_desc.writable = Some(true);
    }
    new_len_desc.value = Some(Value::Number(new_len as f64));

    let succeeded = self.ordinary_define_own_property(obj, length_key, new_len_desc)?;
    if !succeeded {
      return Ok(false);
    }

    // Delete existing array index properties >= newLen, in descending order.
    //
    // `OrdinaryOwnPropertyKeys` already sorts indices numerically, so iterating the resulting list
    // in reverse deletes indices from high to low.
    let keys = self.ordinary_own_property_keys(obj)?;
    for key in keys.into_iter().rev() {
      let Some(index) = self.heap().array_index(&key) else {
        continue;
      };
      if index < new_len {
        break;
      }
      if index >= old_len {
        continue;
      }

      let delete_ok = self.ordinary_delete(obj, key)?;
      if delete_ok {
        continue;
      }

      // Failed to delete a non-configurable element: restore `length` to `index + 1` and (if
      // requested) make it non-writable.
      let restore_len = index
        .checked_add(1)
        .ok_or(VmError::InvariantViolation("array index overflow"))?;

      let ok = self.ordinary_define_own_property(
        obj,
        length_key,
        PropertyDescriptorPatch {
          value: Some(Value::Number(restore_len as f64)),
          ..Default::default()
        },
      )?;
      if !ok {
        return Err(VmError::InvariantViolation(
          "array length restoration via OrdinaryDefineOwnProperty failed",
        ));
      }
      if !new_writable {
        self.heap_mut().array_set_length_writable(obj, false)?;
      }
      return Ok(false);
    }

    if !new_writable {
      self.heap_mut().array_set_length_writable(obj, false)?;
    }

    Ok(true)
  }
}

fn array_length_from_value(value: Value) -> Option<u32> {
  let Value::Number(n) = value else {
    return None;
  };
  if !n.is_finite() {
    return None;
  }
  if n < 0.0 {
    return None;
  }
  if n.fract() != 0.0 {
    return None;
  }
  if n > u32::MAX as f64 {
    return None;
  }
  Some(n as u32)
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

fn root_descriptor_patch(scope: &mut Scope<'_>, desc: &PropertyDescriptorPatch) -> Result<(), VmError> {
  if let Some(v) = desc.value {
    scope.push_root(v)?;
  }
  if let Some(v) = desc.get {
    scope.push_root(v)?;
  }
  if let Some(v) = desc.set {
    scope.push_root(v)?;
  }
  Ok(())
}

fn validate_and_apply_property_descriptor(
  scope: &mut Scope<'_>,
  obj: Option<GcObject>,
  key: PropertyKey,
  extensible: bool,
  desc: PropertyDescriptorPatch,
  current: Option<PropertyDescriptor>,
) -> Result<bool, VmError> {
  desc.validate()?;

  let Some(current_desc) = current else {
    if !extensible {
      return Ok(false);
    }

    // Create new property with default attributes for missing fields.
    let enumerable = desc.enumerable.unwrap_or(false);
    let configurable = desc.configurable.unwrap_or(false);
    let new_desc = if desc.is_accessor_descriptor() {
      PropertyDescriptor {
        enumerable,
        configurable,
        kind: PropertyKind::Accessor {
          get: desc.get.unwrap_or(Value::Undefined),
          set: desc.set.unwrap_or(Value::Undefined),
        },
      }
    } else {
      // Generic descriptors create data properties.
      PropertyDescriptor {
        enumerable,
        configurable,
        kind: PropertyKind::Data {
          value: desc.value.unwrap_or(Value::Undefined),
          writable: desc.writable.unwrap_or(false),
        },
      }
    };

    if let Some(obj) = obj {
      scope.define_property(obj, key, new_desc)?;
    }
    return Ok(true);
  };

  // If `Desc` has no fields, no change is requested.
  if desc.is_empty() {
    return Ok(true);
  }

  // Non-configurable invariants.
  if !current_desc.configurable {
    if matches!(desc.configurable, Some(true)) {
      return Ok(false);
    }
    if let Some(enumerable) = desc.enumerable {
      if enumerable != current_desc.enumerable {
        return Ok(false);
      }
    }
  }

  let desc_is_generic = desc.is_generic_descriptor();
  let desc_is_data = desc.is_data_descriptor();
  let desc_is_accessor = desc.is_accessor_descriptor();

  let current_is_data = current_desc.is_data_descriptor();
  let current_is_accessor = current_desc.is_accessor_descriptor();

  // Reject kind switches when not configurable.
  if !current_desc.configurable && !desc_is_generic {
    if (current_is_data && desc_is_accessor) || (current_is_accessor && desc_is_data) {
      return Ok(false);
    }
  }

  if !desc_is_generic {
    match (&current_desc.kind, current_desc.configurable) {
      (PropertyKind::Data { value, writable }, false) if desc_is_data => {
        if !writable {
          if desc.writable == Some(true) {
            return Ok(false);
          }
          if let Some(new_value) = desc.value {
            if !new_value.same_value(*value, scope.heap()) {
              return Ok(false);
            }
          }
        }
      }
      (PropertyKind::Accessor { get, set }, false) if desc_is_accessor => {
        if let Some(new_get) = desc.get {
          if !new_get.same_value(*get, scope.heap()) {
            return Ok(false);
          }
        }
        if let Some(new_set) = desc.set {
          if !new_set.same_value(*set, scope.heap()) {
            return Ok(false);
          }
        }
      }
      _ => {}
    }
  }

  if let Some(obj) = obj {
    let new_desc = apply_descriptor_patch(current_desc, desc);
    scope.define_property(obj, key, new_desc)?;
  }

  Ok(true)
}

fn apply_descriptor_patch(current: PropertyDescriptor, desc: PropertyDescriptorPatch) -> PropertyDescriptor {
  let enumerable = desc.enumerable.unwrap_or(current.enumerable);
  let configurable = desc.configurable.unwrap_or(current.configurable);

  if desc.is_generic_descriptor() {
    return PropertyDescriptor {
      enumerable,
      configurable,
      kind: current.kind,
    };
  }

  match (current.kind, desc.is_accessor_descriptor()) {
    (PropertyKind::Data { value, writable }, false) => PropertyDescriptor {
      enumerable,
      configurable,
      kind: PropertyKind::Data {
        value: desc.value.unwrap_or(value),
        writable: desc.writable.unwrap_or(writable),
      },
    },
    (PropertyKind::Accessor { get, set }, true) => PropertyDescriptor {
      enumerable,
      configurable,
      kind: PropertyKind::Accessor {
        get: desc.get.unwrap_or(get),
        set: desc.set.unwrap_or(set),
      },
    },
    // Kind conversions. Default values are per `ValidateAndApplyPropertyDescriptor`.
    (PropertyKind::Data { .. }, true) => PropertyDescriptor {
      enumerable,
      configurable,
      kind: PropertyKind::Accessor {
        get: desc.get.unwrap_or(Value::Undefined),
        set: desc.set.unwrap_or(Value::Undefined),
      },
    },
    (PropertyKind::Accessor { .. }, false) => PropertyDescriptor {
      enumerable,
      configurable,
      kind: PropertyKind::Data {
        value: desc.value.unwrap_or(Value::Undefined),
        writable: desc.writable.unwrap_or(false),
      },
    },
  }
}

fn ordinary_set_with_own_descriptor(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  obj: GcObject,
  key: PropertyKey,
  value: Value,
  receiver: Value,
  own_desc: Option<PropertyDescriptor>,
) -> Result<bool, VmError> {
  let mut own_desc = own_desc;

  if own_desc.is_none() {
    match scope.object_get_prototype(obj)? {
      Some(parent) => return scope.ordinary_set(vm, parent, key, value, receiver),
      None => {
        own_desc = Some(PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Data {
            value: Value::Undefined,
            writable: true,
          },
        });
      }
    }
  }

  let Some(own_desc) = own_desc else {
    return Err(VmError::Unimplemented(
      "ordinary_set: missing own property descriptor",
    ));
  };

  match own_desc.kind {
    PropertyKind::Data { writable, .. } => {
      if !writable {
        return Ok(false);
      }
      let Value::Object(receiver_obj) = receiver else {
        return Ok(false);
      };

      let existing_desc = scope.ordinary_get_own_property(receiver_obj, key)?;
      if let Some(existing_desc) = existing_desc {
        if existing_desc.is_accessor_descriptor() {
          return Ok(false);
        }
        let receiver_writable = match existing_desc.kind {
          PropertyKind::Data { writable, .. } => writable,
          PropertyKind::Accessor { .. } => return Ok(false),
        };
        if !receiver_writable {
          return Ok(false);
        }

        return scope.define_own_property(
          receiver_obj,
          key,
          PropertyDescriptorPatch {
            value: Some(value),
            ..Default::default()
          },
        );
      }

      scope.create_data_property(receiver_obj, key, value)
    }
    PropertyKind::Accessor { set, .. } => {
      if matches!(set, Value::Undefined) {
        return Ok(false);
      }
      if !scope.heap().is_callable(set)? {
        return Err(VmError::TypeError("accessor setter is not callable"));
      }
      let _ = vm.call(scope, set, receiver, &[value])?;
      Ok(true)
    }
  }
}
