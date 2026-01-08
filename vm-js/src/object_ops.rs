use crate::property::{PropertyDescriptor, PropertyDescriptorPatch, PropertyKey, PropertyKind};
use crate::{GcObject, Scope, Value, VmError};

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
    self.push_root(Value::Object(obj));
    root_property_key(self, key);
    root_descriptor_patch(self, &desc);

    let current = self.heap().object_get_own_property(obj, &key)?;
    let extensible = self.heap().object_is_extensible(obj)?;

    validate_and_apply_property_descriptor(self, Some(obj), key, extensible, desc, current)
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
            // TODO: once function calling exists, invoke the getter with `receiver` as `this`.
            let _ = receiver;
            Err(VmError::Unimplemented(
              "OrdinaryGet: calling accessor getter requires function calling",
            ))
          }
        }
      };
    }
  }

  /// ECMAScript `[[Set]]` for ordinary objects.
  pub fn ordinary_set(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
    receiver: Value,
  ) -> Result<bool, VmError> {
    self.push_root(Value::Object(obj));
    root_property_key(self, key);
    self.push_root(value);
    self.push_root(receiver);

    let own_desc = self.ordinary_get_own_property(obj, key)?;
    ordinary_set_with_own_descriptor(self, obj, key, value, receiver, own_desc)
  }

  /// ECMAScript `[[Delete]]` for ordinary objects.
  pub fn ordinary_delete(&mut self, obj: GcObject, key: PropertyKey) -> Result<bool, VmError> {
    self.push_root(Value::Object(obj));
    root_property_key(self, key);

    let Some(current) = self.heap().object_get_own_property(obj, &key)? else {
      return Ok(true);
    };

    if !current.configurable {
      return Ok(false);
    }

    let _ = self
      .heap_mut()
      .object_delete_own_property(obj, &key)?;
    Ok(true)
  }

  /// ECMAScript `[[OwnPropertyKeys]]` for ordinary objects.
  pub fn ordinary_own_property_keys(&self, obj: GcObject) -> Result<Vec<PropertyKey>, VmError> {
    let keys = self.heap().object_keys_in_insertion_order(obj)?;

    let mut index_keys: Vec<(u32, PropertyKey)> = Vec::new();
    let mut string_keys: Vec<PropertyKey> = Vec::new();
    let mut symbol_keys: Vec<PropertyKey> = Vec::new();

    for key in keys {
      match key {
        PropertyKey::String(_) => match array_index(self.heap(), &key) {
          Some(idx) => index_keys.push((idx, key)),
          None => string_keys.push(key),
        },
        PropertyKey::Symbol(_) => symbol_keys.push(key),
      }
    }

    index_keys.sort_by_key(|(idx, _)| *idx);

    let mut out = Vec::with_capacity(index_keys.len() + string_keys.len() + symbol_keys.len());
    out.extend(index_keys.into_iter().map(|(_, k)| k));
    out.extend(string_keys);
    out.extend(symbol_keys);
    Ok(out)
  }

  pub fn create_data_property(
    &mut self,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
  ) -> Result<bool, VmError> {
    self.ordinary_define_own_property(
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

fn root_descriptor_patch(scope: &mut Scope<'_>, desc: &PropertyDescriptorPatch) {
  if let Some(v) = desc.value {
    scope.push_root(v);
  }
  if let Some(v) = desc.get {
    scope.push_root(v);
  }
  if let Some(v) = desc.set {
    scope.push_root(v);
  }
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
      Some(parent) => return scope.ordinary_set(parent, key, value, receiver),
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

  let own_desc = own_desc.expect("own_desc set above");

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
        let PropertyKind::Data {
          writable: receiver_writable,
          ..
        } = existing_desc.kind
        else {
          unreachable!("checked accessor above");
        };
        if !receiver_writable {
          return Ok(false);
        }

        return scope.ordinary_define_own_property(
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
      // TODO: once function calling exists, invoke the setter with `receiver` as `this`.
      Err(VmError::Unimplemented(
        "OrdinarySetWithOwnDescriptor: calling accessor setter requires function calling",
      ))
    }
  }
}

fn array_index(heap: &crate::Heap, key: &PropertyKey) -> Option<u32> {
  let PropertyKey::String(s) = key else {
    return None;
  };
  let s = heap.get_string(*s).ok()?;
  let units = s.as_code_units();
  if units.is_empty() {
    return None;
  }

  const U0: u16 = b'0' as u16;
  const U9: u16 = b'9' as u16;

  // `ToString(ToUint32(P)) === P` implies no leading zeros (except the single "0").
  if units.len() > 1 && units[0] == U0 {
    return None;
  }

  let mut value: u64 = 0;
  for &u in units {
    if !(U0..=U9).contains(&u) {
      return None;
    }
    value = value.checked_mul(10)?;
    value = value.checked_add((u - U0) as u64)?;
    if value > u32::MAX as u64 {
      return None;
    }
  }

  // Exclude 2^32-1.
  if value == u32::MAX as u64 {
    return None;
  }
  Some(value as u32)
}
