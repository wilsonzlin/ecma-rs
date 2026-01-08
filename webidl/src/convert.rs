use crate::{
  index_to_property_key, AsyncSequence, AsyncSequenceKind, IdlType, IdlValue, JsRuntime, PropertyKey,
  UnionValue, WebIdlError, WebIdlLimit, WellKnownSymbol,
};

/// Cached `@@iterator` method used to avoid re-invoking side-effectful getters during union/overload
/// resolution.
#[derive(Debug, Clone, Copy)]
pub(crate) struct IteratorHint<V> {
  pub method: V,
}

/// Cached `@@asyncIterator`/`@@iterator` method for `async_sequence<T>`.
#[derive(Debug, Clone, Copy)]
pub(crate) enum AsyncIteratorHint<V> {
  Async { method: V },
  Sync { method: V },
}

#[inline]
fn type_error<R: JsRuntime>(rt: &mut R, message: &'static str) -> WebIdlError {
  WebIdlError::js(rt.type_error(message))
}

pub fn convert_js_to_idl<R: JsRuntime>(
  cx: &mut R,
  ty: &IdlType,
  v: R::Value,
) -> Result<IdlValue<R::Value, R::String>, WebIdlError> {
  convert_js_to_idl_with_hints(cx, ty, v, None, None)
}

pub(crate) fn convert_js_to_idl_with_hints<R: JsRuntime>(
  cx: &mut R,
  ty: &IdlType,
  v: R::Value,
  iterator_hint: Option<IteratorHint<R::Value>>,
  async_iterator_hint: Option<AsyncIteratorHint<R::Value>>,
) -> Result<IdlValue<R::Value, R::String>, WebIdlError> {
  match ty {
    IdlType::Undefined => {
      if cx.is_undefined(v) {
        Ok(IdlValue::Undefined)
      } else {
        Err(type_error(cx, "expected undefined"))
      }
    }
    IdlType::Boolean => Ok(IdlValue::Boolean(cx.to_boolean(v).map_err(WebIdlError::js)?)),
    IdlType::Double => Ok(IdlValue::Double(cx.to_number(v).map_err(WebIdlError::js)?)),
    IdlType::DomString => Ok(IdlValue::DomString(cx.to_string(v).map_err(WebIdlError::js)?)),
    IdlType::Object => {
      if cx.is_object(v) {
        Ok(IdlValue::Object(v))
      } else {
        Err(type_error(cx, "expected object"))
      }
    }

    IdlType::Sequence(elem_ty) => {
      let method = if let Some(hint) = iterator_hint {
        hint.method
      } else {
        let obj = match cx.as_object(v) {
          Some(obj) => obj,
          None => return Err(type_error(cx, "sequence: expected object")),
        };
        let iter_sym = cx
          .well_known_symbol(WellKnownSymbol::Iterator)
          .map_err(WebIdlError::js)?;
        cx.get_method(obj, PropertyKey::Symbol(iter_sym))
          .map_err(WebIdlError::js)?
          .ok_or_else(|| type_error(cx, "sequence: object is not iterable"))?
      };

      let values = create_sequence_from_iterable(cx, v, method, elem_ty)?;
      Ok(IdlValue::Sequence(values))
    }

    IdlType::FrozenArray(elem_ty) => {
      let method = if let Some(hint) = iterator_hint {
        hint.method
      } else {
        let obj = match cx.as_object(v) {
          Some(obj) => obj,
          None => return Err(type_error(cx, "FrozenArray: expected object")),
        };
        let iter_sym = cx
          .well_known_symbol(WellKnownSymbol::Iterator)
          .map_err(WebIdlError::js)?;
        cx.get_method(obj, PropertyKey::Symbol(iter_sym))
          .map_err(WebIdlError::js)?
          .ok_or_else(|| type_error(cx, "FrozenArray: object is not iterable"))?
      };

      let values = create_sequence_from_iterable(cx, v, method, elem_ty)?;
      let array_value = create_frozen_array(cx, elem_ty, &values)?;
      Ok(IdlValue::FrozenArray(array_value))
    }

    IdlType::AsyncSequence(_elem_ty) => {
      if !cx.is_object(v) {
        return Err(type_error(cx, "async_sequence: expected object"));
      }

      let hint = if let Some(hint) = async_iterator_hint {
        hint
      } else {
        // Spec: https://webidl.spec.whatwg.org/#js-to-async-iterable
        let obj = cx.as_object(v).unwrap();
        let async_iter_sym = cx
          .well_known_symbol(WellKnownSymbol::AsyncIterator)
          .map_err(WebIdlError::js)?;
        let method = cx
          .get_method(obj, PropertyKey::Symbol(async_iter_sym))
          .map_err(WebIdlError::js)?;
        if let Some(method) = method {
          AsyncIteratorHint::Async { method }
        } else {
          let iter_sym = cx
            .well_known_symbol(WellKnownSymbol::Iterator)
            .map_err(WebIdlError::js)?;
          let sync_method = cx
            .get_method(obj, PropertyKey::Symbol(iter_sym))
            .map_err(WebIdlError::js)?;
          let Some(method) = sync_method else {
            return Err(type_error(
              cx,
              "async_sequence: object is not async iterable nor iterable",
            ));
          };
          AsyncIteratorHint::Sync { method }
        }
      };

      let (method, kind) = match hint {
        AsyncIteratorHint::Async { method } => (method, AsyncSequenceKind::Async),
        AsyncIteratorHint::Sync { method } => (method, AsyncSequenceKind::Sync),
      };

      Ok(IdlValue::AsyncSequence(AsyncSequence {
        object: v,
        method,
        kind,
      }))
    }

    IdlType::Union(_) => convert_js_to_union(cx, ty, v),

    IdlType::Nullable(inner) => {
      if cx.is_null(v) || cx.is_undefined(v) {
        Ok(IdlValue::Null)
      } else {
        convert_js_to_idl(cx, inner, v)
      }
    }
  }
}

pub fn convert_idl_to_js<R: JsRuntime>(
  cx: &mut R,
  ty: &IdlType,
  v: &IdlValue<R::Value, R::String>,
) -> Result<R::Value, WebIdlError> {
  match (ty, v) {
    (IdlType::Undefined, IdlValue::Undefined) => Ok(cx.value_undefined()),
    (IdlType::Nullable(_), IdlValue::Null) => Ok(cx.value_null()),
    (IdlType::Boolean, IdlValue::Boolean(b)) => Ok(cx.value_bool(*b)),
    (IdlType::Double, IdlValue::Double(n)) => Ok(cx.value_number(*n)),
    (IdlType::DomString, IdlValue::DomString(s)) => Ok(cx.value_string(*s)),
    (IdlType::Object, IdlValue::Object(o)) => Ok(*o),

    (IdlType::Sequence(elem_ty), IdlValue::Sequence(elems)) => {
      let js_elems = elems
        .iter()
        .map(|e| convert_idl_to_js(cx, elem_ty, e))
        .collect::<Result<Vec<_>, _>>()?;

      let array_obj = cx.alloc_array(js_elems.len()).map_err(WebIdlError::js)?;
      for (i, el) in js_elems.into_iter().enumerate() {
        let key = index_to_property_key(cx, i)?;
        cx.create_data_property_or_throw(array_obj, key, el)
          .map_err(WebIdlError::js)?;
      }

      Ok(cx.value_object(array_obj))
    }

    (IdlType::FrozenArray(_), IdlValue::FrozenArray(obj)) => Ok(*obj),
    (IdlType::AsyncSequence(_), IdlValue::AsyncSequence(seq)) => Ok(seq.object),

    (IdlType::Union(_), IdlValue::Union(u)) => convert_idl_to_js(cx, &u.selected_type, &u.value),

    _ => Err(type_error(cx, "unsupported idl-to-js conversion")),
  }
}

fn create_sequence_from_iterable<R: JsRuntime>(
  cx: &mut R,
  iterable: R::Value,
  method: R::Value,
  elem_ty: &IdlType,
) -> Result<Vec<IdlValue<R::Value, R::String>>, WebIdlError> {
  let obj = cx
    .as_object(iterable)
    .ok_or_else(|| type_error(cx, "iterable is not an object"))?;
  let iterator = cx
    .get_iterator_from_method(obj, method)
    .map_err(WebIdlError::js)?;

  let mut out = Vec::new();
  while let Some(step_value) = cx
    .iterator_step_value(iterator)
    .map_err(WebIdlError::js)?
  {
    if out.len() >= cx.limits().max_sequence_length {
      return Err(WebIdlError::limit_exceeded(
        WebIdlLimit::MaxSequenceLength,
        out.len() + 1,
        cx.limits().max_sequence_length,
      ));
    }
    out.push(convert_js_to_idl(cx, elem_ty, step_value)?);
  }

  Ok(out)
}

fn create_frozen_array<R: JsRuntime>(
  cx: &mut R,
  elem_ty: &IdlType,
  values: &[IdlValue<R::Value, R::String>],
) -> Result<R::Value, WebIdlError> {
  // Spec: https://webidl.spec.whatwg.org/#dfn-create-frozen-array
  let js_elems = values
    .iter()
    .map(|v| convert_idl_to_js(cx, elem_ty, v))
    .collect::<Result<Vec<_>, _>>()?;

  if js_elems.len() > cx.limits().max_sequence_length {
    return Err(WebIdlError::limit_exceeded(
      WebIdlLimit::MaxSequenceLength,
      js_elems.len(),
      cx.limits().max_sequence_length,
    ));
  }

  let array_obj = cx.alloc_array(js_elems.len()).map_err(WebIdlError::js)?;
  for (i, el) in js_elems.into_iter().enumerate() {
    let key = index_to_property_key(cx, i)?;
    cx.create_data_property_or_throw(array_obj, key, el)
      .map_err(WebIdlError::js)?;
  }
  cx.set_integrity_level_frozen(array_obj)
    .map_err(WebIdlError::js)?;
  Ok(cx.value_object(array_obj))
}

fn convert_js_to_union<R: JsRuntime>(
  cx: &mut R,
  union_ty: &IdlType,
  v: R::Value,
) -> Result<IdlValue<R::Value, R::String>, WebIdlError> {
  let IdlType::Union(_members) = union_ty else {
    unreachable!();
  };

  // Spec: https://webidl.spec.whatwg.org/#js-to-union (partial)
  if union_ty.includes_undefined() && cx.is_undefined(v) {
    return Ok(IdlValue::Union(UnionValue {
      selected_type: IdlType::Undefined,
      value: Box::new(IdlValue::Undefined),
    }));
  }

  let types = union_ty.flattened_member_types();

  if cx.is_null(v) || cx.is_undefined(v) {
    if let Some(nullable_ty) = types.iter().find_map(|t| {
      if matches!(t, IdlType::Nullable(_)) {
        Some((*t).clone())
      } else {
        None
      }
    }) {
      return Ok(IdlValue::Union(UnionValue {
        selected_type: nullable_ty,
        value: Box::new(IdlValue::Null),
      }));
    }
  }

  if cx.is_object(v) {
    // ---- async_sequence special-case ----
    let types_include_string = types.iter().any(|t| t.contains_string_type());

    if let Some(async_seq_ty) = types
      .iter()
      .find_map(|t| if matches!(t, IdlType::AsyncSequence(_)) { Some(*t) } else { None })
    {
      // Distinguishability requirement (d): when a string type is also present, a string object is
      // never converted to async_sequence, even though it might have @@iterator.
      if !types_include_string || !cx.is_string_object(v) {
        let obj = cx.as_object(v).unwrap();

        let async_iter_sym = cx
          .well_known_symbol(WellKnownSymbol::AsyncIterator)
          .map_err(WebIdlError::js)?;
        if let Some(method) = cx
          .get_method(obj, PropertyKey::Symbol(async_iter_sym))
          .map_err(WebIdlError::js)?
        {
          let value = convert_js_to_idl_with_hints(
            cx,
            async_seq_ty,
            v,
            None,
            Some(AsyncIteratorHint::Async { method }),
          )?;
          return Ok(IdlValue::Union(UnionValue {
            selected_type: async_seq_ty.clone(),
            value: Box::new(value),
          }));
        }

        let iter_sym = cx
          .well_known_symbol(WellKnownSymbol::Iterator)
          .map_err(WebIdlError::js)?;
        if let Some(method) = cx
          .get_method(obj, PropertyKey::Symbol(iter_sym))
          .map_err(WebIdlError::js)?
        {
          let value = convert_js_to_idl_with_hints(
            cx,
            async_seq_ty,
            v,
            None,
            Some(AsyncIteratorHint::Sync { method }),
          )?;
          return Ok(IdlValue::Union(UnionValue {
            selected_type: async_seq_ty.clone(),
            value: Box::new(value),
          }));
        }
      }
    }

    // ---- sequence<T> ----
    if let Some(seq_ty) = types
      .iter()
      .find_map(|t| if let IdlType::Sequence(_) = t { Some(*t) } else { None })
    {
      let obj = cx.as_object(v).unwrap();
      let iter_sym = cx
        .well_known_symbol(WellKnownSymbol::Iterator)
        .map_err(WebIdlError::js)?;
      if let Some(method) = cx
        .get_method(obj, PropertyKey::Symbol(iter_sym))
        .map_err(WebIdlError::js)?
      {
        let value = convert_js_to_idl_with_hints(cx, seq_ty, v, Some(IteratorHint { method }), None)?;
        return Ok(IdlValue::Union(UnionValue {
          selected_type: seq_ty.clone(),
          value: Box::new(value),
        }));
      }
    }

    // ---- FrozenArray<T> ----
    if let Some(fa_ty) = types
      .iter()
      .find_map(|t| if let IdlType::FrozenArray(_) = t { Some(*t) } else { None })
    {
      let obj = cx.as_object(v).unwrap();
      let iter_sym = cx
        .well_known_symbol(WellKnownSymbol::Iterator)
        .map_err(WebIdlError::js)?;
      if let Some(method) = cx
        .get_method(obj, PropertyKey::Symbol(iter_sym))
        .map_err(WebIdlError::js)?
      {
        let value = convert_js_to_idl_with_hints(cx, fa_ty, v, Some(IteratorHint { method }), None)?;
        return Ok(IdlValue::Union(UnionValue {
          selected_type: fa_ty.clone(),
          value: Box::new(value),
        }));
      }
    }
  }

  // ---- string fallback ----
  if let Some(string_ty) = types.iter().find_map(|t| if t.is_string_type() { Some(*t) } else { None }) {
    let value = convert_js_to_idl(cx, string_ty, v)?;
    return Ok(IdlValue::Union(UnionValue {
      selected_type: string_ty.clone(),
      value: Box::new(value),
    }));
  }

  Err(type_error(cx, "union: could not select a member type"))
}
