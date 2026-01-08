use crate::{convert, convert_js_to_idl, IdlType, IdlValue, JsRuntime, PropertyKey, WebIdlError, WellKnownSymbol};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Optionality {
  Required,
  Optional,
}

#[derive(Debug, Clone)]
pub struct Overload {
  pub id: &'static str,
  pub types: Vec<IdlType>,
  pub optionality: Vec<Optionality>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum OverloadArg<V, S> {
  Missing,
  Value(IdlValue<V, S>),
}

#[derive(Debug, Clone, PartialEq)]
pub struct OverloadResult<V, S> {
  pub overload_id: &'static str,
  pub values: Vec<OverloadArg<V, S>>,
}

#[inline]
fn type_error<R: JsRuntime>(rt: &mut R, message: &'static str) -> WebIdlError {
  WebIdlError::js(rt.type_error(message))
}

pub fn resolve_overload<R: JsRuntime>(
  cx: &mut R,
  overloads: &[Overload],
  args: &[R::Value],
) -> Result<OverloadResult<R::Value, R::String>, WebIdlError> {
  let maxarg = overloads.iter().map(|o| o.types.len()).max().unwrap_or(0);
  let argcount = std::cmp::min(maxarg, args.len());

  let mut s: Vec<&Overload> = overloads.iter().filter(|o| o.types.len() == argcount).collect();
  if s.is_empty() {
    return Err(type_error(cx, "no matching overload"));
  }

  let d = if s.len() > 1 {
    Some(
      distinguishing_argument_index(&s).map_err(|_| type_error(cx, "invalid overload set"))?,
    )
  } else {
    None
  };

  let mut values: Vec<OverloadArg<R::Value, R::String>> = Vec::new();
  let mut i: usize = 0;

  // Convert arguments before the distinguishing argument index.
  if let Some(d) = d {
    while i < d {
      let v = args[i];
      let ty = &s[0].types[i];
      let opt = s[0].optionality.get(i).copied().unwrap_or(Optionality::Required);
      if opt == Optionality::Optional && cx.is_undefined(v) {
        values.push(OverloadArg::Missing);
      } else {
        values.push(OverloadArg::Value(convert_js_to_idl(cx, ty, v)?));
      }
      i += 1;
    }
  }

  // Resolve overload at distinguishing argument index.
  if let Some(d) = d {
    debug_assert_eq!(i, d);
    let v = args[i];

    // Async sequence special-case (d): if V is a string object and the overload set includes a
    // string type at position i, do not attempt iterator-based async sequence matching.
    if cx.is_object(v)
      && s.iter().any(|o| o.types[i].contains_async_sequence_type())
      && !(s.iter().any(|o| o.types[i].contains_string_type()) && cx.is_string_object(v))
    {
      let obj = cx.as_object(v).unwrap();

      let async_iter_sym = cx
        .well_known_symbol(WellKnownSymbol::AsyncIterator)
        .map_err(WebIdlError::js)?;
      let mut hint = cx
        .get_method(obj, PropertyKey::Symbol(async_iter_sym))
        .map_err(WebIdlError::js)?
        .map(|method| convert::AsyncIteratorHint::Async { method });

      if hint.is_none() {
        let iter_sym = cx
          .well_known_symbol(WellKnownSymbol::Iterator)
          .map_err(WebIdlError::js)?;
        hint = cx
          .get_method(obj, PropertyKey::Symbol(iter_sym))
          .map_err(WebIdlError::js)?
          .map(|method| convert::AsyncIteratorHint::Sync { method });
      }

      if let Some(hint) = hint {
        s.retain(|o| o.types[i].contains_async_sequence_type());
        if s.len() != 1 {
          return Err(type_error(cx, "ambiguous overload after async sequence selection"));
        }

        let ty = &s[0].types[i];
        values.push(OverloadArg::Value(convert::convert_js_to_idl_with_hints(
          cx,
          ty,
          v,
          None,
          Some(hint),
        )?));
        i += 1;
      }
    }

    if i == d && cx.is_object(v) {
      let any_sequence = s.iter().any(|o| o.types[i].contains_sequence_type());
      let any_frozen_array = s.iter().any(|o| o.types[i].contains_frozen_array_type());

      if any_sequence || any_frozen_array {
        let obj = cx.as_object(v).unwrap();
        let iter_sym = cx
          .well_known_symbol(WellKnownSymbol::Iterator)
          .map_err(WebIdlError::js)?;
        let method = cx
          .get_method(obj, PropertyKey::Symbol(iter_sym))
          .map_err(WebIdlError::js)?;
        if let Some(method) = method {
          if any_sequence {
            s.retain(|o| o.types[i].contains_sequence_type());
          } else {
            s.retain(|o| o.types[i].contains_frozen_array_type());
          }
          if s.len() != 1 {
            return Err(type_error(cx, "ambiguous overload after iterator-based selection"));
          }

          let ty = &s[0].types[i];
          values.push(OverloadArg::Value(convert::convert_js_to_idl_with_hints(
            cx,
            ty,
            v,
            Some(convert::IteratorHint { method }),
            None,
          )?));
          i += 1;
        }
      }
    }

    // String selection (matches the end of the spec's distinguishing argument checks).
    if i == d && s.len() > 1 && s.iter().any(|o| o.types[i].contains_string_type()) {
      s.retain(|o| o.types[i].contains_string_type());
    }

    if i == d && s.len() != 1 {
      return Err(type_error(
        cx,
        "overload resolution not implemented for these types",
      ));
    }
  }

  let selected = s[0];

  // Convert remaining arguments.
  while i < argcount {
    let v = args[i];
    let ty = &selected.types[i];
    let opt = selected.optionality.get(i).copied().unwrap_or(Optionality::Required);
    if opt == Optionality::Optional && cx.is_undefined(v) {
      values.push(OverloadArg::Missing);
    } else {
      values.push(OverloadArg::Value(convert_js_to_idl(cx, ty, v)?));
    }
    i += 1;
  }

  Ok(OverloadResult {
    overload_id: selected.id,
    values,
  })
}

fn distinguishing_argument_index(overloads: &[&Overload]) -> Result<usize, ()> {
  let argcount = overloads[0].types.len();
  for i in 0..argcount {
    let mut all_distinguishable = true;
    for a in 0..overloads.len() {
      for b in (a + 1)..overloads.len() {
        if !are_distinguishable(&overloads[a].types[i], &overloads[b].types[i]) {
          all_distinguishable = false;
          break;
        }
      }
      if !all_distinguishable {
        break;
      }
    }
    if all_distinguishable {
      return Ok(i);
    }
  }
  Err(())
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TypeCategory {
  Undefined,
  Boolean,
  Numeric,
  String,
  Object,
  AsyncSequence,
  SequenceLike,
  Other,
}

fn category(ty: &IdlType) -> TypeCategory {
  match ty {
    IdlType::Union(_) => TypeCategory::Other,
    IdlType::Nullable(inner) => category(inner),
    IdlType::Undefined => TypeCategory::Undefined,
    IdlType::Boolean => TypeCategory::Boolean,
    IdlType::Double => TypeCategory::Numeric,
    IdlType::DomString => TypeCategory::String,
    IdlType::Object => TypeCategory::Object,
    IdlType::AsyncSequence(_) => TypeCategory::AsyncSequence,
    IdlType::Sequence(_) | IdlType::FrozenArray(_) => TypeCategory::SequenceLike,
  }
}

fn are_distinguishable(a: &IdlType, b: &IdlType) -> bool {
  // Partial implementation of WebIDL distinguishability sufficient for the crate's tests.

  match (a, b) {
    (IdlType::Union(am), _) => am.iter().all(|m| are_distinguishable(m, b)),
    (_, IdlType::Union(bm)) => bm.iter().all(|m| are_distinguishable(a, m)),
    _ => {
      let ca = category(a);
      let cb = category(b);
      ca != cb
    }
  }
}
