mod toy;

use toy::{ToyObjectKind, ToyRuntime, ToyValue};
use webidl::{
  dictionary_to_js, DomString, FrozenArray, IdlRecord, PropertyKey, ToJsPropertyKey, ToJsValue,
  WebIdlError, WebIdlLimits,
};

#[test]
fn domstring_roundtrip_code_units_preserved_including_lone_surrogates() {
  let mut rt = ToyRuntime::default();
  let limits = WebIdlLimits::default();

  let s = DomString::from_code_units(vec![0x0061, 0xD800, 0x0062, 0xDC00]);
  let v = s.to_js(&mut rt, &limits).unwrap();

  match v {
    ToyValue::String(h) => {
      assert_eq!(rt.string_code_units(h), &[0x0061, 0xD800, 0x0062, 0xDC00]);
    }
    other => panic!("expected string, got {other:?}"),
  }
}

#[test]
fn sequence_converts_to_array_with_numeric_keys_and_values() {
  let mut rt = ToyRuntime::default();
  let limits = WebIdlLimits::default();

  let seq = vec![true, false, true];
  let v = seq.to_js(&mut rt, &limits).unwrap();

  let obj = match v {
    ToyValue::Object(o) => o,
    other => panic!("expected object, got {other:?}"),
  };

  let data = rt.object(obj);
  assert_eq!(data.kind, ToyObjectKind::Array { len: 3 });

  let keys = data
    .props
    .iter()
    .map(|(k, _)| match k {
      PropertyKey::String(s) => String::from_utf16(rt.string_code_units(*s)).unwrap(),
      PropertyKey::Symbol(_) => "<symbol>".to_string(),
    })
    .collect::<Vec<_>>();

  assert_eq!(keys, vec!["0", "1", "2"]);

  let values = data.props.iter().map(|(_k, v)| *v).collect::<Vec<_>>();
  assert_eq!(
    values,
    vec![
      ToyValue::Bool(true),
      ToyValue::Bool(false),
      ToyValue::Bool(true)
    ]
  );
}

#[test]
fn record_converts_to_object_with_own_enumerable_properties() {
  let mut rt = ToyRuntime::default();
  let limits = WebIdlLimits::default();

  let record = IdlRecord(vec![
    (DomString::from_str("a"), 1u32),
    (DomString::from_str("b"), 2u32),
  ]);

  let v = record.to_js(&mut rt, &limits).unwrap();
  let obj = match v {
    ToyValue::Object(o) => o,
    other => panic!("expected object, got {other:?}"),
  };

  let data = rt.object(obj);
  assert_eq!(data.kind, ToyObjectKind::Ordinary);

  let keys = data
    .props
    .iter()
    .map(|(k, _)| match k {
      PropertyKey::String(s) => String::from_utf16(rt.string_code_units(*s)).unwrap(),
      PropertyKey::Symbol(_) => "<symbol>".to_string(),
    })
    .collect::<Vec<_>>();
  assert_eq!(keys, vec!["a", "b"]);

  let values = data.props.iter().map(|(_k, v)| *v).collect::<Vec<_>>();
  assert_eq!(values, vec![ToyValue::Number(1.0), ToyValue::Number(2.0)]);
}

#[test]
fn dictionary_serialization_is_in_lexicographic_member_order() {
  #[derive(Default)]
  struct ExampleDict {
    pub b: Option<u32>,
    pub a: Option<u32>,
    pub c: Option<u32>,
  }

  impl<R: webidl::JsRuntime> ToJsValue<R> for ExampleDict {
    fn to_js(&self, rt: &mut R, limits: &WebIdlLimits) -> Result<R::Value, WebIdlError> {
      dictionary_to_js(rt, limits, |rt, limits, obj| {
        if let Some(v) = &self.a {
          let key = "a".to_property_key(rt, limits)?;
          let value = v.to_js(rt, limits)?;
          rt.create_data_property_or_throw(obj, key, value)
            .map_err(WebIdlError::js)?;
        }
        if let Some(v) = &self.b {
          let key = "b".to_property_key(rt, limits)?;
          let value = v.to_js(rt, limits)?;
          rt.create_data_property_or_throw(obj, key, value)
            .map_err(WebIdlError::js)?;
        }
        if let Some(v) = &self.c {
          let key = "c".to_property_key(rt, limits)?;
          let value = v.to_js(rt, limits)?;
          rt.create_data_property_or_throw(obj, key, value)
            .map_err(WebIdlError::js)?;
        }
        Ok(())
      })
    }
  }

  let mut rt = ToyRuntime::default();
  let limits = WebIdlLimits::default();

  let dict = ExampleDict {
    b: Some(2),
    a: Some(1),
    c: Some(3),
  };

  let v = dict.to_js(&mut rt, &limits).unwrap();
  let obj = match v {
    ToyValue::Object(o) => o,
    other => panic!("expected object, got {other:?}"),
  };

  let data = rt.object(obj);
  let keys = data
    .props
    .iter()
    .map(|(k, _)| match k {
      PropertyKey::String(s) => String::from_utf16(rt.string_code_units(*s)).unwrap(),
      PropertyKey::Symbol(_) => "<symbol>".to_string(),
    })
    .collect::<Vec<_>>();

  assert_eq!(keys, vec!["a", "b", "c"]);
}

#[test]
fn option_none_converts_to_null() {
  let mut rt = ToyRuntime::default();
  let limits = WebIdlLimits::default();

  let v: Option<u32> = None;
  assert_eq!(v.to_js(&mut rt, &limits).unwrap(), ToyValue::Null);
}

#[test]
fn frozen_array_sets_integrity_level_frozen() {
  let mut rt = ToyRuntime::default();
  let limits = WebIdlLimits::default();

  let v = FrozenArray(vec![1u32, 2u32])
    .to_js(&mut rt, &limits)
    .unwrap();
  let obj = match v {
    ToyValue::Object(o) => o,
    other => panic!("expected object, got {other:?}"),
  };

  let data = rt.object(obj);
  assert!(data.frozen);
}
