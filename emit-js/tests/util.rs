use serde_json::Value;

pub fn strip_locs(value: &mut Value) {
  match value {
    Value::Object(map) => {
      map.remove("loc");
      for v in map.values_mut() {
        strip_locs(v);
      }
    }
    Value::Array(items) => {
      for item in items {
        strip_locs(item);
      }
    }
    _ => {}
  }
}

pub fn serialize_without_locs<T: serde::Serialize>(value: &T) -> Value {
  let mut serialized = serde_json::to_value(value).expect("serialize value");
  strip_locs(&mut serialized);
  serialized
}
