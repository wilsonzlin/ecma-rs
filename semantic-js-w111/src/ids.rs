//! Numeric ID newtypes that must serialize as bare integers for tooling compatibility.

macro_rules! id_type {
  ($name:ident) => {
    #[repr(transparent)]
    #[derive(Copy, Clone, Eq, PartialEq, Hash, Debug)]
    #[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
    #[cfg_attr(feature = "serde", serde(transparent))]
    pub struct $name(u32);

    impl $name {
      pub const fn as_u32(self) -> u32 {
        self.0
      }
    }

    impl From<u32> for $name {
      fn from(value: u32) -> Self {
        Self(value)
      }
    }

    impl From<$name> for u32 {
      fn from(value: $name) -> Self {
        value.0
      }
    }
  };
}

id_type!(ScopeId);
id_type!(SymbolId);
id_type!(NameId);

#[cfg(all(test, feature = "serde"))]
mod tests {
  use super::*;
  use serde_json::json;

  #[test]
  fn symbol_id_serializes_as_integer() {
    let id = SymbolId::from(42u32);

    let serialized = serde_json::to_string(&id).expect("serialize SymbolId");
    assert_eq!(serialized, "42");

    let roundtrip: SymbolId = serde_json::from_str(&serialized).expect("deserialize SymbolId");
    assert_eq!(roundtrip, id);

    let some_value = serde_json::to_value(Some(id)).expect("serialize Option<SymbolId>");
    assert_eq!(some_value, json!(42));
    let option_roundtrip: Option<SymbolId> = serde_json::from_value(some_value).unwrap();
    assert_eq!(option_roundtrip, Some(id));

    let none_value = serde_json::to_value(Option::<SymbolId>::None).expect("serialize None");
    assert!(none_value.is_null());
  }

  #[test]
  fn symbol_id_msgpack_roundtrip_is_integer() {
    let id = SymbolId::from(7u32);

    let bytes = rmp_serde::to_vec(&id).expect("serialize SymbolId to msgpack");

    // Decode as plain u32 to prove the encoded shape is a bare integer.
    let decoded_raw: u32 = rmp_serde::from_slice(&bytes).expect("decode SymbolId as u32");
    assert_eq!(decoded_raw, id.as_u32());

    let roundtrip: SymbolId = rmp_serde::from_slice(&bytes).expect("roundtrip SymbolId");
    assert_eq!(roundtrip, id);

    let some_bytes = rmp_serde::to_vec(&Some(id)).expect("serialize Option<SymbolId>");
    let decoded_some: Option<u32> =
      rmp_serde::from_slice(&some_bytes).expect("decode Option<SymbolId> as Option<u32>");
    assert_eq!(decoded_some, Some(id.as_u32()));
  }
}
