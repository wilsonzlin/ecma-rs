//! WebIDL conversions and overload resolution scaffolding.
//!
//! This crate intentionally keeps the "JS engine" surface abstract via [`JsRuntime`], so it can be
//! embedded on top of different runtimes (e.g. `vm-js`).

mod error;
mod idl;
mod to_js;

pub use error::{WebIdlError, WebIdlLimit};
pub use idl::{ByteString, DomString, FrozenArray, IdlRecord, IdlString, IdlUndefined, UsvString};
pub use to_js::{
  dictionary_to_js, index_to_property_key, record_to_js_object, sequence_to_js_array, union_to_js,
  ToJsPropertyKey, ToJsValue,
};

/// A stable identifier for a WebIDL interface.
///
/// Bindings generators can assign unique IDs per interface and then use those IDs for fast runtime
/// checks (e.g. `instanceof`-like checks for platform objects).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct InterfaceId(pub u32);

/// Runtime/embedding-provided hooks needed for WebIDL conversions.
///
/// In particular, WebIDL interface conversions need to detect "platform objects" (objects owned by
/// the embedding, not the JS engine) and test whether they implement a given interface.
///
/// This is defined in the `webidl` crate so embedders (e.g. FastRender) can implement it without
/// depending on a specific JS runtime.
pub trait WebIdlHooks<V> {
  /// Returns whether `value` is an embedding-defined platform object.
  fn is_platform_object(&self, value: V) -> bool;

  /// Returns whether `value` implements the WebIDL interface `interface`.
  fn implements_interface(&self, value: V, interface: InterfaceId) -> bool;

  /// Optional: returns whether `value` is a typed array object.
  ///
  /// Default implementation returns `false` (typed arrays not supported).
  fn is_typed_array(&self, _value: V) -> bool {
    false
  }

  /// Optional: returns whether `value` is an ArrayBuffer object.
  ///
  /// Default implementation returns `false` (ArrayBuffer not supported).
  fn is_array_buffer(&self, _value: V) -> bool {
    false
  }
}

/// Resource limits for WebIDL conversions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WebIdlLimits {
  /// Maximum length (in UTF-16 code units) allowed for string conversions that allocate.
  pub max_string_code_units: usize,
  /// Maximum length allowed for list/sequence conversions that allocate.
  pub max_sequence_length: usize,
  /// Maximum number of entries allowed when converting WebIDL records to objects.
  pub max_record_entries: usize,
}

impl Default for WebIdlLimits {
  fn default() -> Self {
    Self {
      // Arbitrary but sane defaults for early scaffolding; embedders should set these explicitly.
      max_string_code_units: 1 << 20,
      max_sequence_length: 1 << 20,
      max_record_entries: 1 << 20,
    }
  }
}

/// A JS property key (`PropertyKey` in ECMAScript), re-exposed for WebIDL operations.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PropertyKey<S, Sym> {
  String(S),
  Symbol(Sym),
}

/// The result of an iterator `next()` step.
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct IteratorResult<V> {
  pub value: V,
  pub done: bool,
}

/// Well-known symbols needed by WebIDL conversions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum WellKnownSymbol {
  Iterator,
  AsyncIterator,
}

/// A concrete own-property descriptor returned by [`WebIdlJsRuntime::get_own_property`].
///
/// Web IDL currently only requires the `[[Enumerable]]` flag, but we expose the "shape" of a
/// descriptor so future binding code can reuse it without expanding the runtime surface again.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct JsOwnPropertyDescriptor<V> {
  pub enumerable: bool,
  pub kind: JsPropertyKind<V>,
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum JsPropertyKind<V> {
  Data { value: V },
  Accessor { get: V, set: V },
}

/// Abstraction over a JS runtime sufficient for WebIDL conversions.
///
/// This is intentionally a narrow interface: it models only the operations used by WebIDL
/// conversions and overload resolution (e.g. `ToBoolean`, `ToString`, property access, iterator
/// protocol).
pub trait JsRuntime {
  type Value: Copy;
  type String: Copy;
  type Object: Copy;
  type Symbol: Copy;
  type Error: std::error::Error + Send + Sync + 'static;

  /// Conversion limits configured by the embedding.
  fn limits(&self) -> WebIdlLimits;

  /// Embedding-provided hooks for platform objects.
  fn hooks(&self) -> &dyn WebIdlHooks<Self::Value>;

  // ---- JS value construction (IDL → JS) ----
  fn value_undefined(&self) -> Self::Value;
  fn value_null(&self) -> Self::Value;
  fn value_bool(&self, value: bool) -> Self::Value;
  fn value_number(&self, value: f64) -> Self::Value;
  fn value_string(&self, value: Self::String) -> Self::Value;
  fn value_object(&self, value: Self::Object) -> Self::Value;

  // ---- Type checks ----
  fn is_undefined(&self, value: Self::Value) -> bool;
  fn is_null(&self, value: Self::Value) -> bool;
  fn is_boolean(&self, value: Self::Value) -> bool;
  fn is_number(&self, value: Self::Value) -> bool;
  fn is_string(&self, value: Self::Value) -> bool;
  fn is_symbol(&self, value: Self::Value) -> bool;
  fn is_object(&self, value: Self::Value) -> bool;

  /// Returns whether `value` is a string object (i.e. has `[[StringData]]`).
  ///
  /// This is needed for the async-sequence vs string special-case in union conversion and overload
  /// resolution (distinguishability requirement "(d)" in the spec).
  fn is_string_object(&self, value: Self::Value) -> bool;

  /// Returns the underlying JS string handle if `value` is a string.
  fn as_string(&self, value: Self::Value) -> Option<Self::String>;
  /// Returns the underlying JS object handle if `value` is an object.
  fn as_object(&self, value: Self::Value) -> Option<Self::Object>;
  /// Returns the underlying JS symbol handle if `value` is a symbol.
  fn as_symbol(&self, value: Self::Value) -> Option<Self::Symbol>;

  // ---- ECMAScript conversions ----
  fn to_boolean(&mut self, value: Self::Value) -> Result<bool, Self::Error>;
  fn to_string(&mut self, value: Self::Value) -> Result<Self::String, Self::Error>;
  fn to_number(&mut self, value: Self::Value) -> Result<f64, Self::Error>;

  // ---- Errors ----
  fn type_error(&mut self, message: &'static str) -> Self::Error;

  // ---- Object operations ----
  fn get(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Self::Value, Self::Error>;

  fn get_method(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<Self::Value>, Self::Error>;

  fn own_property_keys(
    &mut self,
    object: Self::Object,
  ) -> Result<Vec<PropertyKey<Self::String, Self::Symbol>>, Self::Error>;

  // ---- Object creation (IDL → JS) ----
  fn alloc_string_from_code_units(&mut self, units: &[u16]) -> Result<Self::String, Self::Error>;
  fn alloc_object(&mut self) -> Result<Self::Object, Self::Error>;
  fn alloc_array(&mut self, len: usize) -> Result<Self::Object, Self::Error>;

  fn create_data_property_or_throw(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
    value: Self::Value,
  ) -> Result<(), Self::Error>;

  fn to_property_key_from_string(
    &self,
    s: Self::String,
  ) -> PropertyKey<Self::String, Self::Symbol> {
    PropertyKey::String(s)
  }

  fn set_integrity_level_frozen(&mut self, _object: Self::Object) -> Result<(), Self::Error> {
    Ok(())
  }

  // ---- Well-known symbols ----
  fn well_known_symbol(&mut self, sym: WellKnownSymbol) -> Result<Self::Symbol, Self::Error>;

  // ---- Iterator protocol ----
  fn get_iterator(&mut self, value: Self::Value) -> Result<Self::Object, Self::Error>;
  fn get_iterator_from_method(
    &mut self,
    object: Self::Object,
    method: Self::Value,
  ) -> Result<Self::Object, Self::Error>;
  fn iterator_next(
    &mut self,
    iterator: Self::Object,
  ) -> Result<IteratorResult<Self::Value>, Self::Error>;

  #[inline]
  fn iterator_step_value(
    &mut self,
    iterator: Self::Object,
  ) -> Result<Option<Self::Value>, Self::Error> {
    let step = self.iterator_next(iterator)?;
    Ok(if step.done { None } else { Some(step.value) })
  }
}

/// Additional JS runtime operations used by WebIDL JS→IDL conversions and overload resolution.
///
/// This extends the base [`JsRuntime`] used by IDL→JS helpers with operations needed to implement
/// WebIDL algorithms like `ToNumeric`, `ToBigInt`, own property descriptor checks, and BufferSource
/// internal-slot predicates.
pub trait WebIdlJsRuntime: JsRuntime {
  fn is_callable(&self, value: Self::Value) -> bool;
  fn is_bigint(&self, value: Self::Value) -> bool;

  fn to_bigint(&mut self, value: Self::Value) -> Result<Self::Value, Self::Error>;
  fn to_numeric(&mut self, value: Self::Value) -> Result<Self::Value, Self::Error>;

  fn get_own_property(
    &mut self,
    object: Self::Object,
    key: PropertyKey<Self::String, Self::Symbol>,
  ) -> Result<Option<JsOwnPropertyDescriptor<Self::Value>>, Self::Error>;

  fn throw_type_error(&mut self, message: &str) -> Self::Error;
  fn throw_range_error(&mut self, message: &str) -> Self::Error;

  // ---- internal slot checks (overload resolution prerequisites) ----
  fn is_array_buffer(&self, value: Self::Value) -> bool;
  fn is_shared_array_buffer(&self, value: Self::Value) -> bool;
  fn is_data_view(&self, value: Self::Value) -> bool;
  fn typed_array_name(&self, value: Self::Value) -> Option<&'static str>;
}

pub mod conversions {
  //! WebIDL conversion functions.
  //!
  //! Only a tiny subset is implemented today; the rest will be added as bindings are generated.

  use super::JsRuntime;

  /// Convert ECMAScript `value` to a WebIDL `DOMString`.
  ///
  /// Spec: https://webidl.spec.whatwg.org/#es-DOMString
  #[inline]
  pub fn dom_string<R: JsRuntime>(cx: &mut R, value: R::Value) -> Result<R::String, R::Error> {
    cx.to_string(value)
  }
}

mod types;
pub use types::{AsyncSequence, AsyncSequenceKind, IdlType, IdlValue, UnionValue};

mod convert;
pub use convert::{convert_idl_to_js, convert_js_to_idl};

mod overload;
pub use overload::{resolve_overload, Optionality, Overload, OverloadArg, OverloadResult};
