//! WebIDL conversions and overload resolution scaffolding.
//!
//! This crate intentionally keeps the "JS engine" surface abstract via [`JsRuntime`], so it can be
//! embedded on top of different runtimes (e.g. `vm-js`).

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
}

impl Default for WebIdlLimits {
  fn default() -> Self {
    Self {
      // Arbitrary but sane defaults for early scaffolding; embedders should set these explicitly.
      max_string_code_units: 1 << 20,
      max_sequence_length: 1 << 20,
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
  type Error;

  /// Conversion limits configured by the embedding.
  fn limits(&self) -> WebIdlLimits;

  /// Embedding-provided hooks for platform objects.
  fn hooks(&self) -> &dyn WebIdlHooks<Self::Value>;

  // ---- Type checks ----
  fn is_undefined(&self, value: Self::Value) -> bool;
  fn is_null(&self, value: Self::Value) -> bool;
  fn is_boolean(&self, value: Self::Value) -> bool;
  fn is_number(&self, value: Self::Value) -> bool;
  fn is_string(&self, value: Self::Value) -> bool;
  fn is_symbol(&self, value: Self::Value) -> bool;
  fn is_object(&self, value: Self::Value) -> bool;

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

  // ---- Iterator protocol ----
  fn get_iterator(&mut self, value: Self::Value) -> Result<Self::Object, Self::Error>;
  fn iterator_next(&mut self, iterator: Self::Object) -> Result<IteratorResult<Self::Value>, Self::Error>;
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

