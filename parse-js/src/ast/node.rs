use crate::error::SyntaxError;
use crate::error::SyntaxErrorType;
use crate::loc::Loc;
use derive_visitor::Drive;
use derive_visitor::DriveMut;
#[cfg(feature = "serde")]
use serde::ser::SerializeStruct;
#[cfg(feature = "serde")]
use serde::{Serialize, Serializer};
use smallvec::SmallVec;
use std::any::Any;
use std::any::TypeId;
use std::fmt::{self, Debug, Display, Formatter};

#[derive(Default, Drive, DriveMut)]
pub struct NodeAssocData {
  // Make Node movable across threads (e.g. rayon) by bounding value to Send + Sync too.
  #[drive(skip)]
  items: SmallVec<[(TypeId, Box<dyn Any + Send + Sync>); 1]>,
}

/// Marker attached to an expression node that was parsed from a parenthesized
/// expression (e.g. `(x)`).
///
/// `parse-js` intentionally does not keep parentheses as distinct AST nodes;
/// they are only preserved via this marker so downstream crates can still
/// implement syntax-sensitive behaviors (e.g. exponentiation operand rules or
/// directive prologue parsing).
#[derive(Clone, Copy, Debug)]
pub struct ParenthesizedExpr;

/// Marker attached to a numeric literal node that originated from a legacy octal
/// integer literal (e.g. `010`).
///
/// Strict mode code may not include these literals; downstream semantic passes
/// use this marker to report the early error without needing access to the raw
/// source text.
#[derive(Clone, Copy, Debug)]
pub struct LegacyOctalNumberLiteral;

/// Marker attached to a numeric literal node that originated from a decimal
/// integer literal with a leading zero (e.g. `08`).
///
/// Strict mode code may not include these literals; downstream semantic passes
/// use this marker to report the early error without needing access to the raw
/// source text.
#[derive(Clone, Copy, Debug)]
pub struct LeadingZeroDecimalLiteral;

/// Marker attached to a string literal token (or a node derived from one) when
/// its raw source contained a legacy escape sequence that is forbidden in strict
/// mode (e.g. `"\1"`, `"\08"`, or `"\8"`).
///
/// Stores the span of the first offending escape sequence so downstream passes
/// can report a precise diagnostic without needing access to the raw source
/// text.
#[derive(Clone, Copy, Debug)]
pub struct LegacyOctalEscapeSequence(pub Loc);

/// Marker attached to a string literal expression node recording the exact UTF-16
/// code units produced by escape decoding.
///
/// ECMAScript strings are sequences of UTF-16 code units and may contain unpaired
/// surrogates, which cannot be represented in Rust's `String`. `parse-js` keeps
/// the existing `String`-typed AST field for compatibility (derived via
/// `String::from_utf16_lossy`), while exposing the spec-correct code units via
/// this association marker for downstream consumers (e.g. the VM).
#[derive(Clone, Debug)]
pub struct LiteralStringCodeUnits(pub Box<[u16]>);

/// Returns the UTF-16 code units for a string literal expression, if present.
pub fn literal_string_code_units(assoc: &NodeAssocData) -> Option<&[u16]> {
  assoc
    .get::<LiteralStringCodeUnits>()
    .map(|data| data.0.as_ref())
}

/// Marker attached to template literal expression nodes recording the raw and
/// cooked UTF-16 code units for each template string segment.
///
/// The slices are aligned with the template's *string segments* (i.e. the
/// `TemplateHead`/`TemplateMiddle`/`TemplateTail` parts), and do **not** include
/// substitution expressions.
///
/// For tagged templates, a segment's cooked value can be `None`, indicating
/// `undefined` per ECMAScript's `GetTemplateObject` semantics when the segment
/// contains an invalid escape sequence.
#[derive(Clone, Debug)]
pub struct TemplateStringParts {
  pub raw: Box<[Box<[u16]>]>,
  pub cooked: Box<[Option<Box<[u16]>>]>,
}

/// Returns the template literal raw/cooked strings for a template expression, if
/// present.
pub fn template_string_parts(assoc: &NodeAssocData) -> Option<&TemplateStringParts> {
  assoc.get::<TemplateStringParts>()
}

/// Marker attached to an untagged template literal node when its raw source
/// contains an escape sequence that is invalid in template strings (e.g.
/// `` `\1` `` or `` `\8` ``).
///
/// Tagged templates allow these escapes (the cooked value becomes undefined),
/// so this marker is only recorded for untagged template literals.
#[derive(Clone, Copy, Debug)]
pub struct InvalidTemplateEscapeSequence(pub Loc);

impl NodeAssocData {
  pub fn is_empty(&self) -> bool {
    self.items.is_empty()
  }

  pub fn get<T: Any>(&self) -> Option<&T> {
    let t = TypeId::of::<T>();
    self
      .items
      .iter()
      .find(|(id, _)| *id == t)
      .map(|(_, v)| v.downcast_ref().unwrap())
  }

  pub fn get_mut<T: Any>(&mut self) -> Option<&mut T> {
    let t = TypeId::of::<T>();
    self
      .items
      .iter_mut()
      .find(|(id, _)| *id == t)
      .map(|(_, v)| v.downcast_mut().unwrap())
  }

  pub fn set<T: Any + Send + Sync>(&mut self, v: T) {
    let t = TypeId::of::<T>();
    if let Some((_, existing)) = self.items.iter_mut().find(|(id, _)| *id == t) {
      *existing = Box::new(v);
    } else {
      self.items.push((t, Box::new(v)));
    }
  }

  pub fn remove<T: Any>(&mut self) -> Option<T> {
    let t = TypeId::of::<T>();
    self.items.iter().position(|(id, _)| *id == t).map(|idx| {
      let (_, v) = self.items.remove(idx);
      *v.downcast::<T>().unwrap()
    })
  }
}

#[derive(Drive, DriveMut)]
pub struct Node<S: Drive + DriveMut> {
  // A location is not a SourceRange; consider that after some transformations, it's possible to create entirely new nodes that don't exist at all in the source code. Also, sometimes we cannot be bothered to set a location, or can only provide an approximate/best-effort location.
  #[drive(skip)]
  pub loc: Loc,
  pub stx: Box<S>,
  pub assoc: NodeAssocData,
}

impl<S: Drive + DriveMut> Node<S> {
  pub fn new(loc: Loc, stx: S) -> Node<S> {
    Node {
      loc,
      stx: Box::new(stx),
      assoc: NodeAssocData::default(),
    }
  }

  /// Converts this Node's stx into a different type, keeping the same location and associated data.
  /// The current type must be convertable into the resulting type (i.e. `Into<T>`/`From<S>`).
  /// This is useful for converting S into a variant E::S(S) on an enum (e.g. `CallExpr => Expr::Call(CallExpr)`) where an E is wanted.
  pub fn into_stx<T: From<S> + Drive + DriveMut>(self) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(T::from(*self.stx)),
      assoc: self.assoc,
    }
  }

  /// Same as `into_stx` except for `TryInto<T>`/`TryFrom<S>`.
  pub fn try_into_stx<T: TryFrom<S> + Drive + DriveMut>(self) -> Result<Node<T>, T::Error> {
    Ok(Node {
      loc: self.loc,
      stx: Box::new(T::try_from(*self.stx)?),
      assoc: self.assoc,
    })
  }

  /// Moves Node<S> into Node<T { Node<S> }>. The wrapper will have the same location but no associated data.
  /// This is useful for converting Node<S> into a variant E::S(Node<S>) on an enum (e.g. `CallExpr => Expr::Call(Node<CallExpr>)`) where an E is wanted.
  pub fn into_wrapped<T: From<Node<S>> + Drive + DriveMut>(self) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(T::from(self)),
      assoc: NodeAssocData::default(),
    }
  }

  /// Maps the syntax, keeping the location and associated data.
  pub fn map_stx<T: Drive + DriveMut, F: FnOnce(S) -> T>(self, f: F) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(f(*self.stx)),
      assoc: self.assoc,
    }
  }

  /// Maps the syntax, copying the location but not the associated data.
  pub fn derive_stx<T: Drive + DriveMut, F: FnOnce(&S) -> T>(&self, f: F) -> Node<T> {
    Node {
      loc: self.loc,
      stx: Box::new(f(&self.stx)),
      assoc: NodeAssocData::default(),
    }
  }

  /// Wraps the node inside another node with the same loc, with syntax derived from the provided callback.
  pub fn wrap<T: Drive + DriveMut, F: FnOnce(Node<S>) -> T>(self, f: F) -> Node<T> {
    let loc = self.loc;
    let stx = f(self);
    Node::new(loc, stx)
  }

  pub fn located(&self) -> LocatedNode<'_, S> {
    LocatedNode(self)
  }

  /// Create an error at this node's location.
  pub fn error(&self, typ: SyntaxErrorType) -> SyntaxError {
    self.loc.error(typ, None)
  }
}

#[derive(Clone, Copy)]
pub struct LocatedNode<'a, S: Drive + DriveMut>(pub &'a Node<S>);

#[derive(Clone, Copy)]
struct LocSpan(Loc);

impl Display for LocSpan {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    let Loc(start, end) = self.0;
    write!(f, "{}..{}", start, end)
  }
}

impl Debug for LocSpan {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    Display::fmt(self, f)
  }
}

#[cfg(feature = "serde")]
impl Serialize for LocSpan {
  fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
    let Loc(start, end) = self.0;
    let mut state = serializer.serialize_struct("Loc", 2)?;
    state.serialize_field("start", &start)?;
    state.serialize_field("end", &end)?;
    state.end()
  }
}

#[cfg(feature = "serde")]
fn serialize_located_node<S: Serialize + Drive + DriveMut, Se: Serializer>(
  node: &Node<S>,
  serializer: Se,
) -> Result<Se::Ok, Se::Error> {
  let mut state = serializer.serialize_struct("Node", 2)?;
  state.serialize_field("loc", &LocSpan(node.loc))?;
  state.serialize_field("stx", &node.stx)?;
  state.end()
}

impl<S: Debug + Drive + DriveMut> Debug for Node<S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    self.stx.fmt(f)
  }
}

impl<'a, S: Debug + Drive + DriveMut> Debug for LocatedNode<'a, S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    f.debug_struct("Node")
      .field("loc", &LocSpan(self.0.loc))
      .field("stx", &self.0.stx)
      .finish()
  }
}

impl<'a, S: Debug + Drive + DriveMut> Display for LocatedNode<'a, S> {
  fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
    write!(f, "{} {:?}", LocSpan(self.0.loc), self.0.stx)
  }
}

#[cfg(all(feature = "serde", feature = "serde-loc"))]
impl<S: Serialize + Drive + DriveMut> Serialize for Node<S> {
  fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
    serialize_located_node(self, serializer)
  }
}

#[cfg(all(feature = "serde", not(feature = "serde-loc")))]
impl<S: Serialize + Drive + DriveMut> Serialize for Node<S> {
  fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
    self.stx.serialize(serializer)
  }
}

#[cfg(feature = "serde")]
impl<'a, S: Serialize + Drive + DriveMut> Serialize for LocatedNode<'a, S> {
  fn serialize<Se: Serializer>(&self, serializer: Se) -> Result<Se::Ok, Se::Error> {
    serialize_located_node(self.0, serializer)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::ast::expr::Expr;
  use crate::ast::expr::IdExpr;
  #[cfg(feature = "serde")]
  use serde_json::{json, to_value};

  fn id_expr(loc: Loc, name: &'static str) -> Node<Expr> {
    let ident = Node::new(loc, IdExpr { name: name.into() });
    Node::new(loc, Expr::Id(ident))
  }

  #[test]
  fn test_node_assoc_data() {
    struct First(u32);
    struct Second(&'static str);

    let mut assoc = NodeAssocData::default();
    assert!(assoc.is_empty());

    assoc.set(First(32));
    assert!(!assoc.is_empty());
    assert_eq!(assoc.get::<First>().unwrap().0, 32);

    assoc.set(Second("ok"));
    assert_eq!(assoc.get::<First>().unwrap().0, 32);
    assert_eq!(assoc.get::<Second>().unwrap().0, "ok");

    assoc.set(First(64));
    assert_eq!(assoc.get::<First>().unwrap().0, 64);

    let first_mut = assoc.get_mut::<First>().unwrap();
    first_mut.0 = 128;
    assert_eq!(assoc.get::<First>().unwrap().0, 128);

    assert_eq!(assoc.remove::<First>().unwrap().0, 128);
    assert!(assoc.get::<First>().is_none());
    assert!(!assoc.is_empty());
    assert_eq!(assoc.remove::<Second>().unwrap().0, "ok");
    assert!(assoc.is_empty());
    assert!(assoc.remove::<Second>().is_none());
  }

  #[test]
  #[cfg(feature = "serde")]
  fn serializes_located_node_with_location() {
    let loc = Loc(2, 5);
    let node = id_expr(loc, "abc");
    let expected_stx = if cfg!(feature = "serde-loc") {
      json!({
        "$t": "Id",
        "loc": { "start": 2, "end": 5 },
        "stx": { "name": "abc" },
      })
    } else {
      json!({ "$t": "Id", "name": "abc" })
    };
    let node_json = to_value(&node).unwrap();
    let expected_node = if cfg!(feature = "serde-loc") {
      json!({
        "loc": { "start": 2, "end": 5 },
        "stx": expected_stx.clone(),
      })
    } else {
      expected_stx.clone()
    };
    assert_eq!(node_json, expected_node);

    let serialized = to_value(LocatedNode(&node)).unwrap();
    assert_eq!(
      serialized,
      json!({
        "loc": { "start": 2, "end": 5 },
        "stx": expected_stx,
      })
    );
  }

  #[test]
  fn located_node_formats_include_location() {
    let node = id_expr(Loc(10, 42), "fmt");
    let located = node.located();
    let debug_fmt = format!("{:?}", located);
    let display_fmt = format!("{}", located);

    for output in [debug_fmt, display_fmt] {
      assert!(output.contains("10..42"));
      assert!(output.contains("fmt"));
    }
  }
}
