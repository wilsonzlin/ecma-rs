//! JSDoc comment scanning and type-tag lowering for checkJs.
//!
//! `parse-js` lexes and skips comments; it does not attach them to AST nodes.
//! Callers therefore scan the raw source for the `/** … */` block comment
//! immediately preceding a declaration byte offset, then parse `@type` /
//! `@returns` / `@param` / `@typedef` / `@template` tags from that comment body.
//!
//! File-level `@typedef` names are collected by scanning all block comments so
//! later `@type` / `@param` references resolve (including `@property` object
//! shapes).
//!
//! Supported type syntax: primitives, identifiers (incl. typedef / type-param
//! names), unions (`A|B`), arrays (`T[]` / `Array<T>`), optional/`?`
//! nullability, **inline object** types (`{a: string}`), and **function**
//! types (`function(string): number`, `(s: string) => void`, and Closure
//! `function(new: T, …)` construct signatures). Object shapes also via
//! `@typedef` + `@property`. `@constructor` / `@class` synthesize construct
//! signatures + instance shapes from `this.prop` assignments.
//!
//! Qualified / CommonJS typedef names are supported: `@typedef {T} exports.Foo`
//! and nameless `@typedef {T}` attached to `exports.Foo = …` /
//! `module.exports.Foo = …`.
//!
//! Nested `@param` property sugar is supported: `@param {object} opts` followed
//! by `@param {number} opts.x` accumulates `{ x: number }` (and recursively for
//! deeper `opts.mid.prop` / `opts[].elem` paths). Missing an immediate
//! `@param {object}` parent yields **TS8032**. Unmatched root `@param` names
//! (no corresponding function parameter) yield **TS8024**. Deferred: parse-js
//! comment attachment.

use std::collections::{HashMap, HashSet};

use ordered_float::OrderedFloat;
use types_ts_interned::{
  ObjectType, Param, PropData, PropKey, Property, Shape, Signature, TypeId, TypeKind, TypeParamId,
  TypeStore,
};

use crate::check::type_expr::TypeResolver;

/// One `@param` / `@arg` / `@argument` tag.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocParam<'a> {
  pub ty: &'a str,
  pub name: Option<&'a str>,
  pub optional: bool,
}

/// One `@property` / `@prop` tag attached to a `@typedef`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocProperty<'a> {
  pub ty: &'a str,
  pub name: &'a str,
  pub optional: bool,
}

/// One `@typedef` declaration (optionally with `@property` members).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocTypedef<'a> {
  /// Typedef name, possibly a dotted namepath (`exports.Foo`). Empty when the
  /// tag is nameless and the host expression supplies the name later.
  pub name: &'a str,
  /// Braced type, or type filled from a following `@type` on the same comment.
  pub ty: Option<&'a str>,
  pub properties: Vec<JsdocProperty<'a>>,
}

/// A `@callback Name` function-type declaration: following `@param` /
/// `@returns` tags belong to the callback's signature, not the host function.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocCallback<'a> {
  pub name: &'a str,
  pub params: Vec<JsdocParam<'a>>,
  pub returns: Option<&'a str>,
}

/// One `@template` type parameter (optional constraint).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocTemplate<'a> {
  pub name: &'a str,
  pub constraint: Option<&'a str>,
}

/// Tags extracted from a single leading JSDoc block comment.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct JsdocTags<'a> {
  pub type_tag: Option<&'a str>,
  pub returns: Option<&'a str>,
  /// `@this {…}` — explicit `this` type for the annotated function (checkJs).
  pub this_type: Option<&'a str>,
  pub params: Vec<JsdocParam<'a>>,
  pub typedefs: Vec<JsdocTypedef<'a>>,
  /// `@callback Name` function-type declarations (their params/returns are
  /// routed here, never into `params` of the host function).
  pub callbacks: Vec<JsdocCallback<'a>>,
  pub templates: Vec<JsdocTemplate<'a>>,
  /// `@constructor` / `@class` — function is a constructor (construct sig).
  pub constructor: bool,
  /// `@public` / `@private` / `@protected` visibility (checkJs).
  pub accessibility: Option<&'static str>,
  /// Absolute UTF-8 range for TS18010: from `@public`/`@private`/`@protected`
  /// through the closing `*/` of the JSDoc block (matches tsc).
  pub accessibility_span: Option<(u32, u32)>,
}

impl JsdocTags<'_> {
  /// True when the comment carries callable annotations (`@param` / `@returns` /
  /// `@this` / `@template` / `@constructor`) or a whole-signature `@type`.
  pub fn has_callable_tags(&self) -> bool {
    self.type_tag.is_some()
      || self.returns.is_some()
      || self.this_type.is_some()
      || !self.params.is_empty()
      || !self.templates.is_empty()
      || self.constructor
  }

  /// Look up a `@param` type by binding name (first match wins).
  pub fn param_ty(&self, name: &str) -> Option<&str> {
    self
      .params
      .iter()
      .find(|p| p.name == Some(name))
      .map(|p| p.ty)
  }

  /// Copy tag strings so callers can mutate the checker while consulting tags.
  pub fn into_owned(self) -> OwnedJsdocTags {
    OwnedJsdocTags {
      type_tag: self.type_tag.map(str::to_owned),
      returns: self.returns.map(str::to_owned),
      this_type: self.this_type.map(str::to_owned),
      params: self
        .params
        .into_iter()
        .map(|p| OwnedJsdocParam {
          ty: p.ty.to_owned(),
          name: p.name.map(str::to_owned),
          optional: p.optional,
        })
        .collect(),
      typedefs: self
        .typedefs
        .into_iter()
        .map(|td| OwnedJsdocTypedef {
          name: td.name.to_owned(),
          ty: td.ty.map(str::to_owned),
          properties: td
            .properties
            .into_iter()
            .map(|p| OwnedJsdocProperty {
              ty: p.ty.to_owned(),
              name: p.name.to_owned(),
              optional: p.optional,
            })
            .collect(),
        })
        .collect(),
      templates: self
        .templates
        .into_iter()
        .map(|t| OwnedJsdocTemplate {
          name: t.name.to_owned(),
          constraint: t.constraint.map(str::to_owned),
        })
        .collect(),
      constructor: self.constructor,
      accessibility: self.accessibility,
      accessibility_span: self.accessibility_span,
    }
  }
}

/// Owned form of [`JsdocTags`] for use across mutable checker borrows.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct OwnedJsdocTags {
  pub type_tag: Option<String>,
  pub returns: Option<String>,
  pub this_type: Option<String>,
  pub params: Vec<OwnedJsdocParam>,
  pub typedefs: Vec<OwnedJsdocTypedef>,
  pub templates: Vec<OwnedJsdocTemplate>,
  pub constructor: bool,
  pub accessibility: Option<&'static str>,
  pub accessibility_span: Option<(u32, u32)>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedJsdocParam {
  pub ty: String,
  pub name: Option<String>,
  pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedJsdocProperty {
  pub ty: String,
  pub name: String,
  pub optional: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedJsdocTypedef {
  pub name: String,
  pub ty: Option<String>,
  pub properties: Vec<OwnedJsdocProperty>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedJsdocTemplate {
  pub name: String,
  pub constraint: Option<String>,
}

/// A root `@param` after nested `name.prop` / `opts.x` folding.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ResolvedJsdocParam {
  pub ty: TypeId,
  pub optional: bool,
}

/// TS8032 candidate: a qualified `@param` name without an immediate object parent.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocNestedParamError {
  /// Full qualified name as written (`xyz.bar.p`).
  pub qualified_name: String,
  /// Immediate parent path expected in `@param {object} {parent}` (`xyz.bar`).
  pub parent_path: String,
}

/// TS8024 candidate: a root `@param` name with no matching function parameter.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct JsdocUnmatchedParamError {
  pub name: String,
}

impl OwnedJsdocTags {
  pub fn param_ty(&self, name: &str) -> Option<&str> {
    self
      .params
      .iter()
      .find(|p| p.name.as_deref() == Some(name))
      .map(|p| p.ty.as_str())
  }
}

/// Fold nested `@param name.prop` tags into object types for root parameters.
///
/// Mirrors tsc's `parseNestedTypeLiteral`: an `@param {object|Object|object[]|Object[]} P`
/// greedily consumes following tags whose path is an immediate child of `P`,
/// recursively when those children are themselves objectish. Qualified tags that
/// are not consumed become [`JsdocNestedParamError`] (TS8032).
pub fn resolve_jsdoc_params(
  store: &TypeStore,
  params: &[OwnedJsdocParam],
  env: &JsdocLowerEnv<'_>,
) -> (
  HashMap<String, ResolvedJsdocParam>,
  Vec<JsdocNestedParamError>,
) {
  let mut stack = HashSet::new();
  let mut cache = HashMap::new();
  let mut out = HashMap::new();
  let mut errors = Vec::new();
  let mut i = 0;
  while i < params.len() {
    let param = &params[i];
    let Some(raw_name) = param.name.as_deref() else {
      i += 1;
      continue;
    };
    let path = param_path_segments(raw_name);
    if path.is_empty() {
      i += 1;
      continue;
    }
    if is_objectish_param_type(&param.ty) {
      let is_array = is_array_objectish_param_type(&param.ty);
      let (ty, next) = fold_nested_param_object(
        store, params, i, &path, is_array, env, &mut stack, &mut cache,
      );
      if path.len() == 1 {
        out.entry(path[0].clone()).or_insert(ResolvedJsdocParam {
          ty,
          optional: param.optional,
        });
      } else {
        errors.push(JsdocNestedParamError {
          qualified_name: path.join("."),
          parent_path: path[..path.len() - 1].join("."),
        });
      }
      i = next;
      continue;
    }
    if path.len() == 1 {
      let ty = lower_type(store, &param.ty, env, &mut stack, &mut cache);
      out.entry(path[0].clone()).or_insert(ResolvedJsdocParam {
        ty,
        optional: param.optional,
      });
      i += 1;
      continue;
    }
    errors.push(JsdocNestedParamError {
      qualified_name: path.join("."),
      parent_path: path[..path.len() - 1].join("."),
    });
    i += 1;
  }
  (out, errors)
}

/// Borrowed convenience wrapper around [`resolve_jsdoc_params`].
pub fn resolve_jsdoc_params_borrowed(
  store: &TypeStore,
  params: &[JsdocParam<'_>],
  env: &JsdocLowerEnv<'_>,
) -> (
  HashMap<String, ResolvedJsdocParam>,
  Vec<JsdocNestedParamError>,
) {
  let owned: Vec<OwnedJsdocParam> = params
    .iter()
    .map(|p| OwnedJsdocParam {
      ty: p.ty.to_owned(),
      name: p.name.map(str::to_owned),
      optional: p.optional,
    })
    .collect();
  resolve_jsdoc_params(store, &owned, env)
}

/// Root `@param` names that do not match any function parameter (TS8024).
///
/// Mirrors tsc `checkUnmatchedJSDocParameters` (non-`arguments` path) after
/// nested type-literal folding:
/// - index is over post-fold tags (absorbed `name.prop` children omitted;
///   unabsorbed qualified tags still occupy an index)
/// - tags at the same index as a binding-pattern parameter are excluded
/// - roots that absorbed nested children are suppressed (`isNameFirst`)
///
/// `fn_param_names[i]` is `Some(ident)` for identifier parameters and `None`
/// for binding patterns / non-id patterns.
pub fn find_unmatched_root_jsdoc_params(
  params: &[OwnedJsdocParam],
  fn_param_names: &[Option<&str>],
) -> Vec<JsdocUnmatchedParamError> {
  let mut id_names = HashSet::new();
  let mut excluded = HashSet::new();
  for (i, name) in fn_param_names.iter().enumerate() {
    match name {
      Some(n) => {
        id_names.insert(*n);
      }
      None => {
        excluded.insert(i);
      }
    }
  }

  let mut errors = Vec::new();
  let mut tag_index = 0usize;
  let mut i = 0;
  while i < params.len() {
    let param = &params[i];
    let Some(raw_name) = param.name.as_deref() else {
      i += 1;
      continue;
    };
    let path = param_path_segments(raw_name);
    if path.is_empty() {
      i += 1;
      continue;
    }
    if path.len() != 1 {
      // Unabsorbed qualified tag — TS8032 elsewhere; still occupies an index.
      tag_index += 1;
      i += 1;
      continue;
    }
    let absorbed = if is_objectish_param_type(&param.ty) {
      let next = skip_nested_param_children(params, i, &path);
      let did_absorb = next > i + 1;
      i = next;
      did_absorb
    } else {
      i += 1;
      false
    };
    let name = path[0].as_str();
    if excluded.contains(&tag_index) || id_names.contains(name) {
      tag_index += 1;
      continue;
    }
    if !absorbed {
      errors.push(JsdocUnmatchedParamError {
        name: name.to_owned(),
      });
    }
    tag_index += 1;
  }
  errors
}

/// Advance past nested `@param` children absorbed by an objectish parent at
/// `start` (same greedy walk as [`fold_nested_param_object`], without lowering).
fn skip_nested_param_children(
  params: &[OwnedJsdocParam],
  start: usize,
  parent_path: &[String],
) -> usize {
  let mut i = start + 1;
  while i < params.len() {
    let child = &params[i];
    let Some(raw_name) = child.name.as_deref() else {
      break;
    };
    let path = param_path_segments(raw_name);
    if path.len() <= parent_path.len() || path[..parent_path.len()] != *parent_path {
      break;
    }
    if path.len() != parent_path.len() + 1 {
      break;
    }
    i = if is_objectish_param_type(&child.ty) {
      skip_nested_param_children(params, i, &path)
    } else {
      i + 1
    };
  }
  i
}

fn param_path_segments(name: &str) -> Vec<String> {
  name
    .split('.')
    .map(|seg| {
      let seg = seg.trim();
      seg
        .strip_suffix("[]")
        .map(str::trim)
        .unwrap_or(seg)
        .to_owned()
    })
    .filter(|s| !s.is_empty())
    .collect()
}

fn is_objectish_param_type(ty: &str) -> bool {
  let t = ty.trim();
  if t.eq_ignore_ascii_case("object") || t == "Object" {
    return true;
  }
  if let Some(inner) = t.strip_suffix("[]") {
    let inner = inner.trim();
    return inner.eq_ignore_ascii_case("object") || inner == "Object";
  }
  false
}

fn is_array_objectish_param_type(ty: &str) -> bool {
  let t = ty.trim();
  t.ends_with("[]") && is_objectish_param_type(t)
}

fn fold_nested_param_object(
  store: &TypeStore,
  params: &[OwnedJsdocParam],
  start: usize,
  parent_path: &[String],
  is_array: bool,
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> (TypeId, usize) {
  let mut shape = Shape::new();
  let mut i = start + 1;
  while i < params.len() {
    let child = &params[i];
    let Some(raw_name) = child.name.as_deref() else {
      break;
    };
    let path = param_path_segments(raw_name);
    if path.len() <= parent_path.len() || path[..parent_path.len()] != *parent_path {
      break;
    }
    // Only immediate children (tsc stops nesting when `name.left` ≠ parent).
    if path.len() != parent_path.len() + 1 {
      break;
    }
    let prop_name = path.last().expect("path non-empty").clone();
    let (prop_ty, next) = if is_objectish_param_type(&child.ty) {
      fold_nested_param_object(
        store,
        params,
        i,
        &path,
        is_array_objectish_param_type(&child.ty),
        env,
        stack,
        cache,
      )
    } else {
      (lower_type(store, &child.ty, env, stack, cache), i + 1)
    };
    let key = PropKey::String(store.intern_name(prop_name));
    shape.properties.push(Property {
      key,
      data: PropData {
        ty: prop_ty,
        optional: child.optional,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
    i = next;
  }
  let ty = if shape.properties.is_empty() {
    // No nested props: keep bare `object`/`Object`/`object[]` semantics.
    lower_type(store, &params[start].ty, env, stack, cache)
  } else {
    let shape_id = store.intern_shape(shape);
    let obj = store.intern_object(ObjectType { shape: shape_id });
    let obj_ty = store.intern_type(TypeKind::Object(obj));
    if is_array {
      store.intern_type(TypeKind::Array {
        ty: obj_ty,
        readonly: false,
      })
    } else {
      obj_ty
    }
  };
  (ty, i)
}

/// Render `@callback` params as function-type param strings, folding nested
/// `root.prop` tags into an objectish root's inline object shape (the
/// type-string-level mirror of [`fold_nested_param_object`]). Qualified tags
/// whose root is not a declared objectish param stay standalone positional
/// params (tsc counts them for arity); their dotted path is sanitized into a
/// valid identifier since only position/optionality matter for the type.
fn render_callback_params(params: &[JsdocParam<'_>]) -> Vec<String> {
  let mut out = Vec::new();
  let mut i = 0;
  while i < params.len() {
    let param = &params[i];
    let path = param.name.map(param_path_segments).unwrap_or_default();
    if path.len() == 1 && is_objectish_param_type(&param.ty) {
      let is_array = is_array_objectish_param_type(&param.ty);
      let (shape, next) = render_callback_nested_shape(params, i, &path);
      if let Some(shape) = shape {
        let ty = if is_array {
          format!("Array<{shape}>")
        } else {
          shape
        };
        out.push(format!("{}: {ty}", path[0]));
        i = next;
        continue;
      }
    }
    let rendered = match param.name {
      Some(name) if !path.is_empty() => {
        if path.len() > 1 {
          format!("{}: {}", path.join("_"), param.ty)
        } else {
          format!("{name}: {}", param.ty)
        }
      }
      _ => param.ty.to_string(),
    };
    out.push(rendered);
    i += 1;
  }
  out
}

/// Greedy immediate-child fold for [`render_callback_params`]. Returns the
/// inline object shape string when at least one child tag was absorbed, plus
/// the index just past the consumed tags.
fn render_callback_nested_shape(
  params: &[JsdocParam<'_>],
  start: usize,
  parent_path: &[String],
) -> (Option<String>, usize) {
  let mut fields = Vec::new();
  let mut i = start + 1;
  while i < params.len() {
    let child = &params[i];
    let Some(raw_name) = child.name else {
      break;
    };
    let path = param_path_segments(raw_name);
    if path.len() != parent_path.len() + 1 || path[..parent_path.len()] != *parent_path {
      break;
    }
    let prop = &path[parent_path.len()];
    let (ty, next) = if is_objectish_param_type(&child.ty) {
      let (shape, next) = render_callback_nested_shape(params, i, &path);
      match shape {
        Some(shape) if is_array_objectish_param_type(&child.ty) => {
          (format!("Array<{shape}>"), next)
        }
        Some(shape) => (shape, next),
        None => (child.ty.to_string(), next),
      }
    } else {
      (child.ty.to_string(), i + 1)
    };
    if child.optional {
      fields.push(format!("{prop}?: {ty}"));
    } else {
      fields.push(format!("{prop}: {ty}"));
    }
    i = next;
  }
  if fields.is_empty() {
    (None, start + 1)
  } else {
    (Some(format!("{{ {} }}", fields.join(", "))), i)
  }
}

/// Locate a `@param` qualified name inside the leading JSDoc comment before
/// `decl_offset` (for TS8032 primary spans).
pub fn leading_param_name_range(
  source: &str,
  decl_offset: u32,
  qualified: &str,
) -> Option<(u32, u32)> {
  if qualified.is_empty() {
    return None;
  }
  let comment = find_leading_block_comment(source, decl_offset)?;
  let comment_start = offset_of_slice(source, comment)?;
  let mut search_from = 0;
  while let Some(rel) = comment[search_from..].find(qualified) {
    let abs = search_from + rel;
    let before = &comment[..abs];
    if let Some(brace) = before.rfind('}') {
      let between = &before[brace + 1..];
      if between.bytes().all(|b| is_js_ws(b) || b == b'*') {
        // Avoid matching a type-path occurrence inside `{…}`.
        let after_end = abs + qualified.len();
        let ok_end = after_end >= comment.len()
          || comment.as_bytes()[after_end].is_ascii_whitespace()
          || matches!(
            comment.as_bytes()[after_end],
            b'*' | b'-' | b'/' | b'\n' | b'\r'
          );
        if ok_end {
          let start = (comment_start + abs) as u32;
          let end = start + qualified.len() as u32;
          return Some((start, end));
        }
      }
    }
    search_from = abs + qualified.len().max(1);
  }
  None
}

/// Environment for lowering JSDoc type expressions under checkJs.
#[derive(Clone, Copy, Default)]
pub struct JsdocLowerEnv<'a> {
  pub resolver: Option<&'a dyn TypeResolver>,
  pub typedefs: Option<&'a HashMap<String, OwnedJsdocTypedef>>,
  pub type_params: Option<&'a HashMap<String, TypeParamId>>,
}

impl<'a> JsdocLowerEnv<'a> {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn with_resolver(mut self, resolver: Option<&'a dyn TypeResolver>) -> Self {
    self.resolver = resolver;
    self
  }

  pub fn with_typedefs(mut self, typedefs: Option<&'a HashMap<String, OwnedJsdocTypedef>>) -> Self {
    self.typedefs = typedefs;
    self
  }

  pub fn with_type_params(mut self, type_params: Option<&'a HashMap<String, TypeParamId>>) -> Self {
    self.type_params = type_params;
    self
  }
}

/// Find the `/** … */` (or `/* … */`) block comment immediately preceding
/// `offset` in UTF-8 source. Only whitespace may intervene between the
/// comment's `*/` and `offset`.
pub fn find_leading_block_comment(source: &str, offset: u32) -> Option<&str> {
  let (start, end) = find_leading_block_comment_range(source, offset)?;
  source.get(start..end)
}

/// Absolute UTF-8 `[start, end)` of the leading block comment before `offset`.
pub fn find_leading_block_comment_range(source: &str, offset: u32) -> Option<(usize, usize)> {
  let bytes = source.as_bytes();
  let mut i = offset as usize;
  if i > bytes.len() {
    return None;
  }
  // Skip whitespace immediately before the declaration.
  while i > 0 && is_js_ws(bytes[i - 1]) {
    i -= 1;
  }
  if i < 2 || bytes[i - 1] != b'/' || bytes[i - 2] != b'*' {
    return None;
  }
  // Scan backwards for the matching `/*`.
  let end = i; // exclusive end of comment (after `/`)
  let mut j = i.saturating_sub(2);
  while j > 0 {
    if bytes[j - 1] == b'/' && bytes[j] == b'*' {
      let start = j - 1;
      // Prefer doc comments (`/**`); still accept plain `/*` for `@type`.
      let _ = std::str::from_utf8(&bytes[start..end]).ok()?;
      return Some((start, end));
    }
    j -= 1;
  }
  None
}

/// Iterate `/* … */` block comments in source order (body includes delimiters).
pub fn iter_block_comments(source: &str) -> impl Iterator<Item = &str> {
  let bytes = source.as_bytes();
  let mut i = 0usize;
  std::iter::from_fn(move || {
    while i + 1 < bytes.len() {
      if bytes[i] == b'/' && bytes[i + 1] == b'*' {
        let start = i;
        i += 2;
        while i + 1 < bytes.len() {
          if bytes[i] == b'*' && bytes[i + 1] == b'/' {
            let end = i + 2;
            i = end;
            return std::str::from_utf8(&bytes[start..end]).ok();
          }
          i += 1;
        }
        return None;
      }
      i += 1;
    }
    None
  })
}

/// Collect file-scope `@typedef` declarations from every block comment.
///
/// Later typedefs with the same name overwrite earlier ones (matches tsc's
/// last-declaration-wins merging for simple aliases).
///
/// Qualified names (`exports.Foo`, `exports.ns.Foo`) are stored under the full
/// namepath. Nameless `@typedef {T}` tags bind from the following host:
/// - `exports.Foo = …` / `module.exports.Foo = …` → register short `Foo` and the
///   full path (so `@type {Foo}` / `@type {exports.Foo}` both resolve)
/// - bare `exports.Foo;` (no assignment) → not registered under the path (tsc
///   reports TS2694 for `@type {exports.Foo}` in that pattern)
///
/// Also synthesizes instance-type aliases for `@constructor` / `@class`
/// functions (from `this.prop = param` assignments) so `new: Name` / `@return
/// {Name}` resolve to the instance shape in type position.
pub fn collect_file_typedefs(source: &str) -> HashMap<String, OwnedJsdocTypedef> {
  let mut out = HashMap::new();
  let bytes = source.as_bytes();
  let mut i = 0usize;
  while i + 1 < bytes.len() {
    if bytes[i] == b'/' && bytes[i + 1] == b'*' {
      let start = i;
      i += 2;
      while i + 1 < bytes.len() {
        if bytes[i] == b'*' && bytes[i + 1] == b'/' {
          let end = i + 2;
          if let Ok(comment) = std::str::from_utf8(&bytes[start..end]) {
            let tags = parse_jsdoc_tags(comment);
            for td in tags.typedefs {
              let owned = OwnedJsdocTypedef {
                name: td.name.to_owned(),
                ty: td.ty.map(str::to_owned),
                properties: td
                  .properties
                  .into_iter()
                  .map(|p| OwnedJsdocProperty {
                    ty: p.ty.to_owned(),
                    name: p.name.to_owned(),
                    optional: p.optional,
                  })
                  .collect(),
              };
              insert_collected_typedef(&mut out, source, end, owned);
            }
            for cb in tags.callbacks {
              if cb.name.is_empty() {
                continue;
              }
              // `@callback Name` registers as a function type synthesized from
              // its `@param` / `@returns` tags so `@type {Name}` resolves.
              // Nested `@param root.prop` tags fold into an objectish root's
              // inline shape (tsc `parseNestedTypeLiteral`) — they are not
              // separate parameters (`callbackTagNestedParameter.ts`).
              let params = render_callback_params(&cb.params);
              let ret = cb.returns.unwrap_or("void");
              let owned = OwnedJsdocTypedef {
                name: cb.name.to_owned(),
                ty: Some(format!("({}) => {}", params.join(", "), ret)),
                properties: Vec::new(),
              };
              insert_collected_typedef(&mut out, source, end, owned);
            }
          }
          i = end;
          break;
        }
        i += 1;
      }
      continue;
    }
    i += 1;
  }
  // Constructor instance aliases fill gaps only (real `@typedef` wins).
  for (name, td) in collect_file_constructor_typedefs(source) {
    out.entry(name).or_insert(td);
  }
  out
}

fn insert_collected_typedef(
  out: &mut HashMap<String, OwnedJsdocTypedef>,
  source: &str,
  comment_end: usize,
  mut owned: OwnedJsdocTypedef,
) {
  if owned.name.is_empty() {
    let Some(host) = parse_typedef_host_after(source, comment_end) else {
      return;
    };
    if !host.is_assign {
      // Bare `exports.Foo;` — typedef is source-only; qualified refs → TS2694.
      return;
    }
    let short = host
      .path
      .rsplit('.')
      .next()
      .filter(|s| !s.is_empty())
      .unwrap_or(host.path);
    owned.name = short.to_owned();
    out.insert(short.to_owned(), owned.clone());
    if host.path != short {
      let mut qualified = owned.clone();
      qualified.name = host.path.to_owned();
      out.insert(host.path.to_owned(), qualified);
    }
    return;
  }
  let name = owned.name.clone();
  out.insert(name, owned);
}

#[derive(Debug, Clone, Copy)]
struct TypedefHost<'a> {
  path: &'a str,
  is_assign: bool,
}

/// Parse `exports.Foo` / `module.exports.Foo` (optionally `= …`) after a nameless
/// `@typedef` comment.
fn parse_typedef_host_after(source: &str, after_comment: usize) -> Option<TypedefHost<'_>> {
  let bytes = source.as_bytes();
  let mut i = after_comment;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  let (path, after_path) = take_namepath(source, i);
  let path = path?;
  if !path.contains('.') {
    return None;
  }
  let mut j = after_path;
  while j < bytes.len() && is_js_ws(bytes[j]) {
    j += 1;
  }
  let is_assign = bytes.get(j) == Some(&b'=');
  Some(TypedefHost { path, is_assign })
}

/// Location of a named `class` declaration in source (UTF-8 byte offsets).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct JsClassLoc {
  /// Offset of the `class` keyword.
  pub class_keyword: u32,
  /// Absolute offset of the first byte inside the class `{…}` body.
  pub body_start: u32,
}

/// Find the first `class Name {…}` declaration with the given name.
pub fn find_named_class_loc(source: &str, class_name: &str) -> Option<JsClassLoc> {
  for (name, loc, _body) in iter_named_classes(source) {
    if name == class_name {
      return Some(loc);
    }
  }
  None
}

/// Leading JSDoc tags attached to `class Name`, if present.
pub fn class_leading_jsdoc_tags<'a>(source: &'a str, class_name: &str) -> Option<JsdocTags<'a>> {
  let loc = find_named_class_loc(source, class_name)?;
  leading_jsdoc_tags(source, loc.class_keyword)
}

/// Leading JSDoc tags attached to `constructor` inside `class Name`, if present.
pub fn constructor_leading_jsdoc_tags<'a>(
  source: &'a str,
  class_name: &str,
) -> Option<JsdocTags<'a>> {
  let loc = find_named_class_loc(source, class_name)?;
  let body = source.get(loc.body_start as usize..)?;
  let ctor_rel = find_constructor_keyword_offset(body)?;
  leading_jsdoc_tags(source, loc.body_start.saturating_add(ctor_rel))
}

/// Collect `this.prop = rhs` assignments inside `class Name { constructor… }`
/// bodies. Returns `class_name → [(prop, rhs_ident)]` in source order.
pub fn collect_js_class_this_props(source: &str) -> HashMap<String, Vec<(String, String)>> {
  let mut out: HashMap<String, Vec<(String, String)>> = HashMap::new();
  for (name, _loc, class_body) in iter_named_classes(source) {
    // Prefer constructor body; fall back to whole class body.
    let scan_src = find_constructor_body(class_body).unwrap_or(class_body);
    let props = scan_this_property_assignments(scan_src);
    if !props.is_empty() {
      out.insert(name.to_owned(), props);
    }
  }
  out
}

fn iter_named_classes(source: &str) -> impl Iterator<Item = (&str, JsClassLoc, &str)> + '_ {
  let bytes = source.as_bytes();
  let mut i = 0usize;
  std::iter::from_fn(move || {
    while i < bytes.len() {
      // Match `class` as a keyword.
      if bytes.get(i..i + 5) == Some(b"class")
        && (i == 0 || !is_ident_continue(bytes[i - 1]))
        && bytes
          .get(i + 5)
          .copied()
          .is_some_and(|b| is_js_ws(b) || b == b'{')
      {
        let class_keyword = i as u32;
        let mut j = i + 5;
        while j < bytes.len() && is_js_ws(bytes[j]) {
          j += 1;
        }
        let name_start = j;
        while j < bytes.len() && is_ident_continue(bytes[j]) {
          j += 1;
        }
        if j == name_start {
          i += 5;
          continue;
        }
        let Ok(name) = std::str::from_utf8(&bytes[name_start..j]) else {
          i = j;
          continue;
        };
        let Some(class_body) = extract_brace_group(bytes, j) else {
          i = j;
          continue;
        };
        // `extract_brace_group` returns the interior of `{…}`; locate its start.
        let body_start = (class_body.as_ptr() as usize).saturating_sub(bytes.as_ptr() as usize);
        let loc = JsClassLoc {
          class_keyword,
          body_start: body_start as u32,
        };
        i = j;
        return Some((name, loc, class_body));
      }
      i += 1;
    }
    None
  })
}

fn find_constructor_keyword_offset(class_body: &str) -> Option<u32> {
  let bytes = class_body.as_bytes();
  let mut i = 0usize;
  while i + 11 <= bytes.len() {
    if bytes.get(i..i + 11) == Some(b"constructor")
      && (i == 0 || !is_ident_continue(bytes[i - 1]))
      && bytes
        .get(i + 11)
        .copied()
        .map(|b| !is_ident_continue(b))
        .unwrap_or(true)
    {
      return Some(i as u32);
    }
    i += 1;
  }
  None
}

fn find_constructor_body(class_body: &str) -> Option<&str> {
  let bytes = class_body.as_bytes();
  let offset = find_constructor_keyword_offset(class_body)? as usize;
  extract_brace_group(bytes, offset + 11)
}

/// Synthesize instance `@typedef`-like shapes for `@constructor` functions.
pub fn collect_file_constructor_typedefs(source: &str) -> HashMap<String, OwnedJsdocTypedef> {
  let mut out = HashMap::new();
  let bytes = source.as_bytes();
  for comment in iter_block_comments(source) {
    let tags = parse_jsdoc_tags(comment);
    if !tags.constructor {
      continue;
    }
    // Locate this comment's end offset in `source`.
    let Some(comment_start) = source.find(comment) else {
      continue;
    };
    let after = comment_start + comment.len();
    let Some((name, body)) = parse_constructor_decl_after(bytes, after) else {
      continue;
    };
    let param_tys: HashMap<&str, &str> = tags
      .params
      .iter()
      .filter_map(|p| p.name.map(|n| (n, p.ty)))
      .collect();
    let assignments = scan_this_property_assignments(body);
    let mut properties = Vec::new();
    let mut seen = HashSet::new();
    for (prop, rhs) in assignments {
      if !seen.insert(prop.clone()) {
        continue;
      }
      let ty = param_tys
        .get(rhs.as_str())
        .copied()
        .unwrap_or("*")
        .to_owned();
      properties.push(OwnedJsdocProperty {
        ty,
        name: prop,
        optional: false,
      });
    }
    out.insert(
      name.clone(),
      OwnedJsdocTypedef {
        name,
        ty: Some("Object".to_owned()),
        properties,
      },
    );
  }
  out
}

/// After a `@constructor` comment, parse `function Name… {body}` or
/// `var/let/const Name = function… {body}`.
fn parse_constructor_decl_after<'a>(bytes: &'a [u8], mut i: usize) -> Option<(String, &'a str)> {
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  let rest = std::str::from_utf8(&bytes[i..]).ok()?;
  let (name, body_start_rel) = if let Some(after_fn) = rest.strip_prefix("function") {
    let after_fn = after_fn.trim_start();
    let name_end = after_fn
      .char_indices()
      .find(|(_, c)| !c.is_ascii_alphanumeric() && *c != '_' && *c != '$')
      .map(|(idx, _)| idx)
      .unwrap_or(after_fn.len());
    if name_end == 0 {
      return None;
    }
    let name = after_fn[..name_end].to_owned();
    let after_name = &after_fn[name_end..];
    let rel = rest.len() - after_name.len();
    (name, rel)
  } else if let Some(after_kw) = strip_var_keyword(rest) {
    let after_kw = after_kw.trim_start();
    let name_end = after_kw
      .char_indices()
      .find(|(_, c)| !c.is_ascii_alphanumeric() && *c != '_' && *c != '$')
      .map(|(idx, _)| idx)
      .unwrap_or(after_kw.len());
    if name_end == 0 {
      return None;
    }
    let name = after_kw[..name_end].to_owned();
    let after_name = after_kw[name_end..].trim_start();
    let after_eq = after_name.strip_prefix('=')?.trim_start();
    let after_fn = after_eq.strip_prefix("function")?.trim_start();
    // Skip optional name on function expression.
    let after_fn = if after_fn.starts_with('(') {
      after_fn
    } else {
      let n_end = after_fn
        .char_indices()
        .find(|(_, c)| !c.is_ascii_alphanumeric() && *c != '_' && *c != '$')
        .map(|(idx, _)| idx)
        .unwrap_or(after_fn.len());
      after_fn[n_end..].trim_start()
    };
    let rel = rest.len() - after_fn.len();
    (name, rel)
  } else {
    return None;
  };
  let abs = i + body_start_rel;
  let body = extract_brace_group(bytes, abs)?;
  Some((name, body))
}

fn strip_var_keyword(s: &str) -> Option<&str> {
  for kw in ["var", "let", "const"] {
    if let Some(rest) = s.strip_prefix(kw) {
      let b = rest.as_bytes().first().copied()?;
      if is_js_ws(b) {
        return Some(rest);
      }
    }
  }
  None
}

fn extract_brace_group(bytes: &[u8], mut i: usize) -> Option<&str> {
  while i < bytes.len() && bytes[i] != b'{' {
    // Stop if we hit another statement boundary without a body.
    if bytes[i] == b';' {
      return None;
    }
    i += 1;
  }
  if i >= bytes.len() || bytes[i] != b'{' {
    return None;
  }
  let start = i;
  let mut depth = 0i32;
  let mut in_str: Option<u8> = None;
  while i < bytes.len() {
    let b = bytes[i];
    if let Some(q) = in_str {
      if b == q && bytes.get(i.wrapping_sub(1)) != Some(&b'\\') {
        in_str = None;
      }
      i += 1;
      continue;
    }
    match b {
      b'"' | b'\'' | b'`' => in_str = Some(b),
      b'{' => depth += 1,
      b'}' => {
        depth -= 1;
        if depth == 0 {
          return std::str::from_utf8(&bytes[start..=i]).ok();
        }
      }
      _ => {}
    }
    i += 1;
  }
  None
}

/// Parse `@type`, `@returns`/`@return`, `@param`/`@arg`/`@argument`,
/// `@typedef`, `@property`/`@prop`, and `@template` tags from a block comment.
pub fn parse_jsdoc_tags(comment: &str) -> JsdocTags<'_> {
  parse_jsdoc_tags_at(comment, 0)
}

/// Like [`parse_jsdoc_tags`], but `comment_abs_start` is the absolute UTF-8
/// offset of `comment` in the file (so accessibility spans are absolute).
pub fn parse_jsdoc_tags_at(comment: &str, comment_abs_start: usize) -> JsdocTags<'_> {
  let body = strip_block_comment_delimiters(comment);
  let body_abs = comment_abs_start
    + if comment.as_bytes().get(0..3) == Some(b"/**") {
      3
    } else if comment.as_bytes().get(0..2) == Some(b"/*") {
      2
    } else {
      0
    };
  // Absolute start of the closing `*/` (tsc TS18010 end).
  let close_star_abs = comment_abs_start + comment.len().saturating_sub(2);
  let mut tags = JsdocTags::default();
  let mut current_typedef: Option<usize> = None;
  let mut current_callback: Option<usize> = None;
  let bytes = body.as_bytes();
  let mut i = 0;
  while i < bytes.len() {
    if bytes[i] == b'@' {
      let name_start = i + 1;
      let mut name_end = name_start;
      while name_end < bytes.len() && bytes[name_end].is_ascii_alphabetic() {
        name_end += 1;
      }
      if name_end == name_start {
        i += 1;
        continue;
      }
      let name = &body[name_start..name_end];
      let mut cursor = name_end;
      while cursor < bytes.len() && is_js_ws(bytes[cursor]) {
        cursor += 1;
      }

      match name {
        "template" => {
          let (templates, after) = take_templates(body, cursor);
          tags.templates.extend(templates);
          i = after;
          continue;
        }
        "typedef" => {
          let (td, after) = take_typedef(body, cursor);
          if let Some(td) = td {
            tags.typedefs.push(td);
            current_typedef = Some(tags.typedefs.len() - 1);
          }
          current_callback = None;
          i = after;
          continue;
        }
        "callback" => {
          // `@callback Name` declares a function type; subsequent @param /
          // @returns belong to it, never to the host function.
          let (cb_name, after) = take_namepath(body, cursor);
          tags.callbacks.push(JsdocCallback {
            name: cb_name.unwrap_or(""),
            params: Vec::new(),
            returns: None,
          });
          current_callback = Some(tags.callbacks.len() - 1);
          current_typedef = None;
          i = after;
          continue;
        }
        "property" | "prop" => {
          if let Some((prop, after)) = take_property(body, cursor) {
            if let Some(idx) = current_typedef {
              tags.typedefs[idx].properties.push(prop);
            }
            i = after;
            continue;
          }
          i = name_end;
          continue;
        }
        "constructor" | "class" => {
          tags.constructor = true;
          i = name_end;
          continue;
        }
        "public" | "private" | "protected" => {
          if tags.accessibility.is_none() {
            tags.accessibility = Some(match name {
              "public" => "public",
              "private" => "private",
              "protected" => "protected",
              _ => unreachable!(),
            });
            // tsc primary: `@tag` … up to (not including) closing `*/`.
            let start = (body_abs + i) as u32;
            let end = close_star_abs as u32;
            if end >= start {
              tags.accessibility_span = Some((start, end));
            }
          }
          i = name_end;
          continue;
        }
        _ => {}
      }

      if let Some((ty, after)) = take_braced_type(body, cursor) {
        match name {
          "type" => {
            if tags.type_tag.is_none() {
              tags.type_tag = Some(ty);
            }
            // `@typedef Name` + `@type {T}` on the same comment.
            if let Some(idx) = current_typedef {
              if tags.typedefs[idx].ty.is_none() {
                tags.typedefs[idx].ty = Some(ty);
              }
            }
          }
          "returns" | "return" if tags.returns.is_none() => {
            if let Some(idx) = current_callback {
              if tags.callbacks[idx].returns.is_none() {
                tags.callbacks[idx].returns = Some(ty);
              }
            } else {
              tags.returns = Some(ty);
            }
          }
          "this" if tags.this_type.is_none() => tags.this_type = Some(ty),
          "param" | "arg" | "argument" => {
            let (ty, optional_from_ty) = strip_closure_optional(ty);
            let (param_name, optional_from_name, after_name) = take_param_name(body, after);
            let param = JsdocParam {
              ty,
              name: param_name,
              optional: optional_from_ty || optional_from_name,
            };
            if let Some(idx) = current_callback {
              tags.callbacks[idx].params.push(param);
            } else {
              tags.params.push(param);
            }
            i = after_name;
            continue;
          }
          _ => {}
        }
        i = after;
        continue;
      }
      i = name_end;
      continue;
    }
    i += 1;
  }
  tags
}

/// Convenience: leading `@type {…}` type string before `offset`, if any.
pub fn leading_type_tag<'a>(source: &'a str, offset: u32) -> Option<&'a str> {
  let comment = find_leading_block_comment(source, offset)?;
  parse_jsdoc_tags(comment).type_tag
}

/// Leading JSDoc tags before `offset`, if a block comment is adjacent.
pub fn leading_jsdoc_tags<'a>(source: &'a str, offset: u32) -> Option<JsdocTags<'a>> {
  let (start, end) = find_leading_block_comment_range(source, offset)?;
  let comment = source.get(start..end)?;
  Some(parse_jsdoc_tags_at(comment, start))
}

/// Lower a JSDoc type expression string into an interned [`TypeId`].
///
/// Convenience wrapper with no typedef / type-param environment.
pub fn lower_jsdoc_type(
  store: &TypeStore,
  raw: &str,
  resolver: Option<&dyn TypeResolver>,
) -> TypeId {
  lower_jsdoc_type_with(store, raw, &JsdocLowerEnv::new().with_resolver(resolver))
}

/// Lower a JSDoc type expression with typedef and type-parameter resolution.
pub fn lower_jsdoc_type_with(store: &TypeStore, raw: &str, env: &JsdocLowerEnv<'_>) -> TypeId {
  let mut stack = HashSet::new();
  let mut cache = HashMap::new();
  lower_type(store, raw.trim(), env, &mut stack, &mut cache)
}

fn lower_type(
  store: &TypeStore,
  raw: &str,
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  let mut s = raw.trim();
  if s.is_empty() {
    return store.primitive_ids().any;
  }
  // Strip balanced outer parentheses.
  while s.starts_with('(') && s.ends_with(')') && balanced_parens(s) {
    s = s[1..s.len() - 1].trim();
  }

  // Nullable prefix/suffix (Closure / TS JSDoc): `?T` / `T?` → `T | null`.
  let nullable = if let Some(rest) = s.strip_prefix('?') {
    s = rest.trim();
    true
  } else if let Some(rest) = s.strip_suffix('?') {
    // Avoid treating `T[]?` as optional of `T[` — only when `?` is outermost.
    s = rest.trim();
    true
  } else {
    false
  };

  // Function types before union split so `function(): A | B` / `(x: A) => B | C`
  // keep `|` inside the signature (tsc JSDoc function types are atomic).
  let ty = if let Some(fn_ty) = parse_function_type(s) {
    lower_function_type(store, &fn_ty, env, stack, cache)
  } else if let Some(union) = split_top_level_union(s) {
    let members: Vec<TypeId> = union
      .into_iter()
      .map(|part| lower_type(store, part, env, stack, cache))
      .collect();
    store.union(members)
  } else if is_postfix_array(s) {
    let elem = s[..s.len() - 2].trim();
    let elem_ty = lower_type(store, elem, env, stack, cache);
    store.intern_type(TypeKind::Array {
      ty: elem_ty,
      readonly: false,
    })
  } else if let Some(inner) = strip_generic(s, "Array") {
    let elem_ty = lower_type(store, inner, env, stack, cache);
    store.intern_type(TypeKind::Array {
      ty: elem_ty,
      readonly: false,
    })
  } else if let Some(obj) = parse_inline_object_type(s) {
    lower_inline_object(store, &obj, env, stack, cache)
  } else {
    lower_atomic(store, s, env, stack, cache)
  };

  if nullable {
    let null = store.primitive_ids().null;
    store.union(vec![ty, null])
  } else {
    ty
  }
}

fn lower_atomic(
  store: &TypeStore,
  name: &str,
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  let prim = store.primitive_ids();
  if let Some(lit) = parse_literal_type(store, name) {
    return lit;
  }
  match name {
    "*" | "any" => prim.any,
    "unknown" => prim.unknown,
    "never" => prim.never,
    "void" => prim.void,
    "null" => prim.null,
    "undefined" => prim.undefined,
    "string" => prim.string,
    "number" => prim.number,
    "boolean" | "bool" => prim.boolean,
    "bigint" => prim.bigint,
    "symbol" => prim.symbol,
    // Bare `object` / `Object` without properties → `any` (permissive checkJs).
    // Bare `function` / `Function` → loosely typed callable (`(...args: any) => any`).
    "object" | "Object" => prim.any,
    "function" | "Function" => loose_function_type(store),
    _ => {
      if let Some(params) = env.type_params {
        if let Some(id) = params.get(name) {
          return store.intern_type(TypeKind::TypeParam(*id));
        }
      }
      if let Some(typedefs) = env.typedefs {
        if typedefs.contains_key(name) {
          return lower_typedef_name(store, name, env, stack, cache);
        }
      }
      if let Some(resolver) = env.resolver {
        if name.contains('.') {
          let path: Vec<String> = name.split('.').map(str::to_owned).collect();
          // Try the type namespace first, then the value namespace: classes
          // assigned via property access (`Outer.Inner = class {…}`) live in
          // the value namespace but name an instance type
          // (`typeFromPropertyAssignment24.ts`).
          if let Some(def) = resolver
            .resolve_type_name(&path)
            .or_else(|| resolver.resolve_typeof(&path))
          {
            return store.intern_type(TypeKind::Ref {
              def,
              args: Vec::new(),
            });
          }
        } else if let Some(def) = resolver.resolve_type_name(&[name.to_string()]) {
          return store.intern_type(TypeKind::Ref {
            def,
            args: Vec::new(),
          });
        }
      }
      // Unresolved name: match tsc's permissive checkJs recovery with `any`.
      // Callers may emit TS2694 for unresolved dotted namepaths.
      prim.any
    }
  }
}

/// True when `raw` is a dotted namepath (`exports.Foo`) with no typedef /
/// type-param / resolver hit — the checkJs path that tsc reports as TS2694.
pub fn unresolved_jsdoc_qualified_name<'a>(
  raw: &'a str,
  env: &JsdocLowerEnv<'_>,
) -> Option<&'a str> {
  let s = strip_jsdoc_nullability(raw.trim());
  if !is_simple_namepath(s) || !s.contains('.') {
    return None;
  }
  if let Some(params) = env.type_params {
    if params.contains_key(s) {
      return None;
    }
  }
  if let Some(typedefs) = env.typedefs {
    if typedefs.contains_key(s) {
      return None;
    }
  }
  if let Some(resolver) = env.resolver {
    let path: Vec<String> = s.split('.').map(str::to_owned).collect();
    // Value-namespace classes assigned via property access
    // (`Outer.Inner = class {…}`) also name an instance type
    // (`typeFromPropertyAssignment24.ts`).
    if resolver
      .resolve_type_name(&path)
      .or_else(|| resolver.resolve_typeof(&path))
      .is_some()
    {
      return None;
    }
  }
  Some(s)
}

fn strip_jsdoc_nullability(s: &str) -> &str {
  let s = s.strip_prefix('?').unwrap_or(s).trim();
  s.strip_suffix('?').unwrap_or(s).trim()
}

fn is_simple_namepath(s: &str) -> bool {
  if s.is_empty() {
    return false;
  }
  let bytes = s.as_bytes();
  let mut i = 0usize;
  loop {
    if i >= bytes.len() || !(bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' || bytes[i] == b'$')
    {
      return false;
    }
    i += 1;
    while i < bytes.len()
      && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'$')
    {
      i += 1;
    }
    if i == bytes.len() {
      return true;
    }
    if bytes[i] != b'.' {
      return false;
    }
    i += 1;
  }
}

/// Locate the rightmost segment of a qualified type name inside the leading
/// `@type {…}` comment before `decl_offset` (for TS2694 primary spans).
pub fn leading_type_tag_member_range(
  source: &str,
  decl_offset: u32,
  qualified: &str,
) -> Option<(u32, u32)> {
  let comment = find_leading_block_comment(source, decl_offset)?;
  let comment_start = offset_of_slice(source, comment)?;
  let member = qualified.rsplit('.').next()?;
  // Prefer an exact `{qualified}` occurrence inside the comment.
  let path_rel = comment
    .find(&format!("{{{qualified}}}"))
    .map(|i| i + 1)
    .or_else(|| comment.find(qualified))?;
  let member_rel = path_rel + qualified.len() - member.len();
  let start = (comment_start + member_rel) as u32;
  let end = start + member.len() as u32;
  Some((start, end))
}

fn offset_of_slice(source: &str, slice: &str) -> Option<usize> {
  let src = source.as_ptr() as usize;
  let sub = slice.as_ptr() as usize;
  if sub < src || sub + slice.len() > src + source.len() {
    return None;
  }
  Some(sub - src)
}

fn loose_function_type(store: &TypeStore) -> TypeId {
  let any = store.primitive_ids().any;
  let sig = Signature {
    params: vec![Param {
      name: None,
      ty: any,
      optional: false,
      rest: true,
    }],
    ret: any,
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  })
}

fn parse_literal_type(store: &TypeStore, raw: &str) -> Option<TypeId> {
  let s = raw.trim();
  if s == "true" {
    return Some(store.intern_type(TypeKind::BooleanLiteral(true)));
  }
  if s == "false" {
    return Some(store.intern_type(TypeKind::BooleanLiteral(false)));
  }
  if (s.starts_with('"') && s.ends_with('"') && s.len() >= 2)
    || (s.starts_with('\'') && s.ends_with('\'') && s.len() >= 2)
  {
    let inner = &s[1..s.len() - 1];
    let name = store.intern_name(inner.to_string());
    return Some(store.intern_type(TypeKind::StringLiteral(name)));
  }
  // Integer / simple float literals (no exponent) used in JSDoc unions.
  if !s.is_empty()
    && s
      .bytes()
      .all(|b| b.is_ascii_digit() || b == b'.' || b == b'-')
    && s.chars().any(|c| c.is_ascii_digit())
  {
    if let Ok(n) = s.parse::<f64>() {
      return Some(store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(n))));
    }
  }
  None
}

/// Parsed inline object type `{ a: string, b?: number }`.
#[derive(Debug, Clone, PartialEq, Eq)]
struct InlineObjectProp<'a> {
  name: &'a str,
  ty: &'a str,
  optional: bool,
}

fn parse_inline_object_type(s: &str) -> Option<Vec<InlineObjectProp<'_>>> {
  let trimmed = s.trim();
  if !trimmed.starts_with('{') || !trimmed.ends_with('}') || !balanced_braces(trimmed) {
    return None;
  }
  // Index signatures / mapped types are deferred.
  let inner = trimmed[1..trimmed.len() - 1].trim();
  if inner.is_empty() {
    return Some(Vec::new());
  }
  if inner.starts_with('[') {
    return None;
  }
  let parts = split_top_level(inner, &[b',', b';']);
  let mut props = Vec::new();
  for part in parts {
    let part = part.trim();
    if part.is_empty() {
      continue;
    }
    let prop = parse_object_prop(part)?;
    props.push(prop);
  }
  Some(props)
}

fn parse_object_prop(part: &str) -> Option<InlineObjectProp<'_>> {
  let bytes = part.as_bytes();
  let mut i = 0;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return None;
  }
  let (name, after_name) = if bytes[i] == b'"' || bytes[i] == b'\'' {
    let quote = bytes[i];
    let start = i + 1;
    let mut j = start;
    while j < bytes.len() && bytes[j] != quote {
      j += 1;
    }
    if j >= bytes.len() {
      return None;
    }
    (Some(&part[start..j]), j + 1)
  } else {
    let start = i;
    while i < bytes.len()
      && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'$')
    {
      i += 1;
    }
    if i == start {
      return None;
    }
    (Some(&part[start..i]), i)
  };
  let name = name?;
  let mut j = after_name;
  while j < bytes.len() && is_js_ws(bytes[j]) {
    j += 1;
  }
  let mut optional = false;
  if j < bytes.len() && bytes[j] == b'?' {
    optional = true;
    j += 1;
    while j < bytes.len() && is_js_ws(bytes[j]) {
      j += 1;
    }
  }
  if j >= bytes.len() || bytes[j] != b':' {
    return None;
  }
  j += 1;
  let ty = part[j..].trim();
  if ty.is_empty() {
    return None;
  }
  let (ty, opt_eq) = strip_closure_optional(ty);
  Some(InlineObjectProp {
    name,
    ty,
    optional: optional || opt_eq,
  })
}

fn lower_inline_object(
  store: &TypeStore,
  props: &[InlineObjectProp<'_>],
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  let owned: Vec<OwnedJsdocProperty> = props
    .iter()
    .map(|p| OwnedJsdocProperty {
      name: p.name.to_owned(),
      ty: p.ty.to_owned(),
      optional: p.optional,
    })
    .collect();
  lower_object_properties(store, &owned, env, stack, cache)
}

/// Parsed JSDoc / TS-in-JSDoc function type.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedFunctionType<'a> {
  params: Vec<ParsedFnParam<'a>>,
  ret: Option<&'a str>,
  this_ty: Option<&'a str>,
  /// Closure `new: InstanceType` — construct signature (return = instance).
  new_ty: Option<&'a str>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct ParsedFnParam<'a> {
  name: Option<&'a str>,
  ty: &'a str,
  optional: bool,
  rest: bool,
}

fn parse_function_type(s: &str) -> Option<ParsedFunctionType<'_>> {
  let trimmed = s.trim();
  // Closure: `function(…): Ret` / `function(…)`
  if let Some(rest) = strip_function_keyword(trimmed) {
    return parse_closure_function_type(rest);
  }
  // TypeScript: `(… ) => Ret`
  parse_ts_arrow_function_type(trimmed)
}

fn strip_function_keyword(s: &str) -> Option<&str> {
  let trimmed = s.trim();
  if !trimmed.starts_with("function") {
    return None;
  }
  let rest = &trimmed["function".len()..];
  if rest.is_empty() {
    // Bare `function` handled in `lower_atomic`.
    return None;
  }
  let first = rest.as_bytes()[0];
  if first == b'(' || is_js_ws(first) {
    Some(rest.trim_start())
  } else {
    None
  }
}

fn parse_closure_function_type(after_function: &str) -> Option<ParsedFunctionType<'_>> {
  let s = after_function.trim();
  if !s.starts_with('(') {
    return None;
  }
  let (params_raw, after_idx) = take_paren_group(s, 0)?;
  let (params, this_ty, new_ty) = parse_fn_params(params_raw)?;
  let after = s[after_idx..].trim_start();
  let ret = if let Some(rest) = after.strip_prefix(':') {
    let ret = rest.trim();
    if ret.is_empty() {
      None
    } else {
      Some(ret)
    }
  } else if after.is_empty() {
    None
  } else {
    // Trailing junk — not a function type.
    return None;
  };
  Some(ParsedFunctionType {
    params,
    ret,
    this_ty,
    new_ty,
  })
}

fn parse_ts_arrow_function_type(s: &str) -> Option<ParsedFunctionType<'_>> {
  let trimmed = s.trim();
  if !trimmed.starts_with('(') {
    return None;
  }
  let arrow_at = find_top_level_arrow(trimmed)?;
  let params_part = trimmed[..arrow_at].trim();
  let ret = trimmed[arrow_at + 2..].trim();
  if ret.is_empty() {
    return None;
  }
  let (params_raw, after_idx) = take_paren_group(params_part, 0)?;
  if !params_part[after_idx..].trim().is_empty() {
    return None;
  }
  let (params, this_ty, new_ty) = parse_fn_params(params_raw)?;
  Some(ParsedFunctionType {
    params,
    ret: Some(ret),
    this_ty,
    new_ty,
  })
}

fn parse_fn_params(inner: &str) -> Option<(Vec<ParsedFnParam<'_>>, Option<&str>, Option<&str>)> {
  let inner = inner.trim();
  if inner.is_empty() {
    return Some((Vec::new(), None, None));
  }
  let parts = split_top_level(inner, &[b',']);
  let mut params = Vec::new();
  let mut this_ty = None;
  let mut new_ty = None;
  for part in parts {
    let part = part.trim();
    if part.is_empty() {
      continue;
    }
    // `this: Type` — call signature this-type.
    if let Some(rest) = part.strip_prefix("this:") {
      this_ty = Some(rest.trim());
      continue;
    }
    // `new: InstanceType` — construct signature (tsc: first param named `new`).
    if let Some(rest) = part.strip_prefix("new:") {
      new_ty = Some(rest.trim());
      continue;
    }
    let mut rest = false;
    let mut body = part;
    if let Some(r) = body.strip_prefix("...") {
      rest = true;
      body = r.trim();
    }
    // `name: Type` or bare `Type` (Closure) or `name?: Type`.
    if let Some((name, ty_raw)) = split_name_colon_type(body) {
      let (name, optional_from_name) = match name.strip_suffix('?') {
        Some(n) => (n.trim(), true),
        None => (name, false),
      };
      let (ty, optional_from_ty) = strip_closure_optional(ty_raw.trim());
      params.push(ParsedFnParam {
        name: if name.is_empty() { None } else { Some(name) },
        ty,
        optional: optional_from_name || optional_from_ty,
        rest,
      });
    } else {
      let (ty, optional) = strip_closure_optional(body);
      params.push(ParsedFnParam {
        name: None,
        ty,
        optional,
        rest,
      });
    }
  }
  Some((params, this_ty, new_ty))
}

/// Split `name: type` at the first top-level `:`. Returns None when there is no
/// colon (bare type) or when the left side is not an identifier-ish name.
fn split_name_colon_type(s: &str) -> Option<(&str, &str)> {
  let bytes = s.as_bytes();
  let mut depth_paren = 0i32;
  let mut depth_brace = 0i32;
  let mut depth_angle = 0i32;
  let mut in_str: Option<u8> = None;
  for (i, &b) in bytes.iter().enumerate() {
    if let Some(q) = in_str {
      if b == q {
        in_str = None;
      }
      continue;
    }
    match b {
      b'"' | b'\'' => in_str = Some(b),
      b'(' => depth_paren += 1,
      b')' => depth_paren -= 1,
      b'{' => depth_brace += 1,
      b'}' => depth_brace -= 1,
      b'<' => depth_angle += 1,
      b'>' => depth_angle -= 1,
      b':' if depth_paren == 0 && depth_brace == 0 && depth_angle == 0 => {
        let name = s[..i].trim();
        let ty = s[i + 1..].trim();
        if name.is_empty() || ty.is_empty() {
          return None;
        }
        // Left must look like a parameter name (ident / ident?).
        let name_core = name.strip_suffix('?').unwrap_or(name);
        if is_ident(name_core) {
          return Some((name, ty));
        }
        return None;
      }
      _ => {}
    }
  }
  None
}

fn is_ident(s: &str) -> bool {
  let mut chars = s.chars();
  let Some(first) = chars.next() else {
    return false;
  };
  if !(first.is_ascii_alphabetic() || first == '_' || first == '$') {
    return false;
  }
  chars.all(|c| c.is_ascii_alphanumeric() || c == '_' || c == '$')
}

fn lower_function_type(
  store: &TypeStore,
  parsed: &ParsedFunctionType<'_>,
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  let prim = store.primitive_ids();
  let mut params = Vec::with_capacity(parsed.params.len());
  for p in &parsed.params {
    let mut ty = lower_type(store, p.ty, env, stack, cache);
    if p.rest {
      // Rest params are arrays of the element type unless already an array.
      if !matches!(store.type_kind(ty), TypeKind::Array { .. }) {
        ty = store.intern_type(TypeKind::Array {
          ty,
          readonly: false,
        });
      }
    }
    let name = p.name.map(|n| store.intern_name(n.to_string()));
    params.push(Param {
      name,
      ty,
      optional: p.optional,
      rest: p.rest,
    });
  }
  // Closure `function(new: T, …): R` → construct signature returning `T`.
  // The trailing `: R` is ignored for construct signatures (tsc
  // `getReturnTypeFromAnnotation` / `isJSDocConstructSignature`).
  if let Some(new_raw) = parsed.new_ty {
    let instance = lower_type(store, new_raw, env, stack, cache);
    let sig = Signature {
      params,
      ret: instance,
      type_params: Vec::new(),
      this_param: None,
    };
    let sig_id = store.intern_signature(sig);
    let mut shape = Shape::new();
    shape.construct_signatures.push(sig_id);
    let shape_id = store.intern_shape(shape);
    let obj = store.intern_object(ObjectType { shape: shape_id });
    return store.intern_type(TypeKind::Object(obj));
  }
  let ret = parsed
    .ret
    .map(|r| lower_type(store, r, env, stack, cache))
    .unwrap_or(prim.any);
  let this_param = parsed
    .this_ty
    .map(|t| lower_type(store, t, env, stack, cache));
  let sig = Signature {
    params,
    ret,
    type_params: Vec::new(),
    this_param,
  };
  let sig_id = store.intern_signature(sig);
  store.intern_type(TypeKind::Callable {
    overloads: vec![sig_id],
  })
}

/// Build a constructable object type: `{ new (...params): instance }`.
pub fn constructable_type(store: &TypeStore, params: Vec<Param>, instance: TypeId) -> TypeId {
  let sig = Signature {
    params,
    ret: instance,
    type_params: Vec::new(),
    this_param: None,
  };
  let sig_id = store.intern_signature(sig);
  let mut shape = Shape::new();
  shape.construct_signatures.push(sig_id);
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj))
}

/// Infer a `@constructor` instance object type from `this.prop = …` assignments
/// in `body_source` (function body text including braces).
///
/// When the RHS is a parameter name present in `param_tys`, that param's type is
/// used; otherwise the property type is `any`.
pub fn infer_constructor_instance_type(
  store: &TypeStore,
  body_source: &str,
  param_tys: &HashMap<String, TypeId>,
) -> TypeId {
  let props = scan_this_property_assignments(body_source);
  if props.is_empty() {
    let shape = store.intern_shape(Shape::new());
    let obj = store.intern_object(ObjectType { shape });
    return store.intern_type(TypeKind::Object(obj));
  }
  let any = store.primitive_ids().any;
  let mut shape = Shape::new();
  let mut seen = HashSet::new();
  for (name, rhs) in props {
    if !seen.insert(name.clone()) {
      continue;
    }
    let ty = param_tys.get(&rhs).copied().unwrap_or(any);
    shape.properties.push(Property {
      key: PropKey::String(store.intern_name(name)),
      data: PropData {
        ty,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj))
}

/// Scan `this.<ident> = <ident>` assignments in source order.
fn scan_this_property_assignments(body: &str) -> Vec<(String, String)> {
  let bytes = body.as_bytes();
  let mut out = Vec::new();
  let mut i = 0usize;
  while i + 4 < bytes.len() {
    // Match `this.`
    if bytes[i] == b't'
      && bytes.get(i..i + 5) == Some(b"this.")
      && (i == 0 || !is_ident_continue(bytes[i - 1]))
    {
      let mut j = i + 5;
      let name_start = j;
      while j < bytes.len() && is_ident_continue(bytes[j]) {
        j += 1;
      }
      if j == name_start {
        i += 1;
        continue;
      }
      let prop = match std::str::from_utf8(&bytes[name_start..j]) {
        Ok(s) => s.to_owned(),
        Err(_) => {
          i = j;
          continue;
        }
      };
      while j < bytes.len() && is_js_ws(bytes[j]) {
        j += 1;
      }
      if j >= bytes.len() || bytes[j] != b'=' {
        i = j;
        continue;
      }
      // Skip `=>` and `==` / `===`.
      if bytes.get(j + 1) == Some(&b'=') || bytes.get(j + 1) == Some(&b'>') {
        i = j + 1;
        continue;
      }
      j += 1;
      while j < bytes.len() && is_js_ws(bytes[j]) {
        j += 1;
      }
      let rhs_start = j;
      if j < bytes.len() && is_ident_start(bytes[j]) {
        j += 1;
        while j < bytes.len() && is_ident_continue(bytes[j]) {
          j += 1;
        }
        if let Ok(rhs) = std::str::from_utf8(&bytes[rhs_start..j]) {
          out.push((prop, rhs.to_owned()));
        }
      }
      i = j;
      continue;
    }
    i += 1;
  }
  out
}

fn is_ident_start(b: u8) -> bool {
  b.is_ascii_alphabetic() || b == b'_' || b == b'$'
}

fn is_ident_continue(b: u8) -> bool {
  is_ident_start(b) || b.is_ascii_digit()
}

/// `T[]` only when `[]` is a postfix on a complete type (not inside unbalanced
/// constructs). `function(): number[]` and `{a: string}[]` are ok.
fn is_postfix_array(s: &str) -> bool {
  let trimmed = s.trim();
  if !trimmed.ends_with("[]") || trimmed.len() < 3 {
    return false;
  }
  let prefix = trimmed[..trimmed.len() - 2].trim();
  if prefix.is_empty() {
    return false;
  }
  // Do not treat `=>` function returns ending mid-parse; prefix must be balanced.
  balanced_type_prefix(prefix)
}

fn balanced_type_prefix(s: &str) -> bool {
  let mut depth_paren = 0i32;
  let mut depth_brace = 0i32;
  let mut depth_angle = 0i32;
  let mut in_str: Option<u8> = None;
  for &b in s.as_bytes() {
    if let Some(q) = in_str {
      if b == q {
        in_str = None;
      }
      continue;
    }
    match b {
      b'"' | b'\'' => in_str = Some(b),
      b'(' => depth_paren += 1,
      b')' => depth_paren -= 1,
      b'{' => depth_brace += 1,
      b'}' => depth_brace -= 1,
      b'<' => depth_angle += 1,
      b'>' => depth_angle -= 1,
      _ => {}
    }
    if depth_paren < 0 || depth_brace < 0 || depth_angle < 0 {
      return false;
    }
  }
  depth_paren == 0 && depth_brace == 0 && depth_angle == 0 && in_str.is_none()
}

fn balanced_braces(s: &str) -> bool {
  let bytes = s.as_bytes();
  if bytes.first() != Some(&b'{') || bytes.last() != Some(&b'}') {
    return false;
  }
  let mut depth = 0i32;
  let mut in_str: Option<u8> = None;
  for (i, &b) in bytes.iter().enumerate() {
    if let Some(q) = in_str {
      if b == q {
        in_str = None;
      }
      continue;
    }
    match b {
      b'"' | b'\'' => in_str = Some(b),
      b'{' => depth += 1,
      b'}' => {
        depth -= 1;
        if depth == 0 {
          return i + 1 == bytes.len();
        }
      }
      _ => {}
    }
  }
  false
}

fn take_paren_group(s: &str, start: usize) -> Option<(&str, usize)> {
  let bytes = s.as_bytes();
  if start >= bytes.len() || bytes[start] != b'(' {
    return None;
  }
  let mut depth = 0i32;
  let mut in_str: Option<u8> = None;
  let mut i = start;
  while i < bytes.len() {
    let b = bytes[i];
    if let Some(q) = in_str {
      if b == q {
        in_str = None;
      }
      i += 1;
      continue;
    }
    match b {
      b'"' | b'\'' => in_str = Some(b),
      b'(' => depth += 1,
      b')' => {
        depth -= 1;
        if depth == 0 {
          return Some((&s[start + 1..i], i + 1));
        }
      }
      _ => {}
    }
    i += 1;
  }
  None
}

fn find_top_level_arrow(s: &str) -> Option<usize> {
  let bytes = s.as_bytes();
  let mut depth_paren = 0i32;
  let mut depth_brace = 0i32;
  let mut depth_angle = 0i32;
  let mut in_str: Option<u8> = None;
  let mut i = 0;
  while i + 1 < bytes.len() {
    let b = bytes[i];
    if let Some(q) = in_str {
      if b == q {
        in_str = None;
      }
      i += 1;
      continue;
    }
    match b {
      b'"' | b'\'' => in_str = Some(b),
      b'(' => depth_paren += 1,
      b')' => depth_paren -= 1,
      b'{' => depth_brace += 1,
      b'}' => depth_brace -= 1,
      b'<' => depth_angle += 1,
      b'>' => depth_angle -= 1,
      b'=' if bytes[i + 1] == b'>' && depth_paren == 0 && depth_brace == 0 && depth_angle == 0 => {
        return Some(i);
      }
      _ => {}
    }
    i += 1;
  }
  None
}

fn split_top_level<'a>(s: &'a str, seps: &[u8]) -> Vec<&'a str> {
  let bytes = s.as_bytes();
  let mut depth_paren = 0i32;
  let mut depth_brace = 0i32;
  let mut depth_angle = 0i32;
  let mut in_str: Option<u8> = None;
  let mut parts = Vec::new();
  let mut start = 0;
  for (i, &b) in bytes.iter().enumerate() {
    if let Some(q) = in_str {
      if b == q {
        in_str = None;
      }
      continue;
    }
    match b {
      b'"' | b'\'' => in_str = Some(b),
      b'(' => depth_paren += 1,
      b')' => depth_paren -= 1,
      b'{' => depth_brace += 1,
      b'}' => depth_brace -= 1,
      b'<' => depth_angle += 1,
      b'>' => depth_angle -= 1,
      sep if seps.contains(&sep) && depth_paren == 0 && depth_brace == 0 && depth_angle == 0 => {
        let part = s[start..i].trim();
        if !part.is_empty() {
          parts.push(part);
        }
        start = i + 1;
      }
      _ => {}
    }
  }
  let last = s[start..].trim();
  if !last.is_empty() {
    parts.push(last);
  }
  parts
}

fn lower_typedef_name(
  store: &TypeStore,
  name: &str,
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  if let Some(cached) = cache.get(name) {
    return *cached;
  }
  if !stack.insert(name.to_owned()) {
    return store.primitive_ids().any;
  }
  let Some(typedefs) = env.typedefs else {
    stack.remove(name);
    return store.primitive_ids().any;
  };
  let Some(td) = typedefs.get(name) else {
    stack.remove(name);
    return store.primitive_ids().any;
  };
  let ty = lower_typedef(store, td, env, stack, cache);
  stack.remove(name);
  cache.insert(name.to_owned(), ty);
  ty
}

fn lower_typedef(
  store: &TypeStore,
  td: &OwnedJsdocTypedef,
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  let ty_str = td.ty.as_deref().map(str::trim).unwrap_or("");
  let objectish = ty_str.is_empty()
    || ty_str.eq_ignore_ascii_case("object")
    || ty_str == "*"
    || ty_str == "Object";
  if !td.properties.is_empty() && objectish {
    return lower_object_properties(store, &td.properties, env, stack, cache);
  }
  if !ty_str.is_empty() {
    return lower_type(store, ty_str, env, stack, cache);
  }
  // Nameless / empty typedef → empty object.
  let shape = store.intern_shape(Shape::new());
  let obj = store.intern_object(ObjectType { shape });
  store.intern_type(TypeKind::Object(obj))
}

fn lower_object_properties(
  store: &TypeStore,
  properties: &[OwnedJsdocProperty],
  env: &JsdocLowerEnv<'_>,
  stack: &mut HashSet<String>,
  cache: &mut HashMap<String, TypeId>,
) -> TypeId {
  let mut shape = Shape::new();
  for prop in properties {
    let ty = lower_type(store, &prop.ty, env, stack, cache);
    let key = PropKey::String(store.intern_name(prop.name.clone()));
    shape.properties.push(Property {
      key,
      data: PropData {
        ty,
        optional: prop.optional,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
  }
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj))
}

fn strip_block_comment_delimiters(comment: &str) -> &str {
  let bytes = comment.as_bytes();
  if bytes.len() >= 4 && bytes[0] == b'/' && bytes[1] == b'*' && bytes[bytes.len() - 2] == b'*' {
    // `/*…*/` — body is between.
    let start = if bytes.len() >= 5 && bytes[2] == b'*' {
      3
    } else {
      2
    };
    let end = bytes.len() - 2;
    &comment[start..end]
  } else {
    comment
  }
}

fn take_braced_type(body: &str, start: usize) -> Option<(&str, usize)> {
  let bytes = body.as_bytes();
  if start >= bytes.len() || bytes[start] != b'{' {
    return None;
  }
  let mut depth = 0i32;
  let mut i = start;
  while i < bytes.len() {
    match bytes[i] {
      b'{' => depth += 1,
      b'}' => {
        depth -= 1;
        if depth == 0 {
          let inner = body[start + 1..i].trim();
          return Some((inner, i + 1));
        }
      }
      _ => {}
    }
    i += 1;
  }
  None
}

/// Closure optional: `{string=}` → (`string`, true).
fn strip_closure_optional(ty: &str) -> (&str, bool) {
  let trimmed = ty.trim();
  if let Some(rest) = trimmed.strip_suffix('=') {
    (rest.trim(), true)
  } else {
    (trimmed, false)
  }
}

/// Parse `@param` name after the braced type: `name`, `name.prop`, `name[].prop`,
/// `[name]`, `[name.prop=default]`.
fn take_param_name(body: &str, start: usize) -> (Option<&str>, bool, usize) {
  let bytes = body.as_bytes();
  let mut i = start;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return (None, false, i);
  }
  if bytes[i] == b'[' {
    let mut j = i + 1;
    while j < bytes.len() && is_js_ws(bytes[j]) {
      j += 1;
    }
    let (name, after_name) = take_param_namepath(body, j);
    let mut k = after_name;
    while k < bytes.len() && is_js_ws(bytes[k]) {
      k += 1;
    }
    if k < bytes.len() && bytes[k] == b'=' {
      while k < bytes.len() && bytes[k] != b']' {
        k += 1;
      }
    }
    if k >= bytes.len() || bytes[k] != b']' {
      return (None, false, i);
    }
    return (name, true, k + 1);
  }
  // Markdown-quoted names: `arg` (accepted by tsc).
  if bytes[i] == b'`' {
    let (name, after_name) = take_param_namepath(body, i + 1);
    let mut k = after_name;
    while k < bytes.len() && is_js_ws(bytes[k]) {
      k += 1;
    }
    if k < bytes.len() && bytes[k] == b'`' {
      k += 1;
    }
    return (name, false, k);
  }
  let (name, after) = take_param_namepath(body, i);
  (name, false, after)
}

/// Identifier / dotted namepath with optional `[]` after each segment
/// (`opts`, `opts.x`, `opts[].x`, `opts[].what.bad[]`).
fn take_param_namepath(body: &str, start: usize) -> (Option<&str>, usize) {
  let bytes = body.as_bytes();
  let mut i = start;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return (None, i);
  }
  let name_start = i;
  if !(bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' || bytes[i] == b'$') {
    return (None, name_start);
  }
  i += 1;
  while i < bytes.len()
    && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'$')
  {
    i += 1;
  }
  if i + 1 < bytes.len() && bytes[i] == b'[' && bytes[i + 1] == b']' {
    i += 2;
  }
  while i < bytes.len() && bytes[i] == b'.' {
    let next = i + 1;
    if next >= bytes.len()
      || !(bytes[next].is_ascii_alphabetic() || bytes[next] == b'_' || bytes[next] == b'$')
    {
      break;
    }
    i = next + 1;
    while i < bytes.len()
      && (bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'$')
    {
      i += 1;
    }
    if i + 1 < bytes.len() && bytes[i] == b'[' && bytes[i + 1] == b']' {
      i += 2;
    }
  }
  (Some(&body[name_start..i]), i)
}

/// `@typedef {Type} Name` / `@typedef {Type}` (nameless) / `@typedef Name`.
///
/// Names may be dotted namepaths (`exports.Foo`, `exports.ns.Foo`).
fn take_typedef(body: &str, start: usize) -> (Option<JsdocTypedef<'_>>, usize) {
  let bytes = body.as_bytes();
  let mut i = start;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return (None, i);
  }
  if bytes[i] == b'{' {
    let Some((ty, after_ty)) = take_braced_type(body, i) else {
      return (None, i);
    };
    let (name, after_name) = take_namepath(body, after_ty);
    return (
      Some(JsdocTypedef {
        name: name.unwrap_or(""),
        ty: Some(ty),
        properties: Vec::new(),
      }),
      after_name,
    );
  }
  let (name, after_name) = take_namepath(body, i);
  let Some(name) = name else {
    return (None, i);
  };
  (
    Some(JsdocTypedef {
      name,
      ty: None,
      properties: Vec::new(),
    }),
    after_name,
  )
}

/// Parse an identifier or dotted namepath (`exports.Foo`).
fn take_namepath(body: &str, start: usize) -> (Option<&str>, usize) {
  let bytes = body.as_bytes();
  let mut i = start;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return (None, i);
  }
  let name_start = i;
  if !(bytes[i].is_ascii_alphabetic() || bytes[i] == b'_' || bytes[i] == b'$') {
    return (None, name_start);
  }
  i += 1;
  while i < bytes.len() {
    if bytes[i].is_ascii_alphanumeric() || bytes[i] == b'_' || bytes[i] == b'$' {
      i += 1;
      continue;
    }
    if bytes[i] == b'.' {
      let next = i + 1;
      if next < bytes.len()
        && (bytes[next].is_ascii_alphabetic() || bytes[next] == b'_' || bytes[next] == b'$')
      {
        i = next + 1;
        continue;
      }
    }
    break;
  }
  (Some(&body[name_start..i]), i)
}

/// `@property {T} name` / `@property name {T}` / optional `[name]` forms.
fn take_property(body: &str, start: usize) -> Option<(JsdocProperty<'_>, usize)> {
  let bytes = body.as_bytes();
  let mut i = start;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return None;
  }
  if bytes[i] == b'{' {
    let (ty, after_ty) = take_braced_type(body, i)?;
    let (ty, optional_from_ty) = strip_closure_optional(ty);
    let (name, optional_from_name, after_name) = take_param_name(body, after_ty);
    let name = name?;
    return Some((
      JsdocProperty {
        ty,
        name,
        optional: optional_from_ty || optional_from_name,
      },
      after_name,
    ));
  }
  // Alternate: `@property name {type}`
  let (name, optional_from_name, after_name) = take_param_name(body, i);
  let name = name?;
  let mut j = after_name;
  while j < bytes.len() && is_js_ws(bytes[j]) {
    j += 1;
  }
  let (ty, after_ty) = take_braced_type(body, j)?;
  let (ty, optional_from_ty) = strip_closure_optional(ty);
  Some((
    JsdocProperty {
      ty,
      name,
      optional: optional_from_ty || optional_from_name,
    },
    after_ty,
  ))
}

/// `@template T` / `@template T, U` / `@template {Constraint} T`.
fn take_templates(body: &str, start: usize) -> (Vec<JsdocTemplate<'_>>, usize) {
  let bytes = body.as_bytes();
  let mut i = start;
  while i < bytes.len() && is_js_ws(bytes[i]) {
    i += 1;
  }
  if i >= bytes.len() {
    return (Vec::new(), i);
  }
  let constraint = if bytes[i] == b'{' {
    match take_braced_type(body, i) {
      Some((ty, after)) => {
        i = after;
        while i < bytes.len() && is_js_ws(bytes[i]) {
          i += 1;
        }
        Some(ty)
      }
      None => None,
    }
  } else {
    None
  };

  let mut templates = Vec::new();
  loop {
    let (name, _, after) = take_param_name(body, i);
    let Some(name) = name else {
      break;
    };
    templates.push(JsdocTemplate { name, constraint });
    i = after;
    while i < bytes.len() && is_js_ws(bytes[i]) {
      i += 1;
    }
    if i < bytes.len() && bytes[i] == b',' {
      i += 1;
      while i < bytes.len() && is_js_ws(bytes[i]) {
        i += 1;
      }
      continue;
    }
    break;
  }
  (templates, i)
}

fn split_top_level_union(s: &str) -> Option<Vec<&str>> {
  let parts = split_top_level(s, &[b'|']);
  if parts.len() < 2 {
    None
  } else {
    Some(parts)
  }
}

fn strip_generic<'a>(s: &'a str, name: &str) -> Option<&'a str> {
  let trimmed = s.trim();
  if !trimmed.starts_with(name) {
    return None;
  }
  let rest = trimmed[name.len()..].trim_start();
  if !rest.starts_with('<') || !rest.ends_with('>') {
    return None;
  }
  // Single top-level type arg only for this slice.
  let inner = &rest[1..rest.len() - 1];
  if balanced_angles(&format!("<{inner}>")) {
    Some(inner.trim())
  } else {
    None
  }
}

fn balanced_parens(s: &str) -> bool {
  let bytes = s.as_bytes();
  if bytes.first() != Some(&b'(') || bytes.last() != Some(&b')') {
    return false;
  }
  let mut depth = 0i32;
  for (i, &b) in bytes.iter().enumerate() {
    match b {
      b'(' => depth += 1,
      b')' => {
        depth -= 1;
        if depth == 0 {
          return i + 1 == bytes.len();
        }
      }
      _ => {}
    }
  }
  false
}

fn balanced_angles(s: &str) -> bool {
  let mut depth = 0i32;
  for b in s.bytes() {
    match b {
      b'<' => depth += 1,
      b'>' => {
        depth -= 1;
        if depth < 0 {
          return false;
        }
      }
      _ => {}
    }
  }
  depth == 0
}

fn is_js_ws(b: u8) -> bool {
  matches!(b, b' ' | b'\t' | b'\n' | b'\r' | 0x0b | 0x0c)
}

#[cfg(test)]
mod tests {
  use super::*;
  use types_ts_interned::TypeStore;

  #[test]
  fn finds_leading_doc_comment() {
    let source = "/** @type {number} */\nvar x = 1;";
    let offset = source.find("var").unwrap() as u32;
    let comment = find_leading_block_comment(source, offset).unwrap();
    assert!(comment.starts_with("/**"));
    assert_eq!(parse_jsdoc_tags(comment).type_tag, Some("number"));
  }

  #[test]
  fn finds_same_line_doc_comment() {
    let source = "/** @type {number} */ var x = 1;";
    let offset = source.find("var").unwrap() as u32;
    assert_eq!(leading_type_tag(source, offset), Some("number"));
  }

  #[test]
  fn ignores_non_adjacent_comment() {
    let source = "/** @type {number} */\n\nfoo();\nvar x = 1;";
    let offset = source.find("var").unwrap() as u32;
    // `foo();` intervenes — not a leading comment for `var`.
    assert!(leading_type_tag(source, offset).is_none());
  }

  #[test]
  fn parses_returns_tag() {
    let comment = "/** @returns {string} */";
    assert_eq!(parse_jsdoc_tags(comment).returns, Some("string"));
  }

  #[test]
  fn parses_param_tags() {
    let comment = "/**\n * @param {number} x\n * @param {string} [y]\n * @param {boolean=} z\n * @returns {void}\n */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(tags.returns, Some("void"));
    assert_eq!(
      tags.params,
      vec![
        JsdocParam {
          ty: "number",
          name: Some("x"),
          optional: false,
        },
        JsdocParam {
          ty: "string",
          name: Some("y"),
          optional: true,
        },
        JsdocParam {
          ty: "boolean",
          name: Some("z"),
          optional: true,
        },
      ]
    );
    assert_eq!(tags.param_ty("x"), Some("number"));
  }

  #[test]
  fn parses_nested_param_names() {
    let comment = "/**\n * @param {object} opts\n * @param {string} opts.x\n * @param {number} [opts.y]\n * @param {boolean} opts2[].z\n */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(tags.params[0].name, Some("opts"));
    assert_eq!(tags.params[1].name, Some("opts.x"));
    assert_eq!(tags.params[2].name, Some("opts.y"));
    assert!(tags.params[2].optional);
    assert_eq!(tags.params[3].name, Some("opts2[].z"));
  }

  #[test]
  fn resolves_nested_param_object_shape() {
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new();
    let params = vec![
      OwnedJsdocParam {
        ty: "object".into(),
        name: Some("opts".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "string".into(),
        name: Some("opts.x".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "number".into(),
        name: Some("opts.y".into()),
        optional: true,
      },
    ];
    let (resolved, errors) = resolve_jsdoc_params(&store, &params, &env);
    assert!(errors.is_empty(), "expected no TS8032; got {errors:?}");
    let opts = resolved.get("opts").expect("opts");
    let TypeKind::Object(obj) = store.type_kind(opts.ty) else {
      panic!("expected object type, got {:?}", store.type_kind(opts.ty));
    };
    let shape = store.shape(store.object(obj).shape);
    assert_eq!(shape.properties.len(), 2);
    assert!(!shape.properties[0].data.optional);
    assert!(shape.properties[1].data.optional);
  }

  #[test]
  fn resolves_nested_param_without_parent_is_error() {
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new();
    let params = vec![OwnedJsdocParam {
      ty: "number".into(),
      name: Some("xyz.p".into()),
      optional: false,
    }];
    let (resolved, errors) = resolve_jsdoc_params(&store, &params, &env);
    assert!(resolved.is_empty());
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].qualified_name, "xyz.p");
    assert_eq!(errors[0].parent_path, "xyz");
  }

  #[test]
  fn unmatched_root_param_reports_ts8024_candidate() {
    let params = vec![
      OwnedJsdocParam {
        ty: "Object".into(),
        name: Some("notSpecial".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "string".into(),
        name: Some("unrelated".into()),
        optional: false,
      },
    ];
    let errors = find_unmatched_root_jsdoc_params(&params, &[Some("notSpecial")]);
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].name, "unrelated");
  }

  #[test]
  fn unmatched_root_suppressed_when_nested_absorbed() {
    // Like bad1: `@param {object} obj` + nested props + `@param {string} x`
    // against `function(x, {a,b})` — absorbed root suppresses TS8024.
    let params = vec![
      OwnedJsdocParam {
        ty: "object".into(),
        name: Some("obj".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "string".into(),
        name: Some("obj.a".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "string".into(),
        name: Some("obj.b".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "string".into(),
        name: Some("x".into()),
        optional: false,
      },
    ];
    let errors = find_unmatched_root_jsdoc_params(&params, &[Some("x"), None]);
    assert!(
      errors.is_empty(),
      "absorbed object root + excluded binding index should be silent; got {errors:?}"
    );
  }

  #[test]
  fn unmatched_root_binding_pattern_excludes_by_index() {
    let params = vec![
      OwnedJsdocParam {
        ty: "{a: string}".into(),
        name: Some("obj".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "string".into(),
        name: Some("x".into()),
        optional: false,
      },
    ];
    let errors = find_unmatched_root_jsdoc_params(&params, &[None, Some("x")]);
    assert!(
      errors.is_empty(),
      "index-0 binding pattern should exclude @param obj; got {errors:?}"
    );
  }

  #[test]
  fn resolves_deep_nested_param_requires_intermediate_object() {
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new();
    let params = vec![
      OwnedJsdocParam {
        ty: "object".into(),
        name: Some("xyz".into()),
        optional: false,
      },
      OwnedJsdocParam {
        ty: "number".into(),
        name: Some("xyz.bar.p".into()),
        optional: false,
      },
    ];
    let (resolved, errors) = resolve_jsdoc_params(&store, &params, &env);
    assert!(resolved.contains_key("xyz"));
    assert_eq!(errors.len(), 1);
    assert_eq!(errors[0].qualified_name, "xyz.bar.p");
    assert_eq!(errors[0].parent_path, "xyz.bar");
  }

  #[test]
  fn parses_typedef_with_properties() {
    let comment =
      "/**\n * @typedef {Object} Opts\n * @property {string} x\n * @property {number} [y]\n */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(tags.typedefs.len(), 1);
    assert_eq!(tags.typedefs[0].name, "Opts");
    assert_eq!(tags.typedefs[0].ty, Some("Object"));
    assert_eq!(
      tags.typedefs[0].properties,
      vec![
        JsdocProperty {
          ty: "string",
          name: "x",
          optional: false,
        },
        JsdocProperty {
          ty: "number",
          name: "y",
          optional: true,
        },
      ]
    );
  }

  #[test]
  fn parses_typedef_name_only_with_type_tag() {
    let comment = "/**\n * @typedef LoadCallback\n * @type {string}\n */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(tags.typedefs.len(), 1);
    assert_eq!(tags.typedefs[0].name, "LoadCallback");
    assert_eq!(tags.typedefs[0].ty, Some("string"));
  }

  #[test]
  fn parses_templates() {
    let comment = "/**\n * @template T\n * @template {string} U\n * @param {T} x\n */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(
      tags.templates,
      vec![
        JsdocTemplate {
          name: "T",
          constraint: None,
        },
        JsdocTemplate {
          name: "U",
          constraint: Some("string"),
        },
      ]
    );
  }

  #[test]
  fn collect_file_typedefs_resolves_alias() {
    let source = "/**\n * @typedef {number} Num\n */\n/** @type {Num} */\nvar x = 1;\n";
    let map = collect_file_typedefs(source);
    assert!(map.contains_key("Num"));
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new().with_typedefs(Some(&map));
    let ty = lower_jsdoc_type_with(&store, "Num", &env);
    assert_eq!(ty, store.primitive_ids().number);
  }

  #[test]
  fn parses_typedef_qualified_name() {
    let comment = "/** @typedef {string} exports.Foo */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(tags.typedefs.len(), 1);
    assert_eq!(tags.typedefs[0].name, "exports.Foo");
    assert_eq!(tags.typedefs[0].ty, Some("string"));
  }

  #[test]
  fn parses_nameless_typedef() {
    let comment = "/** @typedef {string} */";
    let tags = parse_jsdoc_tags(comment);
    assert_eq!(tags.typedefs.len(), 1);
    assert_eq!(tags.typedefs[0].name, "");
    assert_eq!(tags.typedefs[0].ty, Some("string"));
  }

  #[test]
  fn collect_qualified_typedef_resolves_exports_path() {
    let source =
      "/** @typedef {string} exports.Foo */\n/** @type {exports.Foo} */\nvar x = 'ok';\n";
    let map = collect_file_typedefs(source);
    assert!(map.contains_key("exports.Foo"));
    assert!(!map.contains_key("Foo"));
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new().with_typedefs(Some(&map));
    let ty = lower_jsdoc_type_with(&store, "exports.Foo", &env);
    assert_eq!(ty, store.primitive_ids().string);
    assert!(unresolved_jsdoc_qualified_name("exports.Foo", &env).is_none());
  }

  #[test]
  fn collect_nameless_typedef_on_exports_assign() {
    let source = "/** @typedef {number} */\nexports.Bar = {};\n";
    let map = collect_file_typedefs(source);
    assert!(map.contains_key("Bar"));
    assert!(map.contains_key("exports.Bar"));
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new().with_typedefs(Some(&map));
    assert_eq!(
      lower_jsdoc_type_with(&store, "exports.Bar", &env),
      store.primitive_ids().number
    );
    assert_eq!(
      lower_jsdoc_type_with(&store, "Bar", &env),
      store.primitive_ids().number
    );
  }

  #[test]
  fn nameless_typedef_on_bare_exports_not_registered() {
    let source = "/** @typedef {string} */\nexports.SomeName;\n";
    let map = collect_file_typedefs(source);
    assert!(!map.contains_key("SomeName"));
    assert!(!map.contains_key("exports.SomeName"));
    let env = JsdocLowerEnv::new().with_typedefs(Some(&map));
    assert_eq!(
      unresolved_jsdoc_qualified_name("exports.SomeName", &env),
      Some("exports.SomeName")
    );
  }

  #[test]
  fn lowers_typedef_object_properties() {
    let source = "/**\n * @typedef {Object} Opts\n * @property {string} x\n */\n";
    let map = collect_file_typedefs(source);
    let store = TypeStore::new();
    let env = JsdocLowerEnv::new().with_typedefs(Some(&map));
    let ty = lower_jsdoc_type_with(&store, "Opts", &env);
    assert!(matches!(store.type_kind(ty), TypeKind::Object(_)));
  }

  #[test]
  fn lowers_primitives_unions_arrays() {
    let store = TypeStore::new();
    let number = lower_jsdoc_type(&store, "number", None);
    assert_eq!(number, store.primitive_ids().number);

    let union = lower_jsdoc_type(&store, "string|number", None);
    assert!(matches!(store.type_kind(union), TypeKind::Union(_)));

    let arr = lower_jsdoc_type(&store, "number[]", None);
    assert!(matches!(
      store.type_kind(arr),
      TypeKind::Array {
        readonly: false,
        ..
      }
    ));

    let arr2 = lower_jsdoc_type(&store, "Array<string>", None);
    assert!(matches!(store.type_kind(arr2), TypeKind::Array { .. }));
  }

  #[test]
  fn lowers_inline_object_type() {
    let store = TypeStore::new();
    let ty = lower_jsdoc_type(&store, "{ a: string, b?: number }", None);
    assert!(matches!(store.type_kind(ty), TypeKind::Object(_)));
    let obj = match store.type_kind(ty) {
      TypeKind::Object(id) => store.object(id),
      _ => unreachable!(),
    };
    let shape = store.shape(obj.shape);
    assert_eq!(shape.properties.len(), 2);
    assert!(!shape.properties[0].data.optional);
    assert!(shape.properties[1].data.optional);
  }

  #[test]
  fn lowers_closure_and_ts_function_types() {
    let store = TypeStore::new();
    let closure = lower_jsdoc_type(&store, "function(string): number", None);
    assert!(matches!(
      store.type_kind(closure),
      TypeKind::Callable { .. }
    ));
    let sig = match store.type_kind(closure) {
      TypeKind::Callable { overloads } => store.signature(overloads[0]),
      _ => unreachable!(),
    };
    assert_eq!(sig.params.len(), 1);
    assert_eq!(sig.params[0].ty, store.primitive_ids().string);
    assert_eq!(sig.ret, store.primitive_ids().number);

    let arrow = lower_jsdoc_type(&store, "(s: string) => void", None);
    assert!(matches!(store.type_kind(arrow), TypeKind::Callable { .. }));
    let sig = match store.type_kind(arrow) {
      TypeKind::Callable { overloads } => store.signature(overloads[0]),
      _ => unreachable!(),
    };
    assert_eq!(sig.params.len(), 1);
    assert_eq!(sig.params[0].ty, store.primitive_ids().string);
    assert_eq!(sig.ret, store.primitive_ids().void);
  }

  #[test]
  fn lowers_function_with_rest_and_literals() {
    let store = TypeStore::new();
    let ty = lower_jsdoc_type(&store, "function(boolean, string, ...*): void", None);
    let sig = match store.type_kind(ty) {
      TypeKind::Callable { overloads } => store.signature(overloads[0]),
      other => panic!("expected callable, got {other:?}"),
    };
    assert_eq!(sig.params.len(), 3);
    assert!(sig.params[2].rest);

    let lit = lower_jsdoc_type(&store, r#""a" | "b""#, None);
    assert!(matches!(store.type_kind(lit), TypeKind::Union(_)));
  }

  #[test]
  fn lowers_function_with_string_number_literal_unions() {
    let store = TypeStore::new();
    let ty = lower_jsdoc_type(&store, r#"function ("a" | "b", 1 | 2): 3 | 4"#, None);
    let sig = match store.type_kind(ty) {
      TypeKind::Callable { overloads } => store.signature(overloads[0]),
      other => panic!("expected callable, got {other:?}"),
    };
    assert_eq!(sig.params.len(), 2);
    assert!(matches!(
      store.type_kind(sig.params[0].ty),
      TypeKind::Union(_)
    ));
    assert!(matches!(
      store.type_kind(sig.params[1].ty),
      TypeKind::Union(_)
    ));
    assert!(matches!(store.type_kind(sig.ret), TypeKind::Union(_)));
  }

  #[test]
  fn finds_returns_before_function_decl() {
    let source = "/**\n * @returns {number}\n */\nfunction f() {\n  return \"no\";\n}\n";
    let offset = source.find("function").unwrap() as u32;
    let tags = leading_jsdoc_tags(source, offset).unwrap();
    assert_eq!(tags.returns, Some("number"));
  }

  #[test]
  fn finds_class_and_constructor_jsdoc_templates_and_params() {
    let source = r#"
/** @template T */
class Foo {
  /** @param {T} x */
  constructor(x) {
    this.a = x;
  }
}
"#;
    let class_tags = class_leading_jsdoc_tags(source, "Foo").expect("class jsdoc");
    assert_eq!(class_tags.templates.len(), 1);
    assert_eq!(class_tags.templates[0].name, "T");
    let ctor_tags = constructor_leading_jsdoc_tags(source, "Foo").expect("ctor jsdoc");
    assert_eq!(ctor_tags.param_ty("x"), Some("T"));
  }
}
