//! JSX element / props / children typing.
//!
//! Prefers `hir_js::JsxElement` (tag name, attributes, children) via the body
//! expr map. Nested JSX children are HIR `ExprId`s (AstIndex does not index
//! nested `JsxElem` nodes as expressions). Residual AST `JsxElem` walk when
//! HIR is missing; nested expression values still resolve AST nodes by span
//! for `check_expr` / excess-property reporting. No AST `TypeLowerer` /
//! `TypeExpr` lowering here.

use std::collections::HashSet;
use std::sync::Arc;

use diagnostics::{Span, TextRange};
use hir_js::{
  ExprId, ExprKind, JsxAttr as HirJsxAttr, JsxAttrValue, JsxChild, JsxElement, JsxElementName,
};
use parse_js::ast::expr::jsx::{JsxAttr, JsxAttrVal, JsxElem, JsxElemChild, JsxElemName, JsxText};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::node::Node;
use parse_js::loc::Loc;
use types_ts_interned::{
  NameId as TsNameId, ObjectType, PropData, PropKey, Shape, SignatureId, TypeDisplay, TypeId,
  TypeKind,
};

use super::super::super::infer::infer_type_arguments_for_call;
use super::super::super::instantiate::Substituter;
use super::super::super::overload::CallArgType;
use crate::{codes, DefId};

use super::super::{is_empty_jsx_expr_placeholder, loc_to_range, Checker, JsxActualProps};

impl<'a> Checker<'a> {
  pub(crate) fn check_jsx_elem(&mut self, elem: &Node<JsxElem>) -> TypeId {
    let range = loc_to_range(self.file, elem.loc);
    if let Some(hir) = self.hir_jsx_element_at(range).cloned() {
      return self.check_jsx_from_hir(elem.loc, &hir);
    }
    // Residual: no HIR `ExprKind::Jsx` at this span.
    self.check_jsx_elem_ast(elem)
  }

  /// Drive element/tag/attribute/children typing from HIR structure.
  pub(crate) fn check_jsx_from_hir(&mut self, elem_loc: Loc, elem: &JsxElement) -> TypeId {
    let prim = self.store.primitive_ids();
    if self.jsx_mode.is_none() {
      self.diagnostics.push(codes::JSX_DISABLED.error(
        "jsx is disabled",
        Span::new(self.file, loc_to_range(self.file, elem_loc)),
      ));
      self.record_expr_type(elem_loc, prim.unknown);
      return prim.unknown;
    }

    let element_ty = self.jsx_element_type(elem_loc);
    let tag_loc = elem_loc;

    match &elem.name {
      None => {
        let _ = self.jsx_actual_props_hir(elem_loc, &elem.attributes, &elem.children, None);
      }
      Some(JsxElementName::Name(name)) => {
        let tag_buf = name
          .namespace
          .as_ref()
          .map(|ns| format!("{ns}:{}", name.name));
        let tag = tag_buf.as_deref().unwrap_or_else(|| name.name.as_str());
        self.check_jsx_intrinsic_name_hir(tag, elem_loc, tag_loc, &elem.attributes, &elem.children);
      }
      Some(JsxElementName::Ident(name_id)) => {
        let Some(name) = self.names.resolve(*name_id) else {
          let _ = self.jsx_actual_props_hir(elem_loc, &elem.attributes, &elem.children, None);
          self.record_expr_type(elem_loc, element_ty);
          return element_ty;
        };
        let name = name.to_string();
        if name.contains(':') || name.contains('-') {
          self.check_jsx_intrinsic_name_hir(
            &name,
            elem_loc,
            tag_loc,
            &elem.attributes,
            &elem.children,
          );
        } else {
          let component_ty = self
            .lookup(&name)
            .map(|binding| binding.ty)
            .unwrap_or_else(|| {
              self.diagnostics.push(codes::CANNOT_FIND_NAME.error(
                codes::cannot_find_name_message(&name),
                Span::new(self.file, loc_to_range(self.file, tag_loc)),
              ));
              prim.unknown
            });
          let expected_props_ty = self
            .jsx_expected_props_for_value_tag(component_ty, elem_loc)
            .map(|expected| self.jsx_apply_intrinsic_attributes(expected));
          let actual_props = self.jsx_actual_props_hir(
            elem_loc,
            &elem.attributes,
            &elem.children,
            expected_props_ty,
          );
          self.check_jsx_value_tag(component_ty, &actual_props, element_ty, elem_loc, tag_loc);
        }
      }
      Some(JsxElementName::Member(member)) => {
        let Some(base_name) = self.names.resolve(member.base) else {
          let _ = self.jsx_actual_props_hir(elem_loc, &elem.attributes, &elem.children, None);
          self.record_expr_type(elem_loc, element_ty);
          return element_ty;
        };
        let base_name = base_name.to_string();
        if base_name.contains(':') || base_name.contains('-') {
          let mut tag = base_name;
          for segment_id in member.path.iter() {
            let Some(segment) = self.names.resolve(*segment_id) else {
              continue;
            };
            tag.push('.');
            tag.push_str(segment);
          }
          self.check_jsx_intrinsic_name_hir(
            &tag,
            elem_loc,
            tag_loc,
            &elem.attributes,
            &elem.children,
          );
        } else {
          let mut current = self
            .lookup(&base_name)
            .map(|binding| binding.ty)
            .unwrap_or_else(|| {
              self.diagnostics.push(codes::CANNOT_FIND_NAME.error(
                codes::cannot_find_name_message(&base_name),
                Span::new(self.file, loc_to_range(self.file, tag_loc)),
              ));
              prim.unknown
            });
          for segment_id in member.path.iter() {
            let Some(segment) = self.names.resolve(*segment_id) else {
              continue;
            };
            current = self.member_type(current, segment);
          }
          let expected_props_ty = self
            .jsx_expected_props_for_value_tag(current, elem_loc)
            .map(|expected| self.jsx_apply_intrinsic_attributes(expected));
          let actual_props = self.jsx_actual_props_hir(
            elem_loc,
            &elem.attributes,
            &elem.children,
            expected_props_ty,
          );
          self.check_jsx_value_tag(current, &actual_props, element_ty, elem_loc, tag_loc);
        }
      }
    }
    self.record_expr_type(elem_loc, element_ty);
    element_ty
  }

  fn check_jsx_intrinsic_name_hir(
    &mut self,
    tag: &str,
    elem_loc: Loc,
    tag_loc: Loc,
    attrs: &[HirJsxAttr],
    children: &[JsxChild],
  ) {
    let prim = self.store.primitive_ids();
    let intrinsic_elements = self.jsx_intrinsic_elements_type(elem_loc);
    let expected_props_ty = if intrinsic_elements != prim.unknown {
      self.member_type(intrinsic_elements, tag)
    } else {
      prim.unknown
    };
    if expected_props_ty == prim.unknown {
      let _ = self.jsx_actual_props_hir(elem_loc, attrs, children, None);
      if intrinsic_elements != prim.unknown {
        self
          .diagnostics
          .push(codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.error(
            format!("unknown JSX intrinsic element `{tag}`"),
            Span::new(self.file, loc_to_range(self.file, tag_loc)),
          ));
      }
    } else {
      let expected_props_ty = self.jsx_apply_intrinsic_attributes(expected_props_ty);
      let actual_props =
        self.jsx_actual_props_hir(elem_loc, attrs, children, Some(expected_props_ty));
      self.check_jsx_props(elem_loc, &actual_props, expected_props_ty);
    }
  }

  /// Residual AST `JsxElem` walk when HIR JSX is unavailable.
  fn check_jsx_elem_ast(&mut self, elem: &Node<JsxElem>) -> TypeId {
    let prim = self.store.primitive_ids();
    if self.jsx_mode.is_none() {
      self.diagnostics.push(codes::JSX_DISABLED.error(
        "jsx is disabled",
        Span::new(self.file, loc_to_range(self.file, elem.loc)),
      ));
      self.record_expr_type(elem.loc, prim.unknown);
      return prim.unknown;
    }

    let element_ty = self.jsx_element_type(elem.loc);

    match &elem.stx.name {
      None => {
        // Fragment; no attributes, but still typecheck children.
        let _ = self.jsx_actual_props(elem.loc, &elem.stx.attributes, &elem.stx.children, None);
      }
      Some(JsxElemName::Name(name)) => {
        let tag_buf = name
          .stx
          .namespace
          .as_ref()
          .map(|ns| format!("{ns}:{}", name.stx.name));
        let tag = tag_buf.as_deref().unwrap_or_else(|| name.stx.name.as_str());
        let intrinsic_elements = self.jsx_intrinsic_elements_type(elem.loc);
        let expected_props_ty = if intrinsic_elements != prim.unknown {
          self.member_type(intrinsic_elements, tag)
        } else {
          prim.unknown
        };
        if expected_props_ty == prim.unknown {
          let _ = self.jsx_actual_props(elem.loc, &elem.stx.attributes, &elem.stx.children, None);
          if intrinsic_elements != prim.unknown {
            self
              .diagnostics
              .push(codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.error(
                format!("unknown JSX intrinsic element `{tag}`"),
                Span::new(self.file, loc_to_range(self.file, name.loc)),
              ));
          }
        } else {
          let expected_props_ty = self.jsx_apply_intrinsic_attributes(expected_props_ty);
          let actual_props = self.jsx_actual_props(
            elem.loc,
            &elem.stx.attributes,
            &elem.stx.children,
            Some(expected_props_ty),
          );
          self.check_jsx_props(elem.loc, &actual_props, expected_props_ty);
        }
      }
      Some(JsxElemName::Id(id)) => {
        let name = id.stx.name.as_str();
        if name.contains(':') || name.contains('-') {
          let intrinsic_elements = self.jsx_intrinsic_elements_type(elem.loc);
          let expected_props_ty = if intrinsic_elements != prim.unknown {
            self.member_type(intrinsic_elements, name)
          } else {
            prim.unknown
          };
          if expected_props_ty == prim.unknown {
            let _ = self.jsx_actual_props(elem.loc, &elem.stx.attributes, &elem.stx.children, None);
            if intrinsic_elements != prim.unknown {
              self
                .diagnostics
                .push(codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.error(
                  format!("unknown JSX intrinsic element `{name}`"),
                  Span::new(self.file, loc_to_range(self.file, id.loc)),
                ));
            }
          } else {
            let expected_props_ty = self.jsx_apply_intrinsic_attributes(expected_props_ty);
            let actual_props = self.jsx_actual_props(
              elem.loc,
              &elem.stx.attributes,
              &elem.stx.children,
              Some(expected_props_ty),
            );
            self.check_jsx_props(elem.loc, &actual_props, expected_props_ty);
          }
        } else {
          let component_ty = self
            .lookup(name)
            .map(|binding| binding.ty)
            .unwrap_or_else(|| {
              self.diagnostics.push(codes::CANNOT_FIND_NAME.error(
                codes::cannot_find_name_message(name),
                Span::new(self.file, loc_to_range(self.file, id.loc)),
              ));
              prim.unknown
            });
          let expected_props_ty = self
            .jsx_expected_props_for_value_tag(component_ty, elem.loc)
            .map(|expected| self.jsx_apply_intrinsic_attributes(expected));
          let actual_props = self.jsx_actual_props(
            elem.loc,
            &elem.stx.attributes,
            &elem.stx.children,
            expected_props_ty,
          );
          self.check_jsx_value_tag(component_ty, &actual_props, element_ty, elem.loc, id.loc);
        }
      }
      Some(JsxElemName::Member(member)) => {
        let base_name = member.stx.base.stx.name.as_str();
        if base_name.contains(':') || base_name.contains('-') {
          let mut tag = base_name.to_string();
          for segment in member.stx.path.iter() {
            tag.push('.');
            tag.push_str(segment);
          }
          let intrinsic_elements = self.jsx_intrinsic_elements_type(elem.loc);
          let expected_props_ty = if intrinsic_elements != prim.unknown {
            self.member_type(intrinsic_elements, &tag)
          } else {
            prim.unknown
          };
          if expected_props_ty == prim.unknown {
            let _ = self.jsx_actual_props(elem.loc, &elem.stx.attributes, &elem.stx.children, None);
            if intrinsic_elements != prim.unknown {
              self
                .diagnostics
                .push(codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.error(
                  format!("unknown JSX intrinsic element `{tag}`"),
                  Span::new(self.file, loc_to_range(self.file, member.loc)),
                ));
            }
          } else {
            let expected_props_ty = self.jsx_apply_intrinsic_attributes(expected_props_ty);
            let actual_props = self.jsx_actual_props(
              elem.loc,
              &elem.stx.attributes,
              &elem.stx.children,
              Some(expected_props_ty),
            );
            self.check_jsx_props(elem.loc, &actual_props, expected_props_ty);
          }
        } else {
          // Member expressions like `<Foo.Bar />` are treated like looking up
          // `Foo` and then checking `.Bar` as a value.
          let mut current = self
            .lookup(base_name)
            .map(|binding| binding.ty)
            .unwrap_or_else(|| {
              self.diagnostics.push(codes::CANNOT_FIND_NAME.error(
                codes::cannot_find_name_message(base_name),
                Span::new(self.file, loc_to_range(self.file, member.stx.base.loc)),
              ));
              prim.unknown
            });
          for segment in member.stx.path.iter() {
            current = self.member_type(current, segment);
          }
          let expected_props_ty = self
            .jsx_expected_props_for_value_tag(current, elem.loc)
            .map(|expected| self.jsx_apply_intrinsic_attributes(expected));
          let actual_props = self.jsx_actual_props(
            elem.loc,
            &elem.stx.attributes,
            &elem.stx.children,
            expected_props_ty,
          );
          self.check_jsx_value_tag(current, &actual_props, element_ty, elem.loc, member.loc);
        }
      }
    }
    self.record_expr_type(elem.loc, element_ty);
    element_ty
  }

  pub(crate) fn check_jsx_value_tag(
    &mut self,
    tag_ty: TypeId,
    actual_props: &JsxActualProps,
    element_ty: TypeId,
    elem_loc: Loc,
    tag_loc: Loc,
  ) {
    let prim = self.store.primitive_ids();
    if matches!(
      self.store.type_kind(tag_ty),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return;
    }

    let expanded = self.expand_for_props(tag_ty);
    if expanded != tag_ty {
      self.check_jsx_value_tag(expanded, actual_props, element_ty, elem_loc, tag_loc);
      return;
    }

    match self.store.type_kind(tag_ty) {
      TypeKind::Union(members) => {
        for member in members {
          let before = self.diagnostics.len();
          self.check_jsx_value_tag(member, actual_props, element_ty, elem_loc, tag_loc);
          if self.diagnostics.len() > before {
            return;
          }
        }
      }
      TypeKind::StringLiteral(name_id) => {
        let tag = self.store.name(name_id);
        self.check_jsx_intrinsic_tag(tag.as_str(), actual_props, elem_loc, tag_loc);
      }
      TypeKind::String => {
        // Dynamic intrinsic tag; allow it only when `JSX.IntrinsicElements` provides a string
        // index signature.
        let intrinsic_elements = self.jsx_intrinsic_elements_type(elem_loc);
        if intrinsic_elements == prim.unknown {
          return;
        }
        let expected_props_ty =
          self.member_type_for_index_key(intrinsic_elements, prim.string, /*writing*/ false);
        if expected_props_ty == prim.unknown {
          self.diagnostics.push(codes::NO_OVERLOAD.error(
            "JSX tag type `string` is not assignable to JSX.IntrinsicElements",
            Span::new(self.file, loc_to_range(self.file, tag_loc)),
          ));
          return;
        }
        let expected_props_ty = self.jsx_apply_intrinsic_attributes(expected_props_ty);
        self.check_jsx_props(elem_loc, actual_props, expected_props_ty);
      }
      _ => {
        self.check_jsx_component(tag_ty, actual_props, element_ty, elem_loc);
      }
    }
  }

  pub(crate) fn jsx_expected_props_for_value_tag(
    &mut self,
    tag_ty: TypeId,
    elem_loc: Loc,
  ) -> Option<TypeId> {
    let prim = self.store.primitive_ids();
    if matches!(
      self.store.type_kind(tag_ty),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return None;
    }

    let expanded = self.expand_for_props(tag_ty);
    if expanded != tag_ty {
      return self.jsx_expected_props_for_value_tag(expanded, elem_loc);
    }

    match self.store.type_kind(tag_ty) {
      TypeKind::Union(members) => {
        let mut collected = Vec::new();
        for member in members {
          let props_ty = self.jsx_expected_props_for_value_tag(member, elem_loc)?;
          collected.push(props_ty);
        }
        if collected.is_empty() {
          None
        } else {
          Some(self.store.intersection(collected))
        }
      }
      TypeKind::StringLiteral(name_id) => {
        let intrinsic_elements = self.jsx_intrinsic_elements_type(elem_loc);
        if intrinsic_elements == prim.unknown {
          return None;
        }
        let tag = self.store.name(name_id);
        let expected_props_ty = self.member_type(intrinsic_elements, tag.as_str());
        (expected_props_ty != prim.unknown).then_some(expected_props_ty)
      }
      TypeKind::String => {
        let intrinsic_elements = self.jsx_intrinsic_elements_type(elem_loc);
        if intrinsic_elements == prim.unknown {
          return None;
        }
        let expected_props_ty =
          self.member_type_for_index_key(intrinsic_elements, prim.string, /*writing*/ false);
        (expected_props_ty != prim.unknown).then_some(expected_props_ty)
      }
      _ => {
        let call_sigs = self.jsx_component_call_signatures(tag_ty);
        let is_construct = call_sigs.is_empty();
        let sigs = if !is_construct {
          call_sigs
        } else {
          self.jsx_component_construct_signatures(tag_ty)
        };
        if sigs.is_empty() {
          return None;
        }
        let empty_props = {
          let shape_id = self.store.intern_shape(Shape::new());
          let obj = self.store.intern_object(ObjectType { shape: shape_id });
          self.store.intern_type(TypeKind::Object(obj))
        };
        let mut props = Vec::new();
        for sig_id in sigs {
          let sig = self.store.signature(sig_id);
          let mut props_ty = sig.params.first().map(|p| p.ty).unwrap_or(empty_props);
          let ret_ty = sig.ret;

          if is_construct {
            if let Some(attrs_prop) = self.jsx_element_attributes_prop_key() {
              let prop_name = self.store.name(attrs_prop);
              if self.type_has_prop(ret_ty, &prop_name) {
                props_ty = self.member_type(ret_ty, &prop_name);
              }
            }
          }

          props_ty = self.jsx_apply_library_managed_attributes(tag_ty, props_ty);
          if is_construct {
            let class_attrs = self.jsx_intrinsic_class_attributes_type(ret_ty);
            if !matches!(self.store.type_kind(class_attrs), TypeKind::EmptyObject) {
              props_ty = self.store.intersection(vec![props_ty, class_attrs]);
            }
          }
          props.push(props_ty);
        }
        props.sort();
        props.dedup();
        let expected_props = if props.len() == 1 {
          props[0]
        } else {
          self.store.union(props)
        };
        (expected_props != prim.unknown).then_some(expected_props)
      }
    }
  }

  pub(crate) fn check_jsx_intrinsic_tag(
    &mut self,
    tag: &str,
    actual_props: &JsxActualProps,
    elem_loc: Loc,
    tag_loc: Loc,
  ) {
    let prim = self.store.primitive_ids();
    let intrinsic_elements = self.jsx_intrinsic_elements_type(elem_loc);
    if intrinsic_elements == prim.unknown {
      return;
    }
    let expected_props_ty = self.member_type(intrinsic_elements, tag);
    if expected_props_ty == prim.unknown {
      self
        .diagnostics
        .push(codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.error(
          format!("unknown JSX intrinsic element `{tag}`"),
          Span::new(self.file, loc_to_range(self.file, tag_loc)),
        ));
      return;
    }
    let expected_props_ty = self.jsx_apply_intrinsic_attributes(expected_props_ty);
    self.check_jsx_props(elem_loc, actual_props, expected_props_ty);
  }

  fn span_to_loc(span: TextRange) -> Loc {
    Loc(span.start as usize, span.end as usize)
  }

  /// Check a HIR expression by span → AstIndex residual, or recurse HIR JSX.
  fn check_hir_expr_id_with_expected(&mut self, expr_id: ExprId, expected: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let Some(expr_data) = self.body.exprs.get(expr_id.0 as usize) else {
      return prim.unknown;
    };
    let span = expr_data.span;
    let jsx = match &expr_data.kind {
      ExprKind::Jsx(elem) => Some(elem.clone()),
      _ => None,
    };
    if let Some(hir) = jsx {
      return self.check_jsx_from_hir(Self::span_to_loc(span), &hir);
    }
    if let Some(ast) = self.index.exprs.get(&span).copied() {
      self.check_expr_with_expected(ast, expected)
    } else {
      prim.unknown
    }
  }

  fn check_hir_jsx_expr_id(&mut self, expr_id: ExprId) -> TypeId {
    let prim = self.store.primitive_ids();
    let Some(expr_data) = self.body.exprs.get(expr_id.0 as usize) else {
      return prim.unknown;
    };
    let span = expr_data.span;
    let jsx = match &expr_data.kind {
      ExprKind::Jsx(elem) => Some(elem.clone()),
      _ => None,
    };
    if let Some(hir) = jsx {
      return self.check_jsx_from_hir(Self::span_to_loc(span), &hir);
    }
    if let Some(ast) = self.index.exprs.get(&span).copied() {
      if let AstExpr::JsxElem(elem) = ast.stx.as_ref() {
        return self.check_jsx_elem_ast(elem);
      }
      return self.check_expr(ast);
    }
    prim.unknown
  }

  pub(crate) fn jsx_actual_props_hir(
    &mut self,
    loc: Loc,
    attrs: &[HirJsxAttr],
    children: &[JsxChild],
    expected: Option<TypeId>,
  ) -> JsxActualProps {
    let prim = self.store.primitive_ids();
    let mut props = HashSet::new();
    let mut shape = Shape::new();
    let mut spreads = Vec::new();
    let mut has_spread = false;
    for attr in attrs {
      match attr {
        HirJsxAttr::Named { name, value } => {
          let key_string = if let Some(namespace) = name.namespace.as_ref() {
            format!("{namespace}:{}", name.name)
          } else {
            name.name.clone()
          };
          props.insert(key_string.clone());
          let key = PropKey::String(self.store.intern_name(key_string.clone()));
          let value_ty = match value {
            None => self.store.intern_type(TypeKind::BooleanLiteral(true)),
            Some(JsxAttrValue::Text(text)) => self.jsx_attr_text_type_str(text),
            Some(JsxAttrValue::Expression(container)) => match container.expr {
              // Empty JSX expression container (`{}`) — HIR omits the expr.
              None => prim.unknown,
              Some(expr_id) => {
                let expected_ty = expected
                  .filter(|ty| {
                    !matches!(self.store.type_kind(*ty), TypeKind::Any | TypeKind::Unknown)
                  })
                  .map(|props_ty| self.member_type(props_ty, &key_string))
                  .unwrap_or(prim.unknown);
                let value_ty = self.check_hir_expr_id_with_expected(expr_id, expected_ty);
                if expected_ty != prim.unknown
                  && !matches!(
                    self.store.type_kind(expected_ty),
                    TypeKind::Any | TypeKind::Unknown
                  )
                {
                  if let Some(ast) = self
                    .body
                    .exprs
                    .get(expr_id.0 as usize)
                    .and_then(|e| self.index.exprs.get(&e.span).copied())
                  {
                    if let AstExpr::LitObj(obj) = ast.stx.as_ref() {
                      let _ = self.report_excess_property(obj, expected_ty);
                    }
                  }
                }
                value_ty
              }
            },
            Some(JsxAttrValue::Element(expr_id)) => self.check_hir_jsx_expr_id(*expr_id),
          };
          shape.properties.push(types_ts_interned::Property {
            key,
            data: PropData {
              ty: value_ty,
              optional: false,
              readonly: false,
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
        HirJsxAttr::Spread { expr } => {
          has_spread = true;
          let expected_ty = expected
            .filter(|ty| !matches!(self.store.type_kind(*ty), TypeKind::Any | TypeKind::Unknown))
            .unwrap_or(prim.unknown);
          spreads.push(self.check_hir_expr_id_with_expected(*expr, expected_ty));
        }
      }
    }

    let children_key_id = self.jsx_children_prop_key(loc);
    let expected_children_prop_ty = expected
      .filter(|ty| !matches!(self.store.type_kind(*ty), TypeKind::Any | TypeKind::Unknown))
      .map(|props_ty| {
        let children_prop = self.store.name(children_key_id);
        self.member_type(props_ty, &children_prop)
      });

    if let Some(children_ty) = self.jsx_children_prop_type_hir(children, expected_children_prop_ty)
    {
      props.insert(self.store.name(children_key_id));
      let key = PropKey::String(children_key_id);
      shape.properties.push(types_ts_interned::Property {
        key,
        data: PropData {
          ty: children_ty,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }

    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    let mut ty = self.store.intern_type(TypeKind::Object(obj));
    if !spreads.is_empty() {
      spreads.insert(0, ty);
      ty = self.store.intersection(spreads);
    }
    JsxActualProps {
      ty,
      props,
      has_spread,
    }
  }

  pub(crate) fn jsx_children_prop_type_hir(
    &mut self,
    children: &[JsxChild],
    expected: Option<TypeId>,
  ) -> Option<TypeId> {
    let prim = self.store.primitive_ids();
    let mut collected = Vec::new();
    let mut spread = false;

    let mut meaningful = 0usize;
    let mut has_spread_child = false;
    for child in children {
      match child {
        JsxChild::Text(text) => {
          if !text.trim().is_empty() {
            meaningful += 1;
          }
        }
        JsxChild::Expr(container) => {
          if container.expr.is_none() {
            continue;
          }
          meaningful += 1;
          if container.spread {
            has_spread_child = true;
          }
        }
        JsxChild::Element(_) => {
          meaningful += 1;
        }
      }
      if meaningful > 1 {
        break;
      }
    }

    let expected_children_ty = expected.unwrap_or(prim.unknown);
    let expected_spread_ty =
      if has_spread_child && self.spread_element_type(expected_children_ty) != prim.unknown {
        expected_children_ty
      } else {
        prim.unknown
      };
    let expected_child_ty = if has_spread_child || meaningful > 1 {
      self.spread_element_type(expected_children_ty)
    } else {
      expected_children_ty
    };

    for child in children {
      match child {
        JsxChild::Text(text) => {
          if let Some(ty) = self.jsx_child_text_type_str(text) {
            collected.push(ty);
          }
        }
        JsxChild::Expr(container) => {
          let Some(expr_id) = container.expr else {
            continue;
          };
          let expr_ty = if container.spread {
            self.check_hir_expr_id_with_expected(expr_id, expected_spread_ty)
          } else {
            self.check_hir_expr_id_with_expected(expr_id, expected_child_ty)
          };
          if !container.spread
            && expected_child_ty != prim.unknown
            && !matches!(
              self.store.type_kind(expected_child_ty),
              TypeKind::Any | TypeKind::Unknown
            )
          {
            if let Some(ast) = self
              .body
              .exprs
              .get(expr_id.0 as usize)
              .and_then(|e| self.index.exprs.get(&e.span).copied())
            {
              if let AstExpr::LitObj(obj) = ast.stx.as_ref() {
                let _ = self.report_excess_property(obj, expected_child_ty);
              }
            }
          }
          let ty = if container.spread {
            spread = true;
            self.spread_element_type(expr_ty)
          } else {
            expr_ty
          };
          if ty != prim.unknown {
            collected.push(ty);
          }
        }
        JsxChild::Element(expr_id) => {
          collected.push(self.check_hir_jsx_expr_id(*expr_id));
        }
      }
    }
    if collected.is_empty() {
      None
    } else if spread || collected.len() > 1 {
      let ty = self.store.union(collected);
      Some(self.store.intern_type(TypeKind::Array {
        ty,
        readonly: false,
      }))
    } else {
      Some(collected[0])
    }
  }

  pub(crate) fn jsx_attr_text_type_str(&mut self, text: &str) -> TypeId {
    let name = self.store.intern_name(text.to_string());
    self.store.intern_type(TypeKind::StringLiteral(name))
  }

  pub(crate) fn jsx_child_text_type_str(&mut self, text: &str) -> Option<TypeId> {
    let trimmed = text.trim();
    if trimmed.is_empty() {
      return None;
    }
    let name = self.store.intern_name(trimmed.to_string());
    Some(self.store.intern_type(TypeKind::StringLiteral(name)))
  }

  /// Residual AST attribute / children walk.
  pub(crate) fn jsx_actual_props(
    &mut self,
    loc: Loc,
    attrs: &[JsxAttr],
    children: &[JsxElemChild],
    expected: Option<TypeId>,
  ) -> JsxActualProps {
    let prim = self.store.primitive_ids();
    let mut props = HashSet::new();
    let mut shape = Shape::new();
    let mut spreads = Vec::new();
    let mut has_spread = false;
    for attr in attrs {
      match attr {
        JsxAttr::Named { name, value } => {
          let key_string = if let Some(namespace) = name.stx.namespace.as_ref() {
            format!("{namespace}:{}", name.stx.name)
          } else {
            name.stx.name.clone()
          };
          props.insert(key_string.clone());
          let key = PropKey::String(self.store.intern_name(key_string.clone()));
          let value_ty = match value {
            None => self.store.intern_type(TypeKind::BooleanLiteral(true)),
            Some(JsxAttrVal::Text(text)) => self.jsx_attr_text_type(text),
            Some(JsxAttrVal::Expression(expr)) => {
              if is_empty_jsx_expr_placeholder(&expr.stx.value) {
                prim.unknown
              } else {
                let expected_ty = expected
                  .filter(|ty| {
                    !matches!(self.store.type_kind(*ty), TypeKind::Any | TypeKind::Unknown)
                  })
                  .map(|props_ty| self.member_type(props_ty, &key_string))
                  .unwrap_or(prim.unknown);
                let value_ty = self.check_expr_with_expected(&expr.stx.value, expected_ty);
                if expected_ty != prim.unknown
                  && !matches!(
                    self.store.type_kind(expected_ty),
                    TypeKind::Any | TypeKind::Unknown
                  )
                {
                  if let AstExpr::LitObj(obj) = expr.stx.value.stx.as_ref() {
                    let _ = self.report_excess_property(obj, expected_ty);
                  }
                }
                value_ty
              }
            }
            Some(JsxAttrVal::Element(elem)) => self.check_jsx_elem(elem),
          };
          shape.properties.push(types_ts_interned::Property {
            key,
            data: PropData {
              ty: value_ty,
              optional: false,
              readonly: false,
              accessibility: None,
              is_method: false,
              origin: None,
              declared_on: None,
            },
          });
        }
        JsxAttr::Spread { value } => {
          has_spread = true;
          let expected_ty = expected
            .filter(|ty| !matches!(self.store.type_kind(*ty), TypeKind::Any | TypeKind::Unknown))
            .unwrap_or(prim.unknown);
          spreads.push(self.check_expr_with_expected(&value.stx.value, expected_ty));
        }
      }
    }

    let children_key_id = self.jsx_children_prop_key(loc);
    let expected_children_prop_ty = expected
      .filter(|ty| !matches!(self.store.type_kind(*ty), TypeKind::Any | TypeKind::Unknown))
      .map(|props_ty| {
        let children_prop = self.store.name(children_key_id);
        self.member_type(props_ty, &children_prop)
      });

    if let Some(children_ty) = self.jsx_children_prop_type(children, expected_children_prop_ty) {
      props.insert(self.store.name(children_key_id));
      let key = PropKey::String(children_key_id);
      shape.properties.push(types_ts_interned::Property {
        key,
        data: PropData {
          ty: children_ty,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      });
    }

    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    let mut ty = self.store.intern_type(TypeKind::Object(obj));
    if !spreads.is_empty() {
      spreads.insert(0, ty);
      ty = self.store.intersection(spreads);
    }
    JsxActualProps {
      ty,
      props,
      has_spread,
    }
  }

  pub(crate) fn jsx_children_prop_type(
    &mut self,
    children: &[JsxElemChild],
    expected: Option<TypeId>,
  ) -> Option<TypeId> {
    let prim = self.store.primitive_ids();
    let mut collected = Vec::new();
    let mut spread = false;

    let mut meaningful = 0usize;
    let mut has_spread_child = false;
    for child in children {
      match child {
        JsxElemChild::Text(text) => {
          if !text.stx.value.trim().is_empty() {
            meaningful += 1;
          }
        }
        JsxElemChild::Expr(expr) => {
          if is_empty_jsx_expr_placeholder(&expr.stx.value) {
            continue;
          }
          meaningful += 1;
          if expr.stx.spread {
            has_spread_child = true;
          }
        }
        JsxElemChild::Element(_) => {
          meaningful += 1;
        }
      }
      if meaningful > 1 {
        break;
      }
    }

    let expected_children_ty = expected.unwrap_or(prim.unknown);
    let expected_spread_ty =
      if has_spread_child && self.spread_element_type(expected_children_ty) != prim.unknown {
        expected_children_ty
      } else {
        prim.unknown
      };
    let expected_child_ty = if has_spread_child || meaningful > 1 {
      self.spread_element_type(expected_children_ty)
    } else {
      expected_children_ty
    };

    for child in children {
      match child {
        JsxElemChild::Text(text) => {
          if let Some(ty) = self.jsx_child_text_type(text) {
            collected.push(ty);
          }
        }
        JsxElemChild::Expr(expr) => {
          if is_empty_jsx_expr_placeholder(&expr.stx.value) {
            continue;
          }
          let expr_ty = if expr.stx.spread {
            self.check_expr_with_expected(&expr.stx.value, expected_spread_ty)
          } else {
            self.check_expr_with_expected(&expr.stx.value, expected_child_ty)
          };
          if !expr.stx.spread
            && expected_child_ty != prim.unknown
            && !matches!(
              self.store.type_kind(expected_child_ty),
              TypeKind::Any | TypeKind::Unknown
            )
          {
            if let AstExpr::LitObj(obj) = expr.stx.value.stx.as_ref() {
              let _ = self.report_excess_property(obj, expected_child_ty);
            }
          }
          let ty = if expr.stx.spread {
            spread = true;
            self.spread_element_type(expr_ty)
          } else {
            expr_ty
          };
          if ty != prim.unknown {
            collected.push(ty);
          }
        }
        JsxElemChild::Element(elem) => {
          collected.push(self.check_jsx_elem(elem));
        }
      }
    }
    if collected.is_empty() {
      None
    } else if spread || collected.len() > 1 {
      let ty = self.store.union(collected);
      Some(self.store.intern_type(TypeKind::Array {
        ty,
        readonly: false,
      }))
    } else {
      Some(collected[0])
    }
  }

  pub(crate) fn jsx_attr_text_type(&mut self, text: &Node<JsxText>) -> TypeId {
    let name = self.store.intern_name(text.stx.value.clone());
    self.store.intern_type(TypeKind::StringLiteral(name))
  }

  pub(crate) fn jsx_child_text_type(&mut self, text: &Node<JsxText>) -> Option<TypeId> {
    let trimmed = text.stx.value.trim();
    if trimmed.is_empty() {
      return None;
    }
    let name = self.store.intern_name(trimmed.to_string());
    Some(self.store.intern_type(TypeKind::StringLiteral(name)))
  }

  pub(crate) fn check_jsx_props(&mut self, loc: Loc, actual: &JsxActualProps, expected: TypeId) {
    if matches!(
      self.store.type_kind(expected),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return;
    }
    if !actual.has_spread && !self.type_accepts_props(expected, &actual.props) {
      let mut unknown = actual.props.iter().cloned().collect::<Vec<_>>();
      unknown.sort();
      let message = if let Some(name) = unknown.iter().find(|name| {
        let mut single = HashSet::with_capacity(1);
        single.insert((*name).clone());
        !self.type_accepts_props(expected, &single)
      }) {
        let target_disp =
          TypeDisplay::new(self.store.as_ref(), self.store.canon(expected)).to_string();
        codes::excess_property_message(name, &target_disp)
      } else {
        "excess property".to_string()
      };
      self.diagnostics.push(
        codes::EXCESS_PROPERTY.error(message, Span::new(self.file, loc_to_range(self.file, loc))),
      );
      return;
    }
    if matches!(
      self.store.type_kind(actual.ty),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return;
    }
    if self.relate.is_assignable(actual.ty, expected) {
      return;
    }
    self.diagnostics.push(codes::TYPE_MISMATCH.error(
      "type mismatch",
      Span::new(self.file, loc_to_range(self.file, loc)),
    ));
  }

  pub(crate) fn jsx_apply_intrinsic_attributes(&mut self, expected: TypeId) -> TypeId {
    if matches!(
      self.store.type_kind(expected),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return expected;
    }
    let intrinsic = self.jsx_intrinsic_attributes_type();
    if matches!(self.store.type_kind(intrinsic), TypeKind::EmptyObject) {
      return expected;
    }
    self.store.intersection(vec![expected, intrinsic])
  }

  pub(crate) fn check_jsx_component(
    &mut self,
    component_ty: TypeId,
    actual_props: &JsxActualProps,
    element_ty: TypeId,
    loc: Loc,
  ) {
    let span = Span::new(self.file, loc_to_range(self.file, loc));
    let prim = self.store.primitive_ids();
    if matches!(
      self.store.type_kind(component_ty),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return;
    }

    let call_sigs = self.jsx_component_call_signatures(component_ty);
    let is_construct = call_sigs.is_empty();
    let (sigs, contextual_return) = if !is_construct {
      let contextual_return = !matches!(
        self.store.type_kind(element_ty),
        TypeKind::Any | TypeKind::Unknown
      );
      (call_sigs, contextual_return)
    } else {
      (self.jsx_component_construct_signatures(component_ty), false)
    };

    if sigs.is_empty() {
      self.diagnostics.push(
        codes::NO_OVERLOAD
          .error("JSX component is not callable or constructable", span)
          .with_note(format!(
            "component has type {}",
            TypeDisplay::new(self.store.as_ref(), component_ty)
          )),
      );
      return;
    }

    let empty_props = {
      let shape_id = self.store.intern_shape(Shape::new());
      let obj = self.store.intern_object(ObjectType { shape: shape_id });
      self.store.intern_type(TypeKind::Object(obj))
    };

    let element_class_ty = is_construct.then(|| self.jsx_element_class_type());
    let enforce_element_class = element_class_ty
      .is_some_and(|ty| !matches!(self.store.type_kind(ty), TypeKind::Any | TypeKind::Unknown));

    let args = [CallArgType::new(actual_props.ty)];
    let contextual_return_ty = contextual_return.then_some(element_ty);
    let valid_return_ty =
      contextual_return_ty.map(|el_ty| self.store.union(vec![el_ty, prim.null]));
    let mut filtered_props: Vec<TypeId> = Vec::new();
    let mut all_props: Vec<TypeId> = Vec::new();
    let mut saw_valid_return = false;
    for sig_id in sigs.iter().copied() {
      let sig = self.store.signature(sig_id);
      let mut props_ty = sig.params.first().map(|p| p.ty).unwrap_or(empty_props);
      let mut ret_ty = sig.ret;
      if !sig.type_params.is_empty() && !sig.params.is_empty() {
        let inference = infer_type_arguments_for_call(
          &self.store,
          &self.relate,
          &sig,
          &args,
          None,
          contextual_return_ty,
        );
        let mut substituter = Substituter::new(Arc::clone(&self.store), inference.substitutions);
        props_ty = substituter.substitute_type(props_ty);
        ret_ty = substituter.substitute_type(ret_ty);
      }
      if enforce_element_class
        && !matches!(
          self.store.type_kind(ret_ty),
          TypeKind::Any | TypeKind::Unknown
        )
      {
        let class_ty = element_class_ty.expect("enforced element class type");
        if !self.relate.is_assignable(ret_ty, class_ty) {
          continue;
        }
      }
      if is_construct {
        if let Some(attrs_prop) = self.jsx_element_attributes_prop_key() {
          let prop_name = self.store.name(attrs_prop);
          if self.type_has_prop(ret_ty, &prop_name) {
            props_ty = self.member_type(ret_ty, &prop_name);
          }
        }
      }
      props_ty = self.jsx_apply_library_managed_attributes(component_ty, props_ty);
      if is_construct {
        let class_attrs = self.jsx_intrinsic_class_attributes_type(ret_ty);
        if !matches!(self.store.type_kind(class_attrs), TypeKind::EmptyObject) {
          props_ty = self.store.intersection(vec![props_ty, class_attrs]);
        }
      }
      all_props.push(props_ty);
      if let Some(valid_return) = valid_return_ty {
        let return_ok = matches!(
          self.store.type_kind(ret_ty),
          TypeKind::Any | TypeKind::Unknown
        ) || self.relate.is_assignable(ret_ty, valid_return);
        if return_ok {
          saw_valid_return = true;
          filtered_props.push(props_ty);
        }
      }
    }
    if enforce_element_class && all_props.is_empty() {
      let class_ty = element_class_ty.expect("enforced element class type");
      self.diagnostics.push(
        codes::NO_OVERLOAD
          .error(
            "JSX class component does not satisfy JSX.ElementClass",
            span,
          )
          .with_note(format!(
            "expected JSX.ElementClass {}, got component type {}",
            TypeDisplay::new(self.store.as_ref(), class_ty),
            TypeDisplay::new(self.store.as_ref(), component_ty)
          )),
      );
      return;
    }
    if valid_return_ty.is_some() && !saw_valid_return {
      let expected = valid_return_ty.expect("return type computed");
      self.diagnostics.push(
        codes::NO_OVERLOAD
          .error("JSX component return type is not a valid JSX element", span)
          .with_note(format!(
            "expected return type assignable to {}, got component type {}",
            TypeDisplay::new(self.store.as_ref(), expected),
            TypeDisplay::new(self.store.as_ref(), component_ty),
          )),
      );
      return;
    }
    let mut props = if contextual_return_ty.is_some() && !filtered_props.is_empty() {
      filtered_props
    } else {
      all_props
    };
    props.sort();
    props.dedup();
    let expected_props = if props.len() == 1 {
      props[0]
    } else {
      self.store.union(props)
    };
    if expected_props == prim.unknown {
      return;
    }
    let expected_props = self.jsx_apply_intrinsic_attributes(expected_props);
    self.check_jsx_props(loc, actual_props, expected_props);
  }

  pub(crate) fn jsx_component_call_signatures(&self, ty: TypeId) -> Vec<SignatureId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    self.jsx_collect_call_signatures(ty, &mut out, &mut seen);
    out.sort();
    out.dedup();
    out
  }

  pub(crate) fn jsx_collect_call_signatures(
    &self,
    ty: TypeId,
    out: &mut Vec<SignatureId>,
    seen: &mut HashSet<TypeId>,
  ) {
    if !seen.insert(ty) {
      return;
    }
    let expanded = self.expand_for_props(ty);
    if expanded != ty {
      self.jsx_collect_call_signatures(expanded, out, seen);
      return;
    }
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => out.extend(overloads),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        out.extend(shape.call_signatures);
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          self.jsx_collect_call_signatures(member, out, seen);
        }
      }
      TypeKind::Ref { def, args } => {
        if let Some(expander) = self.ref_expander {
          if let Some(expanded) = expander.expand_ref(self.store.as_ref(), def, &args) {
            self.jsx_collect_call_signatures(expanded, out, seen);
          }
        }
      }
      _ => {}
    }
  }

  pub(crate) fn jsx_component_construct_signatures(&self, ty: TypeId) -> Vec<SignatureId> {
    let mut out = Vec::new();
    let mut seen = HashSet::new();
    self.jsx_collect_construct_signatures(ty, &mut out, &mut seen);
    out.sort();
    out.dedup();
    out
  }

  pub(crate) fn jsx_collect_construct_signatures(
    &self,
    ty: TypeId,
    out: &mut Vec<SignatureId>,
    seen: &mut HashSet<TypeId>,
  ) {
    if !seen.insert(ty) {
      return;
    }
    let expanded = self.expand_for_props(ty);
    if expanded != ty {
      self.jsx_collect_construct_signatures(expanded, out, seen);
      return;
    }
    match self.store.type_kind(ty) {
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        out.extend(shape.construct_signatures);
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          self.jsx_collect_construct_signatures(member, out, seen);
        }
      }
      TypeKind::Ref { def, args } => {
        if let Some(expander) = self.ref_expander {
          if let Some(expanded) = expander.expand_ref(self.store.as_ref(), def, &args) {
            self.jsx_collect_construct_signatures(expanded, out, seen);
          }
        }
      }
      _ => {}
    }
  }

  pub(crate) fn resolve_type_ref(&mut self, path: &[&str]) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let segments: Vec<String> = path.iter().map(|s| s.to_string()).collect();
    let def = resolver.resolve_type_name(&segments)?;
    Some(self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: Vec::new(),
    })))
  }

  pub(crate) fn report_jsx_namespace_missing(&mut self, loc: Loc) {
    if self.jsx_namespace_missing_reported {
      return;
    }
    self.jsx_namespace_missing_reported = true;
    self.diagnostics.push(codes::JSX_NAMESPACE_MISSING.error(
      "missing JSX namespace typings",
      Span::new(self.file, loc_to_range(self.file, loc)),
    ));
  }

  pub(crate) fn jsx_element_type(&mut self, loc: Loc) -> TypeId {
    if let Some(ty) = self.jsx_element_ty {
      return ty;
    }
    let prim = self.store.primitive_ids();
    let resolved = self.resolve_type_ref(&["JSX", "Element"]);
    if resolved.is_none() {
      self.report_jsx_namespace_missing(loc);
    }
    let ty = resolved.unwrap_or(prim.unknown);
    self.jsx_element_ty = Some(ty);
    ty
  }

  pub(crate) fn jsx_element_class_type(&mut self) -> TypeId {
    if let Some(ty) = self.jsx_element_class_ty {
      return ty;
    }
    let prim = self.store.primitive_ids();
    let ty = self
      .resolve_type_ref(&["JSX", "ElementClass"])
      .unwrap_or(prim.unknown);
    self.jsx_element_class_ty = Some(ty);
    ty
  }

  pub(crate) fn jsx_intrinsic_elements_type(&mut self, loc: Loc) -> TypeId {
    if let Some(ty) = self.jsx_intrinsic_elements_ty {
      return ty;
    }
    let prim = self.store.primitive_ids();
    let resolved = self.resolve_type_ref(&["JSX", "IntrinsicElements"]);
    if resolved.is_none() {
      self.report_jsx_namespace_missing(loc);
    }
    let ty = resolved.unwrap_or(prim.unknown);
    self.jsx_intrinsic_elements_ty = Some(ty);
    ty
  }

  pub(crate) fn jsx_intrinsic_attributes_type(&mut self) -> TypeId {
    if let Some(ty) = self.jsx_intrinsic_attributes_ty {
      return ty;
    }
    // `JSX.IntrinsicAttributes` is optional; when absent treat it as `{}` so it
    // neither contributes additional props nor disables checks.
    let ty = self
      .resolve_type_ref(&["JSX", "IntrinsicAttributes"])
      .unwrap_or_else(|| self.store.intern_type(TypeKind::EmptyObject));
    self.jsx_intrinsic_attributes_ty = Some(ty);
    ty
  }

  pub(crate) fn jsx_library_managed_attributes_def_id(&mut self) -> Option<DefId> {
    if let Some(cached) = self.jsx_library_managed_attributes_def.as_ref() {
      return *cached;
    }
    let def = self
      .resolve_type_ref(&["JSX", "LibraryManagedAttributes"])
      .and_then(|ty| match self.store.type_kind(ty) {
        TypeKind::Ref { def, args } if args.is_empty() => Some(def),
        _ => None,
      });
    self.jsx_library_managed_attributes_def = Some(def);
    def
  }

  pub(crate) fn jsx_apply_library_managed_attributes(
    &mut self,
    component: TypeId,
    props: TypeId,
  ) -> TypeId {
    if matches!(
      self.store.type_kind(props),
      TypeKind::Any | TypeKind::Unknown
    ) {
      return props;
    }
    let Some(def) = self.jsx_library_managed_attributes_def_id() else {
      return props;
    };
    self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: vec![component, props],
    }))
  }

  pub(crate) fn jsx_intrinsic_class_attributes_def_id(&mut self) -> Option<DefId> {
    if let Some(cached) = self.jsx_intrinsic_class_attributes_def.as_ref() {
      return *cached;
    }
    let def = self
      .resolve_type_ref(&["JSX", "IntrinsicClassAttributes"])
      .and_then(|ty| match self.store.type_kind(ty) {
        TypeKind::Ref { def, args } if args.is_empty() => Some(def),
        _ => None,
      });
    self.jsx_intrinsic_class_attributes_def = Some(def);
    def
  }

  pub(crate) fn jsx_intrinsic_class_attributes_type(&mut self, instance: TypeId) -> TypeId {
    let Some(def) = self.jsx_intrinsic_class_attributes_def_id() else {
      return self.store.intern_type(TypeKind::EmptyObject);
    };
    self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: vec![instance],
    }))
  }

  pub(crate) fn jsx_element_attributes_prop_key(&mut self) -> Option<TsNameId> {
    if let Some(cached) = self.jsx_element_attributes_prop_name.as_ref() {
      return *cached;
    }
    let Some(attrs_ty) = self.resolve_type_ref(&["JSX", "ElementAttributesProperty"]) else {
      self.jsx_element_attributes_prop_name = Some(None);
      return None;
    };
    let mut candidates = Vec::new();
    let mut seen = HashSet::new();
    self.jsx_collect_children_attribute_keys(attrs_ty, &mut candidates, &mut seen);
    candidates.sort();
    candidates.dedup();
    let selected = candidates
      .into_iter()
      .next()
      .map(|name| self.store.intern_name(name));
    self.jsx_element_attributes_prop_name = Some(selected);
    selected
  }

  pub(crate) fn jsx_children_prop_key(&mut self, _loc: Loc) -> TsNameId {
    if let Some(id) = self.jsx_children_prop_name {
      return id;
    }
    let fallback = self.store.intern_name("children".to_string());
    let Some(children_attr_ty) = self.resolve_type_ref(&["JSX", "ElementChildrenAttribute"]) else {
      self.jsx_children_prop_name = Some(fallback);
      return fallback;
    };

    let mut candidates = Vec::new();
    let mut seen = HashSet::new();
    self.jsx_collect_children_attribute_keys(children_attr_ty, &mut candidates, &mut seen);
    candidates.sort();
    candidates.dedup();
    let selected = candidates
      .into_iter()
      .next()
      .map(|name| self.store.intern_name(name))
      .unwrap_or(fallback);
    self.jsx_children_prop_name = Some(selected);
    selected
  }

  pub(crate) fn jsx_collect_children_attribute_keys(
    &self,
    ty: TypeId,
    out: &mut Vec<String>,
    seen: &mut HashSet<TypeId>,
  ) {
    if !seen.insert(ty) {
      return;
    }
    let expanded = self.expand_for_props(ty);
    if expanded != ty {
      self.jsx_collect_children_attribute_keys(expanded, out, seen);
      return;
    }
    match self.store.type_kind(ty) {
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in shape.properties.iter() {
          match prop.key {
            PropKey::String(name) | PropKey::Symbol(name) => out.push(self.store.name(name)),
            PropKey::Number(num) => out.push(num.to_string()),
          }
        }
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for member in members {
          self.jsx_collect_children_attribute_keys(member, out, seen);
        }
      }
      TypeKind::Ref { def, args } => {
        if let Some(expander) = self.ref_expander {
          if let Some(expanded) = expander.expand_ref(self.store.as_ref(), def, &args) {
            self.jsx_collect_children_attribute_keys(expanded, out, seen);
          }
        }
      }
      _ => {}
    }
  }
}
