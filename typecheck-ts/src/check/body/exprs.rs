use std::collections::{HashSet, VecDeque};

use diagnostics::{Span, TextRange};
use num_bigint::BigInt;
use ordered_float::OrderedFloat;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::pat::Pat as AstPat;
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::func::Func;
use parse_js::ast::node::{Node, ParenthesizedExpr};
use parse_js::loc::Loc;
use parse_js::operator::OperatorName;
use parse_js::token::TT;
use types_ts_interned::{
  Accessibility, DefId, ObjectType, Param as SigParam, PropData, PropKey, Shape, Signature,
  SignatureId, TypeDisplay, TypeId, TypeKind,
};

use super::super::super::flow_narrow::narrow_non_nullish;
use super::super::super::overload::{callable_signatures, callable_signatures_with_expander};
use super::{classify_computed_obj_key, synthesize_computed_indexers, ComputedObjKey};
use crate::codes;

use super::super::{
  awaited_type, loc_to_range, parse_canonical_index_str, ArrayLiteralContext, Checker,
  ClassFieldInitializerContext, Scope,
};

impl<'a> Checker<'a> {
  pub(crate) fn check_expr(&mut self, expr: &Node<AstExpr>) -> TypeId {
    // Observe cancellation between expressions; hot relate/eval loops also
    // watch the same token via `RelateHooks::should_stop`.
    self.check_cancelled();
    let steps = self.expr_steps.get().saturating_add(1);
    self.expr_steps.set(steps);
    if self.relate.budget_exceeded()
      || self.eval_budget_exceeded.get()
      || steps > self.expr_step_limit
      || self.type_growth_exceeded()
    {
      // Fail fast once a body has tripped its engine budget: further expression
      // work is unlikely to be meaningful and can still allocate heavily.
      if self.type_growth_exceeded() {
        self.eval_budget_exceeded.set(true);
      }
      return self.store.primitive_ids().unknown;
    }
    let ty = match expr.stx.as_ref() {
      AstExpr::Id(id) => {
        // Prefer HIR CFA side-table types when they are already filled (flow
        // merge). Skip `unknown` placeholders from the pre-flow AST pass —
        // those would hide live binding types (including AST typeof overrides).
        let range = loc_to_range(self.file, expr.loc);
        let prim = self.store.primitive_ids();
        if let Some(ty) = self
          .expr_map
          .get(&range)
          .and_then(|eid| self.expr_types.get(eid.0 as usize))
          .copied()
          .filter(|ty| *ty != prim.unknown)
        {
          if id.stx.name.starts_with('#') || self.lookup(&id.stx.name).is_none() {
            let _ = self.resolve_ident(&id.stx.name, expr);
          }
          ty
        } else {
          self.resolve_ident(&id.stx.name, expr)
        }
      }
      AstExpr::LitNum(num) => {
        let value = num.stx.value.0;
        self
          .store
          .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(value)))
      }
      AstExpr::LitStr(str_lit) => {
        let name = self.store.intern_name(str_lit.stx.value.clone());
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      AstExpr::LitBool(b) => self
        .store
        .intern_type(TypeKind::BooleanLiteral(b.stx.value)),
      // Regex literals are `RegExp` (tsc). Fall back to `unknown` when the
      // global interface is unavailable — never `string`
      // (`controlFlowForInStatement.ts`: `x = /a/`).
      AstExpr::LitRegex(_) => self
        .regexp_literal_type()
        .unwrap_or(self.store.primitive_ids().unknown),
      AstExpr::LitNull(_) => self.store.primitive_ids().null,
      AstExpr::LitBigInt(value) => {
        let trimmed = value.stx.value.trim_end_matches('n');
        let parsed = trimmed.parse::<i128>().unwrap_or(0);
        self
          .store
          .intern_type(TypeKind::BigIntLiteral(parsed.into()))
      }
      AstExpr::This(_) => self.contextual_this_ty.unwrap_or_else(|| {
        // tsc: `this` in a function (expression or declaration) without a
        // contextual `this` type is `any` (`typeOfThisInFunctionExpression.ts`).
        if matches!(self.body_kind, hir_js::BodyKind::Function) {
          self.store.primitive_ids().any
        } else {
          self.store.primitive_ids().unknown
        }
      }),
      AstExpr::Super(_) => self.resolve_super_type(),
      AstExpr::Unary(un) => {
        if matches!(un.stx.operator, OperatorName::New) {
          self.check_new_expr(un, expr.loc, None)
        } else {
          self.check_unary(un.stx.operator, &un.stx.argument)
        }
      }
      AstExpr::UnaryPostfix(post) => match post.stx.operator {
        OperatorName::PostfixIncrement | OperatorName::PostfixDecrement => {
          // Compound update reads the target (tsc AssignmentKind.Compound).
          self.check_compound_update_target(&post.stx.argument);
          self.store.primitive_ids().number
        }
        _ => self.store.primitive_ids().unknown,
      },
      AstExpr::Binary(bin) => self.check_binary(bin.stx.operator, &bin.stx.left, &bin.stx.right),
      AstExpr::Cond(cond) => {
        let cons = self.check_expr(&cond.stx.consequent);
        let alt = self.check_expr(&cond.stx.alternate);
        self.store.union(vec![cons, alt])
      }
      AstExpr::Call(call) => self.check_call_expr(call, None),
      AstExpr::TaggedTemplate(tagged) => self.check_tagged_template_expr(tagged),
      AstExpr::LitTemplate(template) => self.template_literal_type(template),
      AstExpr::Member(mem) => {
        let full_range = loc_to_range(self.file, mem.loc);
        let prop_len = mem.stx.right.len() as u32;
        let prop_span = TextRange::new(full_range.end.saturating_sub(prop_len), full_range.end);
        self.check_abstract_property_in_constructor(&mem.stx.left, &mem.stx.right, prop_span);
        self.check_property_used_before_assigned(&mem.stx.left, &mem.stx.right, prop_span);
        self.check_property_not_used_before_initialization(
          &mem.stx.left,
          &mem.stx.right,
          full_range,
        );
        // Read / nested-read of a setter-only private accessor (TS2806). Definite
        // writes go through `check_assignment` / `check_assign_target_expr` instead.
        self.check_private_write_only_accessor_read(&mem.stx.right, full_range);
        let prim = self.store.primitive_ids();
        let obj_ty = self.check_expr(&mem.stx.left);
        let chain_optional =
          mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.left);
        let base_obj_ty = if chain_optional {
          let (non_nullish, _) = narrow_non_nullish(obj_ty, &self.store);
          non_nullish
        } else {
          obj_ty
        };
        // Collapse `A & B` alias intersections to `never` before member checks
        // (same reduction as callability via expand_callable_type).
        let base_obj_ty = self.expand_callable_type(base_obj_ty);
        // TS18013 / TS18014 / TS18030 / TS18046: private-identifier visibility /
        // shadowing / optional-chain ban / unknown receiver.
        self.check_private_identifier_property_access(
          base_obj_ty,
          Some(&mem.stx.left),
          &mem.stx.right,
          prop_span,
          chain_optional,
        );
        let mut prop_ty = if chain_optional && base_obj_ty == prim.never {
          prim.undefined
        } else {
          self.member_type(base_obj_ty, &mem.stx.right)
        };
        // Unannotated class fields sit as `unknown` on synthesized `this` shapes.
        // Recover initializer types / detect TS7022 circularity while typing
        // another field initializer (`#foo = this.#bar`, `["#bar"] = this["#bar"]`).
        if !chain_optional {
          prop_ty = self.recover_field_prop_type(&mem.stx.right, prop_ty);
        }

        let is_callable =
          !callable_signatures_with_expander(self.store.as_ref(), base_obj_ty, self.ref_expander)
            .is_empty();

        // tsc: property access on `never` is TS2339 (`reportNonexistentProperty`).
        // Also: callable receivers with missing props (TS2339). Private-identifier
        // missing props are reported by `check_private_identifier_property_access`.
        let missing_on_never = base_obj_ty == prim.never && !chain_optional;
        if (missing_on_never
          || (is_callable
            && prop_ty == prim.unknown
            && !matches!(
              self.store.type_kind(base_obj_ty),
              TypeKind::Any | TypeKind::Unknown | TypeKind::Never
            )
            && !self.type_has_prop(base_obj_ty, &mem.stx.right)))
          && !mem.stx.right.starts_with('#')
        {
          let name_len = mem.stx.right.len() as u32;
          let start = full_range.end.saturating_sub(name_len);
          let range = TextRange::new(start, full_range.end);
          self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
            format!(
              "Property '{}' does not exist on type '{}'.",
              mem.stx.right,
              TypeDisplay::new(self.store.as_ref(), base_obj_ty)
            ),
            Span::new(self.file, range),
          ));
          prop_ty = prim.any;
        }
        if self.native_define_class_fields {
          if let Some(props) = self.current_class_field_param_props {
            if matches!(mem.stx.left.stx.as_ref(), AstExpr::This(_))
              && props.iter().any(|name| name == &mem.stx.right)
            {
              let name_len = mem.stx.right.len() as u32;
              let start = full_range.end.saturating_sub(name_len);
              let range = TextRange::new(start, full_range.end);
              self
                .diagnostics
                .push(codes::PROPERTY_USED_BEFORE_INITIALIZATION.error(
                  format!(
                    "Property '{}' is used before its initialization.",
                    mem.stx.right
                  ),
                  Span::new(self.file, range),
                ));
            }
          }
        }
        if chain_optional {
          self.store.union(vec![prop_ty, prim.undefined])
        } else {
          prop_ty
        }
      }
      AstExpr::ComputedMember(mem) => {
        let prim = self.store.primitive_ids();
        let obj_ty = self.check_expr(&mem.stx.object);
        let chain_optional =
          mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.object);
        let base_obj_ty = if chain_optional {
          let (non_nullish, _) = narrow_non_nullish(obj_ty, &self.store);
          non_nullish
        } else {
          obj_ty
        };
        let key_ty = self.check_expr(&mem.stx.member);

        let literal_key = match mem.stx.member.stx.as_ref() {
          AstExpr::LitStr(s) => Some(s.stx.value.clone()),
          AstExpr::LitNum(n) => Some(n.stx.value.0.to_string()),
          AstExpr::LitBigInt(v) => Some(v.stx.value.clone()),
          _ => match self.store.type_kind(key_ty) {
            TypeKind::StringLiteral(id) => Some(self.store.name(id).to_string()),
            TypeKind::NumberLiteral(num) => Some(num.0.to_string()),
            _ => None,
          },
        };

        if let Some(ref key) = literal_key {
          if !chain_optional {
            self.maybe_report_tuple_index_oob(
              base_obj_ty,
              key,
              loc_to_range(self.file, mem.stx.member.loc),
            );
          }
        }

        let mut ty = if chain_optional && base_obj_ty == prim.never {
          prim.undefined
        } else if let Some(ref key) = literal_key {
          let mut prop_ty = self.member_type(base_obj_ty, key);
          if !chain_optional {
            prop_ty = self.recover_field_prop_type(key, prop_ty);
          }
          prop_ty
        } else {
          self.member_type_for_index_key(base_obj_ty, key_ty, /*writing*/ false)
        };
        if self.relate.options.no_unchecked_indexed_access {
          ty = self.store.union(vec![ty, prim.undefined]);
        }
        if chain_optional {
          ty = self.store.union(vec![ty, prim.undefined]);
        }
        ty
      }
      AstExpr::LitArr(arr) => self.array_literal_type(arr),
      AstExpr::LitObj(obj) => self.object_literal_type(obj),
      AstExpr::Func(func) => self.function_type(&func.stx.func),
      AstExpr::ArrowFunc(func) => self.function_type(&func.stx.func),
      AstExpr::Class(class_expr) => self.check_class_expression(class_expr, expr.loc),
      AstExpr::JsxElem(elem) => self.check_jsx_elem(elem),
      AstExpr::IdPat(_) | AstExpr::ArrPat(_) | AstExpr::ObjPat(_) => {
        self.store.primitive_ids().unknown
      }
      AstExpr::Instantiation(inst) => {
        let base_ty = self.check_expr(&inst.stx.expression);
        let range = loc_to_range(self.file, expr.loc);
        // Prefer HIR `ExprKind::Instantiation` type args (`TypeExprId`); AST
        // TypeLowerer is residual for `import(...)` / missing arenas.
        let hir_args = self
          .hir_instantiation_type_args_at(range)
          .map(|args| args.to_vec());
        let args: Vec<_> = if let Some(hir_args) = hir_args.as_deref() {
          let mut lowered = Vec::with_capacity(hir_args.len());
          let mut used_hir = true;
          for &ann in hir_args {
            if let Some(ty) = self.hir_lower_type_expr_id(ann) {
              lowered.push(ty);
            } else {
              used_hir = false;
              break;
            }
          }
          if used_hir && lowered.len() == hir_args.len() {
            lowered
          } else {
            inst
              .stx
              .type_arguments
              .iter()
              .map(|arg| self.lowerer.lower_type_expr(arg))
              .collect()
          }
        } else {
          inst
            .stx
            .type_arguments
            .iter()
            .map(|arg| self.lowerer.lower_type_expr(arg))
            .collect()
        };
        let span = Span::new(self.file, range);
        self.apply_explicit_type_args(base_ty, &args, span)
      }
      AstExpr::TypeAssertion(assert) => {
        // Prefer HIR `const_assertion` + `TypeExprId`; AST TypeLowerer is residual
        // for `import(...)` / `typeof import(...)` targets (and no arenas).
        let range = loc_to_range(self.file, expr.loc);
        let hir = self.hir_type_assertion_at(range);
        let is_const = hir.map(|(c, _)| c).unwrap_or(assert.stx.const_assertion);
        if is_const {
          self.const_assertion_type(&assert.stx.expression)
        } else {
          let inner = self.check_expr(&assert.stx.expression);
          let target = if let Some(ann) = hir.and_then(|(_, ann)| ann) {
            if let Some(ty) = self.hir_lower_type_expr_id(ann) {
              ty
            } else if let Some(annotation) = assert.stx.type_annotation.as_ref() {
              self.lowerer.lower_type_expr(annotation)
            } else {
              inner
            }
          } else if let Some(annotation) = assert.stx.type_annotation.as_ref() {
            self.lowerer.lower_type_expr(annotation)
          } else {
            inner
          };
          self.report_type_assertion_overlap(inner, target, expr.loc);
          target
        }
      }
      AstExpr::NonNullAssertion(assert) => {
        // tsc `checkNonNullExpression`: strip null/undefined (and void) so
        // `undefined!` is `never` and assigns to any target
        // (`optionalPropertyAssignableToStringIndexSignature.ts`).
        let inner = self.check_expr(&assert.stx.expression);
        let (non_nullish, _) = narrow_non_nullish(inner, &self.store);
        non_nullish
      }
      AstExpr::SatisfiesExpr(expr) => {
        // Prefer HIR `Satisfies.type_annotation` (`TypeExprId`); residual AST
        // for `import(...)` / `typeof import(...)` / missing arenas.
        let range = loc_to_range(self.file, expr.loc);
        let target_ty = if let Some(ann) = self.hir_satisfies_annotation_at(range) {
          self
            .hir_lower_type_expr_id(ann)
            .unwrap_or_else(|| self.lowerer.lower_type_expr(&expr.stx.type_annotation))
        } else {
          self.lowerer.lower_type_expr(&expr.stx.type_annotation)
        };
        let value_ty = self.check_expr_with_expected(&expr.stx.expression, target_ty);
        // Reuse `check_assignable` so object-literal property mismatches get
        // tsc-aligned primary spans (property key), matching var/assignment
        // and `satisfies` (TS2322 on `mode` in `{ mode: "maybe" } satisfies …`).
        self.check_assignable(&expr.stx.expression, value_ty, target_ty, None);
        value_ty
      }
      _ => self.store.primitive_ids().unknown,
    };
    self.record_expr_type(expr.loc, ty);
    ty
  }

  /// Template literal expression type: no-substitution → string literal; otherwise
  /// widened `string` (after checking substitutions). Used so `` `x`(…) `` /
  /// `` `x` `y` `` are not typed as `unknown` (which silenced TS2349).
  pub(crate) fn template_literal_type(
    &mut self,
    template: &Node<parse_js::ast::expr::lit::LitTemplateExpr>,
  ) -> TypeId {
    use parse_js::ast::expr::lit::LitTemplatePart;

    let mut only_strings = true;
    let mut concat = String::new();
    for part in template.stx.parts.iter() {
      match part {
        LitTemplatePart::String(s) => concat.push_str(s),
        LitTemplatePart::Substitution(expr) => {
          only_strings = false;
          let _ = self.check_expr(expr);
        }
      }
    }
    if only_strings {
      let name = self.store.intern_name(concat);
      self.store.intern_type(TypeKind::StringLiteral(name))
    } else {
      self.store.primitive_ids().string
    }
  }

  pub(crate) fn is_optional_chain_expr(&self, expr: &Node<AstExpr>) -> bool {
    match expr.stx.as_ref() {
      AstExpr::Member(mem) => {
        mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.left)
      }
      AstExpr::ComputedMember(mem) => {
        mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.object)
      }
      AstExpr::Call(call) => {
        call.stx.optional_chaining || self.is_optional_chain_expr(&call.stx.callee)
      }
      AstExpr::Instantiation(inst) => self.is_optional_chain_expr(&inst.stx.expression),
      AstExpr::TypeAssertion(assert) => self.is_optional_chain_expr(&assert.stx.expression),
      AstExpr::NonNullAssertion(assert) => self.is_optional_chain_expr(&assert.stx.expression),
      AstExpr::SatisfiesExpr(expr) => self.is_optional_chain_expr(&expr.stx.expression),
      _ => false,
    }
  }

  pub(crate) fn recorded_expr_type(&self, loc: Loc) -> Option<TypeId> {
    let range = loc_to_range(self.file, loc);
    self
      .expr_map
      .get(&range)
      .and_then(|id| self.expr_types.get(id.0 as usize))
      .copied()
  }

  pub(crate) fn const_inference_type(&self, expr: &Node<AstExpr>) -> TypeId {
    let prim = self.store.primitive_ids();
    match expr.stx.as_ref() {
      AstExpr::LitNum(num) => self
        .store
        .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(num.stx.value.0))),
      AstExpr::LitStr(str_lit) => {
        let name = self.store.intern_name(str_lit.stx.value.clone());
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      AstExpr::LitTemplate(template) => {
        use parse_js::ast::expr::lit::LitTemplatePart;
        let mut only_strings = true;
        let mut concat = String::new();
        for part in template.stx.parts.iter() {
          match part {
            LitTemplatePart::String(s) => concat.push_str(s),
            LitTemplatePart::Substitution(_) => only_strings = false,
          }
        }
        if only_strings {
          let name = self.store.intern_name(concat);
          self.store.intern_type(TypeKind::StringLiteral(name))
        } else {
          prim.string
        }
      }
      AstExpr::LitBool(b) => self
        .store
        .intern_type(TypeKind::BooleanLiteral(b.stx.value)),
      AstExpr::LitNull(_) => prim.null,
      AstExpr::LitBigInt(value) => {
        let trimmed = value.stx.value.trim_end_matches('n');
        let parsed = trimmed
          .parse::<BigInt>()
          .unwrap_or_else(|_| BigInt::from(0u8));
        self.store.intern_type(TypeKind::BigIntLiteral(parsed))
      }
      AstExpr::LitArr(arr) => {
        let mut elems = Vec::new();
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(v) => {
              elems.push(types_ts_interned::TupleElem {
                ty: self.const_inference_type(v),
                optional: false,
                rest: false,
                readonly: true,
              })
            }
            parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
              elems.push(types_ts_interned::TupleElem {
                ty: self.const_inference_type(v),
                optional: false,
                rest: true,
                readonly: true,
              })
            }
            parse_js::ast::expr::lit::LitArrElem::Empty => {
              elems.push(types_ts_interned::TupleElem {
                ty: prim.undefined,
                optional: true,
                rest: false,
                readonly: true,
              })
            }
          }
        }
        self.store.intern_type(TypeKind::Tuple(elems))
      }
      AstExpr::LitObj(obj) => {
        let mut shape = Shape::new();
        for member in obj.stx.members.iter() {
          match &member.stx.typ {
            ObjMemberType::Valued { key, val } => {
              if let ClassOrObjKey::Direct(direct) = key {
                if let ClassOrObjVal::Prop(Some(value)) = val {
                  let prop_key = PropKey::String(self.store.intern_name(direct.stx.key.clone()));
                  let value_ty = self.const_inference_type(value);
                  shape.properties.push(types_ts_interned::Property {
                    key: prop_key,
                    data: PropData {
                      ty: value_ty,
                      optional: false,
                      readonly: true,
                      accessibility: None,
                      is_method: false,
                      origin: None,
                      declared_on: None,
                    },
                  });
                }
              }
            }
            ObjMemberType::Shorthand { id } => {
              let key = PropKey::String(self.store.intern_name(id.stx.name.clone()));
              let ty = self
                .lookup(&id.stx.name)
                .map(|b| b.ty)
                .unwrap_or(prim.unknown);
              shape.properties.push(types_ts_interned::Property {
                key,
                data: PropData {
                  ty,
                  optional: false,
                  readonly: true,
                  accessibility: None,
                  is_method: false,
                  origin: None,
                  declared_on: None,
                },
              });
            }
            // Spread under const-context inference still needs `&mut self` for
            // ref expansion helpers; handled in `const_assertion_type` / assign paths.
            ObjMemberType::Rest { .. } => {}
          }
        }
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      AstExpr::TypeAssertion(assert) => {
        let range = loc_to_range(self.file, expr.loc);
        let is_const = self
          .hir_type_assertion_at(range)
          .map(|(c, _)| c)
          .unwrap_or(assert.stx.const_assertion);
        if is_const {
          self.const_inference_type(&assert.stx.expression)
        } else {
          self
            .expr_map
            .get(&range)
            .and_then(|id| self.expr_types.get(id.0 as usize))
            .copied()
            .unwrap_or(prim.unknown)
        }
      }
      _ => {
        let range = loc_to_range(self.file, expr.loc);
        self
          .expr_map
          .get(&range)
          .and_then(|id| self.expr_types.get(id.0 as usize))
          .copied()
          .unwrap_or(prim.unknown)
      }
    }
  }

  pub(crate) fn const_assertion_type(&mut self, expr: &Node<AstExpr>) -> TypeId {
    let prim = self.store.primitive_ids();
    let ty = match expr.stx.as_ref() {
      AstExpr::LitNum(num) => self
        .store
        .intern_type(TypeKind::NumberLiteral(OrderedFloat::from(num.stx.value.0))),
      AstExpr::LitStr(str_lit) => {
        let name = self.store.intern_name(str_lit.stx.value.clone());
        self.store.intern_type(TypeKind::StringLiteral(name))
      }
      AstExpr::LitTemplate(template) => self.template_literal_type(template),
      AstExpr::LitBool(b) => self
        .store
        .intern_type(TypeKind::BooleanLiteral(b.stx.value)),
      AstExpr::LitNull(_) => prim.null,
      AstExpr::LitBigInt(value) => {
        let trimmed = value.stx.value.trim_end_matches('n');
        let parsed = trimmed
          .parse::<BigInt>()
          .unwrap_or_else(|_| BigInt::from(0u8));
        self.store.intern_type(TypeKind::BigIntLiteral(parsed))
      }
      AstExpr::LitArr(arr) => {
        let mut elems = Vec::new();
        for elem in arr.stx.elements.iter() {
          match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(v) => {
              elems.push(types_ts_interned::TupleElem {
                ty: self.const_assertion_type(v),
                optional: false,
                rest: false,
                readonly: true,
              })
            }
            parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
              elems.push(types_ts_interned::TupleElem {
                ty: self.const_assertion_type(v),
                optional: false,
                rest: true,
                readonly: true,
              })
            }
            parse_js::ast::expr::lit::LitArrElem::Empty => {
              elems.push(types_ts_interned::TupleElem {
                ty: prim.undefined,
                optional: true,
                rest: false,
                readonly: true,
              })
            }
          }
        }
        self.store.intern_type(TypeKind::Tuple(elems))
      }
      AstExpr::LitObj(obj) => {
        let mut shape = Shape::new();
        for member in obj.stx.members.iter() {
          match &member.stx.typ {
            ObjMemberType::Valued { key, val } => {
              if let ClassOrObjKey::Direct(direct) = key {
                if let ClassOrObjVal::Prop(Some(value)) = val {
                  let prop_key = PropKey::String(self.store.intern_name(direct.stx.key.clone()));
                  let value_ty = self.const_assertion_type(value);
                  shape.properties.push(types_ts_interned::Property {
                    key: prop_key,
                    data: PropData {
                      ty: value_ty,
                      optional: false,
                      readonly: true,
                      accessibility: None,
                      is_method: false,
                      origin: None,
                      declared_on: None,
                    },
                  });
                }
              } else if let ClassOrObjVal::Prop(Some(expr)) = val {
                let _ = self.check_expr(expr);
              }
            }
            ObjMemberType::Shorthand { id } => {
              let key = PropKey::String(self.store.intern_name(id.stx.name.clone()));
              let ty = self
                .lookup(&id.stx.name)
                .map(|b| b.ty)
                .unwrap_or(prim.unknown);
              shape.properties.push(types_ts_interned::Property {
                key,
                data: PropData {
                  ty,
                  optional: false,
                  readonly: true,
                  accessibility: None,
                  is_method: false,
                  origin: None,
                  declared_on: None,
                },
              });
            }
            ObjMemberType::Rest { val } => {
              let spread_ty = self.check_expr(val);
              self.append_object_spread_properties(&mut shape, spread_ty);
              for prop in shape.properties.iter_mut() {
                prop.data.readonly = true;
              }
            }
          }
        }
        let shape_id = self.store.intern_shape(shape);
        let obj = self.store.intern_object(ObjectType { shape: shape_id });
        self.store.intern_type(TypeKind::Object(obj))
      }
      AstExpr::TypeAssertion(assert) => {
        let range = loc_to_range(self.file, expr.loc);
        let hir = self.hir_type_assertion_at(range);
        let is_const = hir.map(|(c, _)| c).unwrap_or(assert.stx.const_assertion);
        if is_const {
          self.const_assertion_type(&assert.stx.expression)
        } else if let Some(ann) = hir.and_then(|(_, ann)| ann) {
          if let Some(ty) = self.hir_lower_type_expr_id(ann) {
            ty
          } else if let Some(annotation) = assert.stx.type_annotation.as_ref() {
            self.lowerer.lower_type_expr(annotation)
          } else {
            self.check_expr(&assert.stx.expression)
          }
        } else if let Some(annotation) = assert.stx.type_annotation.as_ref() {
          self.lowerer.lower_type_expr(annotation)
        } else {
          self.check_expr(&assert.stx.expression)
        }
      }
      _ => self.check_expr(expr),
    };
    self.record_expr_type(expr.loc, ty);
    ty
  }

  /// Global interface that supplies members for a primitive (tsc's
  /// `getGlobal*Type` / apparent-type path: `string` → `String`, etc.).
  pub(crate) fn primitive_interface_type(&self, ty: TypeId) -> Option<TypeId> {
    let name = match self.store.type_kind(ty) {
      TypeKind::String | TypeKind::StringLiteral(_) => "String",
      TypeKind::Number | TypeKind::NumberLiteral(_) => "Number",
      TypeKind::Boolean | TypeKind::BooleanLiteral(_) => "Boolean",
      TypeKind::BigInt | TypeKind::BigIntLiteral(_) => "BigInt",
      TypeKind::Symbol | TypeKind::UniqueSymbol => "Symbol",
      _ => return None,
    };
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&[name.to_string()])?;
    let ref_ty = self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: Vec::new(),
    }));
    let expanded = self.expand_ref(ref_ty);
    // Guard against a missing/cycle expansion that leaves a primitive.
    if matches!(
      self.store.type_kind(expanded),
      TypeKind::String
        | TypeKind::StringLiteral(_)
        | TypeKind::Number
        | TypeKind::NumberLiteral(_)
        | TypeKind::Boolean
        | TypeKind::BooleanLiteral(_)
        | TypeKind::BigInt
        | TypeKind::BigIntLiteral(_)
        | TypeKind::Symbol
        | TypeKind::UniqueSymbol
        | TypeKind::Unknown
        | TypeKind::Any
    ) {
      return None;
    }
    Some(expanded)
  }

  /// Lib `interface Object` members (`hasOwnProperty`, `toString`, …).
  ///
  /// Global `Object` / `{}` lower to [`TypeKind::EmptyObject`] for assignability;
  /// property access must still see Object's methods (tsc apparent type).
  pub(crate) fn object_interface_type(&self) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&["Object".to_string()])?;
    let ref_ty = self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: Vec::new(),
    }));
    let expanded = self.expand_ref(ref_ty);
    match self.store.type_kind(expanded) {
      // Must be a real object/intersection shape — not the EmptyObject shortcut.
      TypeKind::Object(_) | TypeKind::Intersection(_) => Some(expanded),
      _ => None,
    }
  }

  pub(crate) fn member_type(&mut self, obj: TypeId, prop: &str) -> TypeId {
    let prim = self.store.primitive_ids();
    // Lexically-resolved private identifiers (`#x`) shadow same-spelled slots
    // from base classes; resolve the brand before structural lookup.
    if prop.starts_with('#') {
      if let Some(ty) = self.lexical_private_member_type(obj, prop) {
        return ty;
      }
    }
    let obj = self.expand_ref(obj);
    match self.store.type_kind(obj) {
      // tsc: property access on `any` stays `any` (not `unknown`).
      TypeKind::Any => prim.any,
      // `expand_ref` above follows any resolvable references with a local
      // cycle guard. If we still have a `Ref`, treat it as unknown to avoid
      // infinitely recursing on self-referential expansions (e.g. during
      // in-progress type computation).
      TypeKind::Ref { .. } => prim.unknown,
      // tsc: every function value has `Function`'s members. We special-case the
      // high-traffic ones on bare `Callable` types (lib `interface Function`
      // may be absent under `noLib` / sparse lib sets):
      // - `call` → a method type derived from the callable's own signatures
      // - `prototype` → `any` (lib.es5: `prototype: any`)
      TypeKind::Callable { .. } if prop == "call" => {
        let sigs = callable_signatures(self.store.as_ref(), obj);
        if sigs.is_empty() {
          prim.unknown
        } else {
          self.build_call_method_type(sigs)
        }
      }
      TypeKind::Callable { .. } if prop == "prototype" => prim.any,
      TypeKind::EmptyObject => {
        if let Some(iface) = self.object_interface_type() {
          let looked = self.member_type(iface, prop);
          if looked != prim.unknown {
            return looked;
          }
        }
        prim.unknown
      }
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for candidate in shape.properties.iter() {
          match &candidate.key {
            PropKey::String(name_id) => {
              if self.store.name(*name_id) == prop {
                return candidate.data.ty;
              }
            }
            PropKey::Number(num) => {
              if prop.parse::<i64>().ok() == Some(*num) {
                return candidate.data.ty;
              }
            }
            _ => {}
          }
        }
        if prop == "call" && !shape.call_signatures.is_empty() {
          return self.build_call_method_type(shape.call_signatures.clone());
        }
        let key = if let Some(idx) = parse_canonical_index_str(prop) {
          PropKey::Number(idx)
        } else {
          PropKey::String(self.store.intern_name(prop))
        };
        let mut matches = Vec::new();
        for idxer in shape.indexers.iter() {
          if crate::type_queries::indexer_accepts_key(&key, idxer.key_type, &self.store) {
            matches.push(idxer.value_type);
          }
        }
        if !matches.is_empty() {
          return if matches.len() == 1 {
            matches[0]
          } else {
            matches.sort_by(|a, b| self.store.type_cmp(*a, *b));
            matches.dedup();
            self.store.union(matches)
          };
        }
        // Own props miss: fall back to lib `Object` (interfaces / `{}` / fresh
        // literals still expose `hasOwnProperty`, etc.).
        if let Some(iface) = self.object_interface_type() {
          // Avoid recursing into the same shape when Object iface *is* this object.
          if self.store.canon(iface) != self.store.canon(obj) {
            let looked = self.member_type(iface, prop);
            if looked != prim.unknown {
              return looked;
            }
          }
        }
        prim.unknown
      }
      TypeKind::Union(members) => {
        let mut collected = Vec::new();
        for member in members {
          let ty = self.member_type(member, prop);
          if ty != prim.unknown {
            collected.push(ty);
          }
        }
        if collected.is_empty() {
          prim.unknown
        } else {
          self.store.union(collected)
        }
      }
      TypeKind::Intersection(members) => {
        let mut collected = Vec::new();
        for member in members {
          let ty = self.member_type(member, prop);
          if ty != prim.unknown {
            collected.push(ty);
          }
        }
        if collected.is_empty() {
          prim.unknown
        } else if collected.len() == 1 {
          collected[0]
        } else {
          self.store.intersection(collected)
        }
      }
      TypeKind::Tuple(elems) => {
        if prop == "length" {
          return prim.number;
        }
        self.tuple_element_type(&elems, prop)
      }
      // Intrinsic `T[]` / `Array<T>`: `length` is number; named methods (`push`,
      // …) come from the lib `Array<T>` interface; numeric keys yield `T`.
      TypeKind::Array { ty: elem_ty, .. } => {
        if prop == "length" {
          return prim.number;
        }
        if let Some(iface) = self.array_interface_type(elem_ty) {
          let looked = self.member_type(iface, prop);
          if looked != prim.unknown {
            return looked;
          }
        }
        if parse_canonical_index_str(prop).is_some() {
          elem_ty
        } else {
          prim.unknown
        }
      }
      TypeKind::String
      | TypeKind::StringLiteral(_)
      | TypeKind::Number
      | TypeKind::NumberLiteral(_)
      | TypeKind::Boolean
      | TypeKind::BooleanLiteral(_)
      | TypeKind::BigInt
      | TypeKind::BigIntLiteral(_)
      | TypeKind::Symbol
      | TypeKind::UniqueSymbol => {
        if let Some(iface) = self.primitive_interface_type(obj) {
          self.member_type(iface, prop)
        } else {
          prim.unknown
        }
      }
      _ => prim.unknown,
    }
  }

  /// Whether `prop` is a read-only property on `obj` for assignment (TS2540).
  ///
  /// - Object: the property's `readonly` flag
  /// - Union: readonly if any arm is readonly (writable only if all are)
  /// - Intersection: readonly only if every arm that declares it is readonly
  pub(crate) fn member_is_readonly(&mut self, obj: TypeId, prop: &str) -> bool {
    self.member_readonly_flag(obj, prop).unwrap_or_default()
  }

  fn member_readonly_flag(&mut self, obj: TypeId, prop: &str) -> Option<bool> {
    let obj = self.expand_ref(obj);
    match self.store.type_kind(obj) {
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for candidate in shape.properties.iter() {
          let matches = match &candidate.key {
            PropKey::String(name_id) => self.store.name(*name_id) == prop,
            PropKey::Number(num) => prop.parse::<i64>().ok() == Some(*num),
            _ => false,
          };
          if matches {
            return Some(candidate.data.readonly);
          }
        }
        None
      }
      TypeKind::Union(members) => {
        let mut saw = false;
        let mut any_readonly = false;
        for member in members {
          if let Some(ro) = self.member_readonly_flag(member, prop) {
            saw = true;
            any_readonly |= ro;
          }
        }
        saw.then_some(any_readonly)
      }
      TypeKind::Intersection(members) => {
        let mut flags = Vec::new();
        for member in members {
          if let Some(ro) = self.member_readonly_flag(member, prop) {
            flags.push(ro);
          }
        }
        if flags.is_empty() {
          None
        } else {
          Some(flags.iter().all(|ro| *ro))
        }
      }
      TypeKind::Ref { .. } => None,
      _ => None,
    }
  }

  /// Instance getter-only accessor on the class currently being initialized.
  fn is_getter_only_instance_accessor(&self, prop: &str) -> bool {
    let Some(class_index) = self.class_initialization_index() else {
      return false;
    };
    let Some(info) = self.index.classes.get(class_index) else {
      return false;
    };
    info.instance_getters.contains(prop) && !info.instance_setters.contains(prop)
  }

  /// Whether `prop` is a setter-only private accessor (`set #x` without `get #x`)
  /// declared on the lexically enclosing class (or, failing that, any class in
  /// this file that declares the name).
  fn is_setter_only_private_accessor(&self, prop: &str) -> bool {
    if !prop.starts_with('#') {
      return false;
    }
    let class_is_setter_only = |idx: usize| -> Option<bool> {
      let info = self.index.classes.get(idx)?;
      let has_setter = info.instance_setters.contains(prop) || info.static_setters.contains(prop);
      let has_getter = info.instance_getters.contains(prop) || info.static_getters.contains(prop);
      if !has_setter && !has_getter {
        return None;
      }
      Some(has_setter && !has_getter)
    };
    if let Some(idx) = self.enclosing_class_index {
      if let Some(setter_only) = class_is_setter_only(idx) {
        return setter_only;
      }
    }
    for idx in 0..self.index.classes.len() {
      if let Some(setter_only) = class_is_setter_only(idx) {
        return setter_only;
      }
    }
    false
  }

  /// Whether `prop` is a private method (`#m() {}`) declared on the lexically
  /// enclosing class (tsc `lookupSymbolForPrivateIdentifierDeclaration` +
  /// `isMethodDeclaration`). Falls back to any class in this file that declares
  /// the name so nested / anonymous class edge cases still fire.
  fn is_private_method(&self, prop: &str) -> bool {
    if !prop.starts_with('#') {
      return false;
    }
    if let Some(idx) = self.enclosing_class_index {
      if let Some(info) = self.index.classes.get(idx) {
        if info.private_methods.contains(prop) {
          return true;
        }
      }
    }
    self
      .index
      .classes
      .iter()
      .any(|info| info.private_methods.contains(prop))
  }

  /// Emit TS2803 when assigning to a private method. Returns `true` when a
  /// diagnostic was emitted. Unlike TS2540, callers must **not** skip the
  /// ordinary type-mismatch check — tsc reports both when applicable.
  pub(crate) fn check_assign_to_private_method(
    &mut self,
    prop: &str,
    prop_span: TextRange,
  ) -> bool {
    if !self.is_private_method(prop) {
      return false;
    }
    self
      .diagnostics
      .push(codes::CANNOT_ASSIGN_PRIVATE_METHOD.error(
        format!("Cannot assign to private method '{prop}'. Private methods are not writable."),
        Span {
          file: self.file,
          range: prop_span,
        },
      ));
    true
  }

  /// Emit TS2806 when reading a setter-only private accessor.
  pub(crate) fn check_private_write_only_accessor_read(
    &mut self,
    prop: &str,
    access_span: TextRange,
  ) {
    if !self.is_setter_only_private_accessor(prop) {
      return;
    }
    self
      .diagnostics
      .push(codes::PRIVATE_ACCESSOR_NO_GETTER.error(
        "Private accessor was defined without a getter.",
        Span {
          file: self.file,
          range: access_span,
        },
      ));
  }

  /// Whether `ty` has an own/named property `prop` (ignores index signatures).
  /// Used for private-identifier visibility (TS18013/TS18014) where an indexer
  /// must not count as "property on type".
  fn type_has_named_prop(&self, ty: TypeId, prop: &str) -> bool {
    fn inner(checker: &Checker<'_>, ty: TypeId, prop: &str, seen: &mut HashSet<TypeId>) -> bool {
      let ty = checker.store.canon(ty);
      if !seen.insert(ty) {
        return false;
      }
      let expanded = checker.expand_for_props(ty);
      if expanded != ty {
        return inner(checker, expanded, prop, seen);
      }
      let ty = checker.expand_ref(ty);
      if ty != expanded {
        return inner(checker, ty, prop, seen);
      }
      match checker.store.type_kind(ty) {
        TypeKind::Object(obj_id) => {
          let shape = checker.store.shape(checker.store.object(obj_id).shape);
          for candidate in shape.properties.iter() {
            match candidate.key {
              PropKey::String(name_id) => {
                if checker.store.name(name_id) == prop {
                  return true;
                }
              }
              PropKey::Number(num) => {
                if prop.parse::<i64>().ok() == Some(num) {
                  return true;
                }
              }
              _ => {}
            }
          }
          false
        }
        TypeKind::Union(members) | TypeKind::Intersection(members) => members
          .iter()
          .copied()
          .any(|member| inner(checker, member, prop, seen)),
        TypeKind::Ref { .. } => false,
        _ => false,
      }
    }
    let mut seen = HashSet::new();
    inner(self, ty, prop, &mut seen)
  }

  /// Best-effort nominal class for `ty` (instance or constructor / `typeof`).
  pub(crate) fn nominal_class_index_for_type(&mut self, ty: TypeId) -> Option<usize> {
    let ty = self.expand_ref(self.expand_for_props(ty));
    match self.store.type_kind(ty) {
      TypeKind::Intersection(members) => {
        let mut indices = Vec::new();
        for member in members {
          if let Some(idx) = self.nominal_class_index_for_type(member) {
            if !indices.contains(&idx) {
              indices.push(idx);
            }
          }
        }
        self.most_derived_class_index(&indices)
      }
      TypeKind::Union(members) => {
        // Prefer a single shared class when all arms agree.
        let mut indices = Vec::new();
        for member in members {
          if let Some(idx) = self.nominal_class_index_for_type(member) {
            if !indices.contains(&idx) {
              indices.push(idx);
            }
          }
        }
        if indices.len() == 1 {
          Some(indices[0])
        } else {
          None
        }
      }
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        let ty_canon = self.store.canon(ty);
        if !shape.construct_signatures.is_empty() {
          for idx in 0..self.index.classes.len() {
            if let Some(static_ty) = self.resolve_static_this_type(idx) {
              if self.store.canon(static_ty) == ty_canon {
                return Some(idx);
              }
            }
          }
        }
        for idx in 0..self.index.classes.len() {
          if let Some(inst_ty) = self.resolve_instance_this_type(idx) {
            if self.store.canon(inst_ty) == ty_canon {
              return Some(idx);
            }
          }
        }
        // Derived-class instances are intersections (`B & A`): an own-shape
        // member of the intersection never equals the class's full instance
        // type, so also accept membership in the instance intersection —
        // otherwise the nominal falls back to the *base* class and
        // `this.#priv` in the derived class mis-brands as the base's private
        // (`privateNamesAndMethods`).
        for idx in 0..self.index.classes.len() {
          if let Some(inst_ty) = self.resolve_instance_this_type(idx) {
            if let TypeKind::Intersection(members) = self.store.type_kind(self.store.canon(inst_ty))
            {
              if members.contains(&ty_canon) {
                return Some(idx);
              }
            }
          }
        }
        self.nominal_class_index_from_name_binding(ty_canon)
      }
      _ => {
        let ty_canon = self.store.canon(ty);
        self.nominal_class_index_from_name_binding(ty_canon)
      }
    }
  }

  /// Resolve a class index from a value-namespace binding whose ctor/instance
  /// matches `ty_canon`. When multiple classes share a spelling (`class Inner`
  /// expressions in different outer classes), prefer the homonym on the
  /// lexical parent chain from [`Self::enclosing_class_index`] instead of the
  /// first `classes_by_name` entry (avoids false TS18013).
  fn nominal_class_index_from_name_binding(&self, ty_canon: TypeId) -> Option<usize> {
    let mut matched_names: Vec<String> = Vec::new();
    let mut seen_names = HashSet::new();
    for class in self.index.classes.iter() {
      let Some(name) = class.name.as_ref() else {
        continue;
      };
      if !seen_names.insert(name.clone()) {
        continue;
      }
      let Some(binding) = self.lookup(name) else {
        continue;
      };
      let matches = self.store.canon(binding.ty) == ty_canon
        || self
          .instance_type_from_constructor_value(binding.ty)
          .is_some_and(|inst| self.store.canon(inst) == ty_canon);
      if matches {
        matched_names.push(name.clone());
      }
    }
    for name in matched_names {
      let homonyms: Vec<usize> = self
        .index
        .classes
        .iter()
        .enumerate()
        .filter(|(_, c)| c.name.as_deref() == Some(name.as_str()))
        .map(|(i, _)| i)
        .collect();
      if homonyms.len() == 1 {
        return Some(homonyms[0]);
      }
      if let Some(enc) = self.enclosing_class_index {
        let mut current = Some(enc);
        let mut visited = HashSet::new();
        while let Some(idx) = current.take() {
          if !visited.insert(idx) {
            break;
          }
          if homonyms.contains(&idx) {
            return Some(idx);
          }
          current = self
            .index
            .classes
            .get(idx)
            .and_then(|c| c.parent_class_index);
        }
      }
      if let Some(&idx) = self.index.classes_by_name.get(&name) {
        return Some(idx);
      }
    }
    None
  }

  fn most_derived_class_index(&self, indices: &[usize]) -> Option<usize> {
    if indices.is_empty() {
      return None;
    }
    if indices.len() == 1 {
      return Some(indices[0]);
    }
    for &idx in indices {
      let Some(extends) = self.index.classes.get(idx).and_then(|c| c.extends.as_ref()) else {
        continue;
      };
      if let Some(&base_idx) = self.index.classes_by_name.get(extends) {
        if indices.contains(&base_idx) {
          return Some(idx);
        }
      }
    }
    Some(indices[0])
  }

  /// Resolve which class's private `prop` is present on `left_ty` (tsc
  /// `checkPrivateIdentifierPropertyAccess` / heritage walk).
  ///
  /// When `allow_unique_fallback` is false, skip the file-local unique-declarer
  /// fallback (needed so foreign `import("./b").Foo` brands are not attributed
  /// to the enclosing class).
  /// Whether `ty` is the *static side* of a class (a `typeof C` value:
  /// callable/constructable), as opposed to an instance. Static private names
  /// do not participate in heritage (tsc `checkPrivateIdentifierPropertyAccess`
  /// treats `B.#x` as B's own private only).
  fn is_static_class_receiver(&mut self, ty: TypeId) -> bool {
    let ty = self.expand_ref(self.expand_for_props(ty));
    let static_side = match self.store.type_kind(ty) {
      TypeKind::Callable { .. } => true,
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        !shape.construct_signatures.is_empty()
      }
      _ => false,
    };
    static_side && self.nominal_class_index_for_type(ty).is_some()
  }

  fn private_declarer_on_type(
    &mut self,
    left_ty: TypeId,
    prop: &str,
    allow_unique_fallback: bool,
  ) -> Option<usize> {
    if !self.type_has_named_prop(left_ty, prop) {
      return None;
    }
    if let Some(cls) = self.nominal_class_index_for_type(left_ty) {
      if let Some(decl) = self.index.private_declarer_in_heritage(cls, prop) {
        return Some(decl);
      }
    }
    if !allow_unique_fallback {
      return None;
    }
    // Fallback: unique declarer in this file (covers anonymous class expressions).
    let mut unique: Option<usize> = None;
    for idx in 0..self.index.classes.len() {
      if self.index.class_declares_private_name(idx, prop) {
        if unique.is_some() {
          return None;
        }
        unique = Some(idx);
      }
    }
    unique
  }

  /// `declared_on` brand for a private property on `ty` (HIR class shapes).
  fn private_prop_declared_on(&mut self, ty: TypeId, prop: &str) -> Option<DefId> {
    fn inner(
      checker: &mut Checker<'_>,
      ty: TypeId,
      prop: &str,
      seen: &mut HashSet<TypeId>,
    ) -> Option<DefId> {
      let ty = checker.store.canon(ty);
      if !seen.insert(ty) {
        return None;
      }
      let expanded = checker.expand_for_props(ty);
      if expanded != ty {
        return inner(checker, expanded, prop, seen);
      }
      let ty = checker.expand_ref(ty);
      if ty != expanded {
        return inner(checker, ty, prop, seen);
      }
      match checker.store.type_kind(ty) {
        TypeKind::Object(obj_id) => {
          let shape = checker.store.shape(checker.store.object(obj_id).shape);
          for candidate in shape.properties.iter() {
            let PropKey::String(name_id) = candidate.key else {
              continue;
            };
            if checker.store.name(name_id) != prop {
              continue;
            }
            if candidate.data.accessibility != Some(Accessibility::Private) {
              continue;
            }
            return candidate.data.declared_on;
          }
          None
        }
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          let mut found: Option<DefId> = None;
          for member in members {
            if let Some(def) = inner(checker, member, prop, seen) {
              if found.is_some_and(|f| f != def) {
                return None;
              }
              found = Some(def);
            }
          }
          found
        }
        _ => None,
      }
    }
    let mut seen = HashSet::new();
    inner(self, ty, prop, &mut seen)
  }

  /// Lexical enclosing class's private brand for `prop` (`declared_on` DefId).
  fn lexical_private_declared_on(&mut self, prop: &str) -> Option<DefId> {
    let idx = self
      .index
      .lookup_lexical_private_class(self.enclosing_class_index, prop)?;
    let info = self.index.classes.get(idx)?;
    let is_static = info.static_fields.iter().any(|f| f.name == prop)
      || info.static_methods.iter().any(|m| m == prop)
      || info.static_getters.contains(prop)
      || info.static_setters.contains(prop);
    let side = if is_static {
      self.resolve_static_this_type(idx)
    } else {
      self.resolve_instance_this_type(idx)
    };
    if let Some(side) = side {
      if let Some(def) = self.private_prop_declared_on(side, prop) {
        return Some(def);
      }
    }
    // Class expressions: binding lookup may yield a synthesized shape without
    // `declared_on`; prefer the HIR constructor value type for the class span.
    let class_span = self.index.classes.get(idx)?.span;
    let ctor = *self.class_expr_value_tys.get(&class_span)?;
    let side = if is_static {
      ctor
    } else {
      self.instance_type_from_constructor_value(ctor)?
    };
    self.private_prop_declared_on(side, prop)
  }

  /// tsc: a private identifier (`#x`) resolves lexically to the nearest
  /// enclosing class declaring that name — a derived class redeclaring `#x`
  /// shadows the base's slot for accesses in its scope, so the access type is
  /// the *derived* declaration's type (`privateNamesAndFields`). Field-like
  /// declarations resolve from the lexical class's own declaration; methods
  /// and accessors keep structural resolution (intersected signatures behave
  /// like an overload set for calls).
  ///
  /// Only fires when the receiver can carry two same-spelled slots (an
  /// ancestor of the lexical class also declares the name) — without
  /// shadowing, the structural path is equally correct and better informed
  /// (it refines unannotated field types from their initializers).
  pub(crate) fn lexical_private_member_type(&mut self, obj: TypeId, prop: &str) -> Option<TypeId> {
    if !prop.starts_with('#') {
      return None;
    }
    let idx = self
      .index
      .lookup_lexical_private_class(self.enclosing_class_index, prop)?;
    let info = self.index.classes.get(idx)?;
    // Shadowing gate: some base class of `idx` must also declare `prop`.
    let base_idx = info
      .extends
      .as_ref()
      .and_then(|name| self.index.classes_by_name.get(name))
      .copied();
    let shadowed = base_idx
      .and_then(|base| self.index.private_declarer_in_heritage(base, prop))
      .is_some();
    if !shadowed {
      return None;
    }
    let info = self.index.classes.get(idx)?;
    // Instance vs static side: constructor-typed receivers (`typeof C`, e.g.
    // `this` in static members) read the static declaration.
    let obj = self.expand_ref(obj);
    let static_side = match self.store.type_kind(obj) {
      TypeKind::Object(obj_id) => !self
        .store
        .shape(self.store.object(obj_id).shape)
        .construct_signatures
        .is_empty(),
      _ => false,
    };
    let has_field = if static_side {
      info.static_fields.iter().any(|f| f.name == prop)
    } else {
      info.instance_fields.iter().any(|f| f.name == prop)
    };
    if !has_field {
      return None;
    }
    self.class_field_inferred_type_for(idx, prop)
  }

  /// Emit TS18013 / TS18014 / TS18016 / TS18030 / TS18046 / TS2339 for illegal
  /// private-identifier property access. Primary span is the private name
  /// (`#x`) except TS18046 (receiver expression), matching tsc.
  pub(crate) fn check_private_identifier_property_access(
    &mut self,
    left_ty: TypeId,
    left_expr: Option<&Node<AstExpr>>,
    prop: &str,
    prop_span: TextRange,
    optional_chain: bool,
  ) {
    if !prop.starts_with('#') {
      return;
    }
    // tsc parser: optional chain + PrivateIdentifier → TS18030 (before
    // semantic visibility / nonexistent-property diagnostics).
    if optional_chain {
      self
        .diagnostics
        .push(codes::OPTIONAL_CHAIN_PRIVATE_IDENTIFIER.error(
          "An optional chain cannot contain private identifiers.",
          Span {
            file: self.file,
            range: prop_span,
          },
        ));
      return;
    }
    let prim = self.store.primitive_ids();
    let left = self.expand_ref(left_ty);
    let lexical = self
      .index
      .lookup_lexical_private_class(self.enclosing_class_index, prop);
    // tsc `checkNonNullType`: entity-name `unknown` under strictNullChecks →
    // TS18046 on the receiver. After that, recovery is `errorType`/`any`:
    // declared lexical privates are allowed; undeclared → TS2339.
    //
    // Skip for `this`/`super` inside a class member: when contextual `this` was
    // not seeded (initializer body edge cases), tsc still does not emit TS2571
    // on `this.#priv` in field initializers.
    let skip_unknown_receiver = left_expr.is_some_and(|e| {
      matches!(e.stx.as_ref(), AstExpr::This(_) | AstExpr::Super(_))
        && self.enclosing_class_index.is_some()
    });
    // `this.#priv` with an unseeded `this: unknown` inside a class: allow
    // lexically declared privates (no TS2571/TS2339); undeclared still TS2339
    // via the normal path below once recovered.
    if left == prim.unknown && skip_unknown_receiver {
      if lexical.is_some() {
        return;
      }
    }
    if self.strict_null_checks && left == prim.unknown && !skip_unknown_receiver {
      // A `this.<unannotated field>` receiver may refine from its initializer
      // (e.g. `otherClass = A` — tsc infers `typeof A`): recover before
      // flagging TS2571 on the would-be-unknown receiver
      // (`privateNameStaticFieldDestructuredBinding`).
      if let Some(AstExpr::Member(mem)) = left_expr.map(|e| e.stx.as_ref()) {
        if let Some(recovered) = self.class_field_inferred_type(&mem.stx.right) {
          if self.store.canon(recovered) != prim.unknown {
            return self.check_private_identifier_property_access(
              recovered,
              left_expr,
              prop,
              prop_span,
              optional_chain,
            );
          }
        }
      }
      if let Some(expr) = left_expr {
        if let Some(name) = Self::expr_display_name(expr) {
          if name.len() < 100 {
            self.diagnostics.push(codes::IS_OF_TYPE_UNKNOWN.error(
              format!("'{name}' is of type 'unknown'."),
              Span {
                file: self.file,
                range: loc_to_range(self.file, expr.loc),
              },
            ));
          } else {
            self
              .diagnostics
              .push(codes::OBJECT_IS_OF_TYPE_UNKNOWN.error(
                "Object is of type 'unknown'.",
                Span {
                  file: self.file,
                  range: loc_to_range(self.file, expr.loc),
                },
              ));
          }
        } else {
          self
            .diagnostics
            .push(codes::OBJECT_IS_OF_TYPE_UNKNOWN.error(
              "Object is of type 'unknown'.",
              Span {
                file: self.file,
                range: loc_to_range(self.file, expr.loc),
              },
            ));
        }
      }
      if lexical.is_some() {
        return;
      }
      if self.enclosing_class_index.is_none() {
        self
          .diagnostics
          .push(codes::PRIVATE_IDENTIFIERS_OUTSIDE_CLASS.error(
            "Private identifiers are not allowed outside class bodies.",
            Span {
              file: self.file,
              range: prop_span,
            },
          ));
        return;
      }
      self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
        format!(
          "Property '{prop}' does not exist on type '{}'.",
          TypeDisplay::new(self.store.as_ref(), left_ty)
        ),
        Span {
          file: self.file,
          range: prop_span,
        },
      ));
      return;
    }
    // tsc any-like branch for private names:
    // - `any` + lexical private → allow
    // - `any` + no lexical, outside class → TS18016
    // - `any` + no lexical, inside class → TS2339
    // - `never` → always TS2339 (`reportNonexistentProperty`); do not treat as
    //   any-like allow (privateNameAndAny methodN).
    // Unresolved names recover as `any` (tsc errorType), so `exports.#x` hits this.
    if left == prim.any {
      if lexical.is_some() {
        return;
      }
      if self.enclosing_class_index.is_none() {
        self
          .diagnostics
          .push(codes::PRIVATE_IDENTIFIERS_OUTSIDE_CLASS.error(
            "Private identifiers are not allowed outside class bodies.",
            Span {
              file: self.file,
              range: prop_span,
            },
          ));
        return;
      }
      self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
        format!(
          "Property '{prop}' does not exist on type '{}'.",
          TypeDisplay::new(self.store.as_ref(), left_ty)
        ),
        Span {
          file: self.file,
          range: prop_span,
        },
      ));
      return;
    }
    if left == prim.never {
      self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
        format!(
          "Property '{prop}' does not exist on type '{}'.",
          TypeDisplay::new(self.store.as_ref(), left_ty)
        ),
        Span {
          file: self.file,
          range: prop_span,
        },
      ));
      return;
    }
    if !self.type_has_named_prop(left_ty, prop) {
      // tsc: `checkPrivateIdentifierPropertyAccess` returns false →
      // `reportNonexistentProperty` (TS2339). Index signatures do not apply to
      // private identifiers.
      //
      // Setter-only private accessors *exist* for visibility purposes; reading
      // one is TS2806 ("defined without a getter", already emitted by the
      // caller), not TS2339 (`privateNameSetterNoGetter.ts`).
      if !self.is_setter_only_private_accessor(prop) {
        self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
          format!(
            "Property '{prop}' does not exist on type '{}'.",
            TypeDisplay::new(self.store.as_ref(), left_ty)
          ),
          Span {
            file: self.file,
            range: prop_span,
          },
        ));
      }
      return;
    }

    // Prefer nominal AstIndex matching (no unique-declarer fallback). The
    // unique fallback mis-attributes foreign `import("./b").Foo` types to the
    // enclosing class when both declare `#x`.
    let type_brand = self.private_prop_declared_on(left_ty, prop);
    let lexical_brand = self.lexical_private_declared_on(prop);
    if let Some(type_declarer) = self.private_declarer_on_type(left_ty, prop, false) {
      if lexical == Some(type_declarer) {
        return;
      }
      // tsc: the private name resolves lexically; the access is still allowed
      // when the receiver's nearest declarer *derives from* the lexical
      // declarer — the receiver carries the lexical private in its heritage.
      // (`b.#foo` inside class `A` with `b: B extends A` and B shadowing
      // `#foo`: tsc allows it.)
      //
      // Instances only: static private names do not participate in heritage —
      // `typeof B` carries no inherited static privates, so `B.#foo` targets
      // B's *own* private and the heritage rule must not allow it
      // (`privateNamesAndStaticFields.ts` → TS18013).
      if let Some(lex) = lexical {
        if !self.is_static_class_receiver(left_ty)
          && self.index.class_extends_chain_includes(type_declarer, lex)
        {
          return;
        }
      }
      let class_name = self.index.class_diagnostic_name(type_declarer);
      if let Some(lex) = lexical {
        if self.index.class_is_nested_in(lex, type_declarer) && lex != type_declarer {
          self.diagnostics.push(codes::PRIVATE_IDENTIFIER_SHADOWED.error(
            format!(
              "The property '{prop}' cannot be accessed on type '{}' within this class because it is shadowed by another private identifier with the same spelling.",
              TypeDisplay::new(self.store.as_ref(), left_ty)
            ),
            Span {
              file: self.file,
              range: prop_span,
            },
          ));
          return;
        }
      }
      self
        .diagnostics
        .push(codes::PRIVATE_IDENTIFIER_NOT_ACCESSIBLE.error(
          format!(
            "Property '{prop}' is not accessible outside class '{class_name}' because it has a private identifier."
          ),
          Span {
            file: self.file,
            range: prop_span,
          },
        ));
      return;
    }

    // No nominal local class: use `declared_on` DefId brands (cross-file).
    if let (Some(type_def), Some(lex_def)) = (type_brand, lexical_brand) {
      if type_def == lex_def {
        return;
      }
      // Same-file type/value DefId skew (class expressions): allow when the
      // receiver brand is not from another file. Cross-file `import()` brands
      // have a different `def_file` and stay TS18013.
      let foreign = self
        .type_resolver
        .as_ref()
        .and_then(|r| r.def_file(type_def))
        .is_some_and(|f| f != self.file);
      if !foreign {
        if lexical.is_some_and(|idx| self.index.class_declares_private_name(idx, prop)) {
          return;
        }
      }
      self
        .diagnostics
        .push(codes::PRIVATE_IDENTIFIER_NOT_ACCESSIBLE.error(
          format!(
            "Property '{prop}' is not accessible outside class 'Object' because it has a private identifier."
          ),
          Span {
            file: self.file,
            range: prop_span,
          },
        ));
      return;
    }
    if type_brand.is_some() && lexical_brand.is_none() {
      // Foreign branded private; no lexical brand (outside class, or
      // class-expression initializers without HIR brands on the lexical side).
      if lexical.is_none() {
        self
          .diagnostics
          .push(codes::PRIVATE_IDENTIFIER_NOT_ACCESSIBLE.error(
            format!(
              "Property '{prop}' is not accessible outside class 'Object' because it has a private identifier."
            ),
            Span {
              file: self.file,
              range: prop_span,
            },
          ));
        return;
      }
      // Inside a class that declares `prop` but lacks a DefId brand: allow via
      // unique local declarer (class expressions).
      if let Some(type_declarer) = self.private_declarer_on_type(left_ty, prop, true) {
        if lexical == Some(type_declarer) {
          return;
        }
        let class_name = self.index.class_diagnostic_name(type_declarer);
        self
          .diagnostics
          .push(codes::PRIVATE_IDENTIFIER_NOT_ACCESSIBLE.error(
            format!(
              "Property '{prop}' is not accessible outside class '{class_name}' because it has a private identifier."
            ),
            Span {
              file: self.file,
              range: prop_span,
            },
          ));
        return;
      }
      if lexical.is_some_and(|idx| self.index.class_declares_private_name(idx, prop)) {
        return;
      }
      self
        .diagnostics
        .push(codes::PRIVATE_IDENTIFIER_NOT_ACCESSIBLE.error(
          format!(
            "Property '{prop}' is not accessible outside class 'Object' because it has a private identifier."
          ),
          Span {
            file: self.file,
            range: prop_span,
          },
        ));
      return;
    }

    // Unbranded shapes: unique local declarer fallback (anonymous class exprs).
    let Some(type_declarer) = self.private_declarer_on_type(left_ty, prop, true) else {
      self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
        format!(
          "Property '{prop}' does not exist on type '{}'.",
          TypeDisplay::new(self.store.as_ref(), left_ty)
        ),
        Span {
          file: self.file,
          range: prop_span,
        },
      ));
      return;
    };
    if lexical == Some(type_declarer) {
      return;
    }
    let class_name = self.index.class_diagnostic_name(type_declarer);
    if let Some(lex) = lexical {
      if self.index.class_is_nested_in(lex, type_declarer) && lex != type_declarer {
        self.diagnostics.push(codes::PRIVATE_IDENTIFIER_SHADOWED.error(
          format!(
            "The property '{prop}' cannot be accessed on type '{}' within this class because it is shadowed by another private identifier with the same spelling.",
            TypeDisplay::new(self.store.as_ref(), left_ty)
          ),
          Span {
            file: self.file,
            range: prop_span,
          },
        ));
        return;
      }
    }
    self
      .diagnostics
      .push(codes::PRIVATE_IDENTIFIER_NOT_ACCESSIBLE.error(
        format!(
          "Property '{prop}' is not accessible outside class '{class_name}' because it has a private identifier."
        ),
        Span {
          file: self.file,
          range: prop_span,
        },
      ));
  }

  /// Whether `op` is a compound assignment that must read the LHS (tsc
  /// `AssignmentKind.Compound`). Logical / nullish assignments are definite
  /// writes for this purpose.
  fn is_compound_assignment_op(op: OperatorName) -> bool {
    matches!(
      op,
      OperatorName::AssignmentAddition
        | OperatorName::AssignmentSubtraction
        | OperatorName::AssignmentMultiplication
        | OperatorName::AssignmentDivision
        | OperatorName::AssignmentRemainder
        | OperatorName::AssignmentExponentiation
        | OperatorName::AssignmentBitwiseAnd
        | OperatorName::AssignmentBitwiseOr
        | OperatorName::AssignmentBitwiseXor
        | OperatorName::AssignmentBitwiseLeftShift
        | OperatorName::AssignmentBitwiseRightShift
        | OperatorName::AssignmentBitwiseUnsignedRightShift
    )
  }

  /// Check a `++` / `--` target: walk into the member and emit TS2806 when it
  /// reads a setter-only private accessor, and TS2803 when writing a private method.
  fn check_compound_update_target(&mut self, target: &Node<AstExpr>) {
    match target.stx.as_ref() {
      AstExpr::Member(mem) => {
        let full_range = loc_to_range(self.file, mem.loc);
        let prop_len = mem.stx.right.len() as u32;
        let prop_span = TextRange::new(full_range.end.saturating_sub(prop_len), full_range.end);
        self.check_private_write_only_accessor_read(&mem.stx.right, full_range);
        let obj_ty = self.check_expr(&mem.stx.left);
        let optional_chain =
          mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.left);
        self.check_private_identifier_property_access(
          obj_ty,
          Some(&mem.stx.left),
          &mem.stx.right,
          prop_span,
          optional_chain,
        );
        let _ = self.check_assign_to_private_method(&mem.stx.right, prop_span);
      }
      _ => {
        let _ = self.check_expr(target);
      }
    }
  }

  /// Type-check an assignment-pattern target (`Pat::AssignTarget`) without
  /// treating a top-level private member access as a read. Nested reads on the
  /// object side (`this.#x.prop`) still go through [`Self::check_expr`] and may
  /// emit TS2806.
  pub(crate) fn check_assign_target_expr(&mut self, expr: &Node<AstExpr>) -> TypeId {
    match expr.stx.as_ref() {
      AstExpr::Member(mem) => {
        let full_range = loc_to_range(self.file, mem.loc);
        let prop_len = mem.stx.right.len() as u32;
        let prop_span = TextRange::new(full_range.end.saturating_sub(prop_len), full_range.end);
        self.check_abstract_property_in_constructor(&mem.stx.left, &mem.stx.right, prop_span);
        self.check_property_not_used_before_initialization(
          &mem.stx.left,
          &mem.stx.right,
          full_range,
        );
        let obj_ty = self.check_expr(&mem.stx.left);
        let optional_chain =
          mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.left);
        self.check_private_identifier_property_access(
          obj_ty,
          Some(&mem.stx.left),
          &mem.stx.right,
          prop_span,
          optional_chain,
        );
        let _ = self.check_assign_to_private_method(&mem.stx.right, prop_span);
        let _ =
          self.check_assign_to_readonly_property(&mem.stx.left, obj_ty, &mem.stx.right, prop_span);
        self.member_type(obj_ty, &mem.stx.right)
      }
      AstExpr::ComputedMember(mem) => {
        let obj_ty = self.check_expr(&mem.stx.object);
        let key_ty = self.check_expr(&mem.stx.member);
        let prop = match mem.stx.member.stx.as_ref() {
          AstExpr::LitStr(str_lit) => Some(str_lit.stx.value.clone()),
          AstExpr::LitNum(num) => Some(num.stx.value.0.to_string()),
          _ => match self.store.type_kind(key_ty) {
            TypeKind::StringLiteral(id) => Some(self.store.name(id).to_string()),
            TypeKind::NumberLiteral(num) => Some(num.0.to_string()),
            _ => None,
          },
        };
        if let Some(prop_name) = prop.as_deref() {
          let prop_span = loc_to_range(self.file, mem.stx.member.loc);
          let _ = self.check_assign_to_private_method(prop_name, prop_span);
          let _ =
            self.check_assign_to_readonly_property(&mem.stx.object, obj_ty, prop_name, prop_span);
        }
        // Assignment targets use write-indexed-access: `T[A|B]` → `T[A] & T[B]`.
        self.member_type_for_index_key(obj_ty, key_ty, /*writing*/ true)
      }
      _ => self.check_expr(expr),
    }
  }

  /// Emit TS2540 when assigning to a read-only property. Returns `true` when a
  /// diagnostic was emitted (caller should skip the ordinary type-mismatch
  /// check — tsc reports only TS2540 in that case).
  ///
  /// Constructor / instance-field-initializer `this.prop = …` may assign to
  /// `readonly` *fields*, but never to getter-only accessors.
  pub(crate) fn check_assign_to_readonly_property(
    &mut self,
    obj_expr: &Node<AstExpr>,
    obj_ty: TypeId,
    prop: &str,
    prop_span: TextRange,
  ) -> bool {
    let getter_only_this = matches!(obj_expr.stx.as_ref(), AstExpr::This(_))
      && self.is_getter_only_instance_accessor(prop);
    let readonly = getter_only_this || self.member_is_readonly(obj_ty, prop);
    if !readonly {
      return false;
    }
    let ctor_field_exempt = !getter_only_this
      && matches!(obj_expr.stx.as_ref(), AstExpr::This(_))
      && self.class_initialization_index().is_some();
    if ctor_field_exempt {
      return false;
    }
    self.diagnostics.push(codes::CANNOT_ASSIGN_READONLY.error(
      format!("Cannot assign to '{prop}' because it is a read-only property."),
      Span {
        file: self.file,
        range: prop_span,
      },
    ));
    true
  }

  pub(crate) fn type_has_prop(&self, ty: TypeId, prop: &str) -> bool {
    pub(crate) fn inner(
      checker: &Checker<'_>,
      ty: TypeId,
      prop: &str,
      seen: &mut HashSet<TypeId>,
    ) -> bool {
      let ty = checker.store.canon(ty);
      if !seen.insert(ty) {
        return false;
      }
      let expanded = checker.expand_for_props(ty);
      if expanded != ty {
        return inner(checker, expanded, prop, seen);
      }
      let ty = checker.expand_ref(ty);
      if ty != expanded {
        return inner(checker, ty, prop, seen);
      }
      match checker.store.type_kind(ty) {
        TypeKind::Object(obj_id) => {
          let shape = checker.store.shape(checker.store.object(obj_id).shape);
          if !shape.indexers.is_empty() {
            return true;
          }
          for candidate in shape.properties.iter() {
            match candidate.key {
              PropKey::String(name_id) => {
                if checker.store.name(name_id) == prop {
                  return true;
                }
              }
              PropKey::Number(num) => {
                if prop.parse::<i64>().ok() == Some(num) {
                  return true;
                }
              }
              _ => {}
            }
          }
          false
        }
        // Bare callables expose `Function.prototype` / synthesized `call`.
        TypeKind::Callable { .. } => prop == "prototype" || prop == "call",
        TypeKind::Union(members) | TypeKind::Intersection(members) => members
          .iter()
          .copied()
          .any(|member| inner(checker, member, prop, seen)),
        TypeKind::Ref { .. } => false,
        TypeKind::Mapped(_) => true,
        _ => false,
      }
    }

    inner(self, ty, prop, &mut HashSet::new())
  }

  /// Element type for a string/numeric property key on a tuple.
  pub(crate) fn tuple_element_type(
    &self,
    elems: &[types_ts_interned::TupleElem],
    prop: &str,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    if prop.contains('.') || prop.starts_with('-') {
      return prim.unknown;
    }
    let Ok(idx) = prop.parse::<usize>() else {
      return prim.unknown;
    };
    if let Some(elem) = elems.get(idx) {
      let mut ty = elem.ty;
      if elem.optional && !self.relate.options.exact_optional_property_types {
        ty = self.store.union(vec![ty, prim.undefined]);
      }
      return ty;
    }
    // Past the fixed prefix: use a trailing rest element when present.
    if let Some(rest) = elems.iter().rev().find(|e| e.rest) {
      return rest.ty;
    }
    prim.undefined
  }

  /// TS2493 when a numeric literal indexes past a fixed-length tuple.
  pub(crate) fn maybe_report_tuple_index_oob(
    &mut self,
    obj_ty: TypeId,
    key: &str,
    index_range: TextRange,
  ) {
    if key.contains('.') || key.starts_with('-') {
      return;
    }
    let Ok(idx) = key.parse::<usize>() else {
      return;
    };
    let obj = self.expand_ref(obj_ty);
    let TypeKind::Tuple(elems) = self.store.type_kind(obj) else {
      return;
    };
    if elems.iter().any(|e| e.rest) {
      return;
    }
    if idx < elems.len() {
      return;
    }
    let display = TypeDisplay::new(self.store.as_ref(), obj).to_string();
    let span = Span {
      file: self.file,
      range: index_range,
    };
    self
      .diagnostics
      .push(codes::TUPLE_INDEX_OUT_OF_BOUNDS.error(
        format!(
          "Tuple type '{display}' of length '{}' has no element at index '{idx}'.",
          elems.len()
        ),
        span,
      ));
  }

  /// Indexed access `obj[key]`.
  ///
  /// When `writing` is true, mirrors tsc write-indexed-access distribution:
  /// - `T[A | B]` → `T[A] & T[B]`
  /// - `(T | U)[K]` → `T[K] & U[K]`
  ///
  /// Reads use unions instead of intersections for those distributions.
  pub(crate) fn member_type_for_index_key(
    &mut self,
    obj: TypeId,
    key_ty: TypeId,
    writing: bool,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let key_ty = self.store.canon(key_ty);
    let obj = self.expand_ref(obj);

    match self.store.type_kind(key_ty) {
      TypeKind::Union(members) => {
        let mut collected = Vec::new();
        for member in members {
          collected.push(self.member_type_for_index_key(obj, member, writing));
        }
        return if writing {
          self.store.intersection(collected)
        } else {
          self.store.union(collected)
        };
      }
      TypeKind::Intersection(members) => {
        // Keep this conservative: treat intersections of key types similarly to
        // unions for distribution (each constituent key is accessed).
        let mut collected = Vec::new();
        for member in members {
          collected.push(self.member_type_for_index_key(obj, member, writing));
        }
        return if writing {
          self.store.intersection(collected)
        } else {
          self.store.union(collected)
        };
      }
      _ => {}
    }

    // Literal keys resolve through named properties (and object indexers via
    // `member_type`) before the array/tuple/indexer fallbacks below.
    if !matches!(
      self.store.type_kind(obj),
      TypeKind::Array { .. } | TypeKind::Tuple(_)
    ) {
      let literal_name = match self.store.type_kind(key_ty) {
        TypeKind::StringLiteral(id) => Some(self.store.name(id).to_string()),
        TypeKind::NumberLiteral(num) => Some(num.0.to_string()),
        _ => None,
      };
      if let Some(name) = literal_name.as_deref() {
        let named = self.member_type(obj, name);
        if named != prim.unknown {
          return named;
        }
      }
    }

    match self.store.type_kind(obj) {
      TypeKind::Union(members) => {
        let mut collected = Vec::new();
        for member in members {
          collected.push(self.member_type_for_index_key(member, key_ty, writing));
        }
        if writing {
          self.store.intersection(collected)
        } else {
          self.store.union(collected)
        }
      }
      TypeKind::Intersection(members) => {
        let mut collected = Vec::new();
        for member in members {
          collected.push(self.member_type_for_index_key(member, key_ty, writing));
        }
        self.store.intersection(collected)
      }
      TypeKind::Ref { .. } => prim.unknown,
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        let mut matches = Vec::new();
        for idx in shape.indexers.iter() {
          if self.indexer_key_matches(idx.key_type, key_ty) {
            matches.push(idx.value_type);
          }
        }
        if matches.is_empty() {
          prim.unknown
        } else if matches.len() == 1 {
          matches[0]
        } else {
          matches.sort_by(|a, b| self.store.type_cmp(*a, *b));
          matches.dedup();
          self.store.union(matches)
        }
      }
      TypeKind::Array { ty, .. } => {
        if self.relate.is_assignable(key_ty, prim.number) {
          ty
        } else {
          prim.unknown
        }
      }
      TypeKind::Tuple(elems) => match self.store.type_kind(key_ty) {
        TypeKind::NumberLiteral(num) => {
          let raw = num.0;
          if raw.fract() != 0.0 || raw < 0.0 {
            return prim.unknown;
          }
          let idx = raw as usize;
          if let Some(elem) = elems.get(idx) {
            let mut ty = elem.ty;
            if elem.optional && !self.relate.options.exact_optional_property_types {
              ty = self.store.union(vec![ty, prim.undefined]);
            }
            ty
          } else {
            prim.undefined
          }
        }
        _ => {
          if !self.relate.is_assignable(key_ty, prim.number) {
            return prim.unknown;
          }
          let mut members = Vec::new();
          for elem in elems {
            let mut ty = elem.ty;
            if elem.optional && !self.relate.options.exact_optional_property_types {
              ty = self.store.union(vec![ty, prim.undefined]);
            }
            members.push(ty);
          }
          if writing {
            self.store.intersection(members)
          } else {
            self.store.union(members)
          }
        }
      },
      _ => prim.unknown,
    }
  }

  pub(crate) fn indexer_key_matches(&self, indexer_key: TypeId, key_ty: TypeId) -> bool {
    let prim = self.store.primitive_ids();
    let key_ty = self.store.canon(key_ty);

    let dummy_name = self.store.intern_name("<index>");
    let mut candidates = Vec::new();

    match self.store.type_kind(key_ty) {
      TypeKind::String | TypeKind::StringLiteral(_) => {
        candidates.push(PropKey::String(dummy_name));
      }
      TypeKind::Number | TypeKind::NumberLiteral(_) => {
        candidates.push(PropKey::Number(0));
      }
      TypeKind::Symbol | TypeKind::UniqueSymbol => {
        candidates.push(PropKey::Symbol(dummy_name));
      }
      TypeKind::Any => {
        candidates.push(PropKey::String(dummy_name));
        candidates.push(PropKey::Number(0));
        candidates.push(PropKey::Symbol(dummy_name));
      }
      _ => {
        if self.relate.is_assignable(key_ty, prim.string) {
          candidates.push(PropKey::String(dummy_name));
        }
        if self.relate.is_assignable(key_ty, prim.number) {
          candidates.push(PropKey::Number(0));
        }
        if self.relate.is_assignable(key_ty, prim.symbol) {
          candidates.push(PropKey::Symbol(dummy_name));
        }
      }
    }

    candidates
      .into_iter()
      .any(|key| crate::type_queries::indexer_accepts_key(&key, indexer_key, &self.store))
  }

  pub(crate) fn build_call_method_type(&self, sigs: Vec<SignatureId>) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut overloads = Vec::new();
    for sig_id in sigs {
      let sig = self.store.signature(sig_id);
      let this_arg = sig.this_param.unwrap_or(prim.any);
      let mut params = Vec::with_capacity(sig.params.len() + 1);
      params.push(SigParam {
        name: None,
        ty: this_arg,
        optional: false,
        rest: false,
      });
      params.extend(sig.params.clone());
      let call_sig = Signature {
        params,
        ret: sig.ret,
        type_params: sig.type_params.clone(),
        this_param: None,
      };
      overloads.push(self.store.intern_signature(call_sig));
    }
    let mut deduped = Vec::new();
    let mut seen = HashSet::new();
    for sig_id in overloads {
      if seen.insert(sig_id) {
        deduped.push(sig_id);
      }
    }
    self
      .store
      .intern_type(TypeKind::Callable { overloads: deduped })
  }

  pub(crate) fn array_literal_context_candidates(
    &self,
    expected: TypeId,
    arity: usize,
  ) -> Vec<ArrayLiteralContext> {
    let mut queue: VecDeque<TypeId> = VecDeque::from([expected]);
    let mut seen = HashSet::new();
    let mut tuples: Vec<Vec<types_ts_interned::TupleElem>> = Vec::new();
    let mut arrays: Vec<TypeId> = Vec::new();

    while let Some(ty) = queue.pop_front() {
      if !seen.insert(ty) {
        continue;
      }
      match self.store.type_kind(ty) {
        TypeKind::Tuple(elems) => tuples.push(elems),
        TypeKind::Array { ty, .. } => arrays.push(ty),
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for member in members {
            queue.push_back(member);
          }
        }
        TypeKind::Ref { def, args } => {
          if let Some(expanded) = self
            .ref_expander
            .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
          {
            queue.push_back(expanded);
          }
        }
        _ => {}
      }
    }

    tuples.sort_by_key(|tuple| {
      let len = tuple.len();
      let diff = len.abs_diff(arity) as u32;
      (diff, len)
    });

    arrays.sort_by(|a, b| self.store.type_cmp(*a, *b));
    arrays.dedup();

    let mut out = Vec::new();
    out.extend(tuples.into_iter().map(ArrayLiteralContext::Tuple));
    out.extend(arrays.into_iter().map(ArrayLiteralContext::Array));
    out
  }

  pub(crate) fn expected_contains_primitive(&self, expected: TypeId, primitive: TypeId) -> bool {
    if expected == primitive {
      return true;
    }
    let mut queue: VecDeque<TypeId> = VecDeque::from([expected]);
    let mut seen = HashSet::new();
    while let Some(ty) = queue.pop_front() {
      if !seen.insert(ty) {
        continue;
      }
      if ty == primitive {
        return true;
      }
      match self.store.type_kind(ty) {
        TypeKind::Any => return true,
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for member in members {
            queue.push_back(member);
          }
        }
        TypeKind::Ref { def, args } => {
          if let Some(expanded) = self
            .ref_expander
            .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, &args))
          {
            queue.push_back(expanded);
          }
        }
        _ => {}
      }
    }
    false
  }

  pub(crate) fn contextual_widen_container(&self, inferred: TypeId, expected: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let should_widen = self.expected_contains_primitive(expected, prim.number)
      || self.expected_contains_primitive(expected, prim.string)
      || self.expected_contains_primitive(expected, prim.boolean)
      || self.expected_contains_primitive(expected, prim.bigint);
    if should_widen {
      self.widen_object_prop(inferred)
    } else {
      inferred
    }
  }

  pub(crate) fn spread_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let ty = self.expand_ref(ty);
    match self.store.type_kind(ty) {
      TypeKind::Any => prim.any,
      TypeKind::Unknown => prim.unknown,
      TypeKind::Union(members) => {
        let elems: Vec<_> = members
          .into_iter()
          .map(|m| self.spread_element_type(m))
          .collect();
        self.store.union(elems)
      }
      TypeKind::Intersection(members) => {
        let elems: Vec<_> = members
          .into_iter()
          .map(|m| self.spread_element_type(m))
          .collect();
        self.store.intersection(elems)
      }
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => {
        let members: Vec<_> = elems.into_iter().map(|e| e.ty).collect();
        if members.is_empty() {
          prim.unknown
        } else {
          self.store.union(members)
        }
      }
      // Strings iterate char-by-char (`[..."ab"]` is `string[]`).
      TypeKind::String | TypeKind::StringLiteral(_) => prim.string,
      // Non-array object types use the iterable protocol
      // (`[Symbol.iterator]().next().value`; `iteratorSpreadInArray7.ts`).
      _ => super::flow_ops::iterable_protocol_element(&self.store, self.ref_expander, ty)
        .unwrap_or(prim.unknown),
    }
  }

  /// Element type for a no-element array literal `[]`.
  ///
  /// Matches tsc `checkArrayLiteral`: with `strictNullChecks`, empty `[]` is
  /// `never[]`; without, it is an `undefined`-widening array (`undefined[]`).
  /// Contextual typing still accepts `never[]` where `T[]` is expected because
  /// `never` is assignable to every `T`.
  pub(crate) fn empty_array_element_type(&self) -> TypeId {
    let prim = self.store.primitive_ids();
    if self.strict_null_checks {
      prim.never
    } else {
      prim.undefined
    }
  }

  pub(crate) fn array_literal_type(
    &mut self,
    arr: &Node<parse_js::ast::expr::lit::LitArrExpr>,
  ) -> TypeId {
    let mut elems = Vec::new();
    for elem in arr.stx.elements.iter() {
      match elem {
        parse_js::ast::expr::lit::LitArrElem::Single(v) => elems.push(self.check_expr(v)),
        parse_js::ast::expr::lit::LitArrElem::Rest(v) => {
          let spread = self.check_expr(v);
          elems.push(self.spread_element_type(spread));
        }
        parse_js::ast::expr::lit::LitArrElem::Empty => {}
      }
    }
    let elem_ty = if elems.is_empty() {
      self.empty_array_element_type()
    } else {
      self.store.union(elems)
    };
    let elem_ty = if self.widen_object_literals {
      self.widen_object_prop(elem_ty)
    } else {
      elem_ty
    };
    self.store.intern_type(TypeKind::Array {
      ty: elem_ty,
      readonly: false,
    })
  }

  /// tsc infers a *tuple* for an all-single-element array literal in a
  /// destructuring position (`[x, [y]] = [1, [2]]` binds `x: number`,
  /// `y: number[]`) — the union-element array type would smear every element
  /// across every target.
  pub(crate) fn tuple_literal_type_for_destructuring(
    &mut self,
    arr: &Node<parse_js::ast::expr::lit::LitArrExpr>,
  ) -> TypeId {
    let mut elems = Vec::new();
    for elem in arr.stx.elements.iter() {
      let parse_js::ast::expr::lit::LitArrElem::Single(v) = elem else {
        return self.array_literal_type(arr);
      };
      let ty = self.check_expr(v);
      elems.push(types_ts_interned::TupleElem {
        ty,
        optional: false,
        rest: false,
        readonly: false,
      });
    }
    self.store.intern_type(TypeKind::Tuple(elems))
  }

  pub(crate) fn array_literal_type_with_expected(
    &mut self,
    arr: &Node<parse_js::ast::expr::lit::LitArrExpr>,
    expected: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    if arr
      .stx
      .elements
      .iter()
      .any(|e| !matches!(e, parse_js::ast::expr::lit::LitArrElem::Single(_)))
    {
      return self.array_literal_type(arr);
    }

    let elems: Vec<_> = arr
      .stx
      .elements
      .iter()
      .filter_map(|e| match e {
        parse_js::ast::expr::lit::LitArrElem::Single(v) => Some(v),
        _ => None,
      })
      .collect();
    let arity = elems.len();

    let contexts = self.array_literal_context_candidates(expected, arity);
    if contexts.is_empty() {
      return self.array_literal_type(arr);
    }

    let selected = contexts
      .iter()
      .enumerate()
      .find_map(|(context_idx, context)| {
        let ok = elems.iter().enumerate().all(|(idx, expr)| {
          let expected_elem = match context {
            ArrayLiteralContext::Tuple(expected_elems) => expected_elems
              .get(idx)
              .map(|e| e.ty)
              .unwrap_or(prim.unknown),
            ArrayLiteralContext::Array(expected_elem) => *expected_elem,
          };
          !self.has_contextual_excess_properties(expr, expected_elem)
        });
        ok.then_some(context_idx)
      })
      .unwrap_or(0);

    let context = contexts
      .into_iter()
      .nth(selected)
      .unwrap_or_else(|| unreachable!("contexts non-empty; selected index {selected} must exist"));

    match context {
      ArrayLiteralContext::Tuple(expected_elems) => {
        let mut out = Vec::new();
        for (idx, expr) in elems.into_iter().enumerate() {
          let expected_elem = expected_elems
            .get(idx)
            .map(|e| e.ty)
            .unwrap_or(prim.unknown);
          let expr_ty = if expected_elem != prim.unknown {
            self.check_expr_with_expected(expr, expected_elem)
          } else {
            self.check_expr(expr)
          };
          if expected_elem != prim.unknown {
            if let AstExpr::LitObj(obj) = expr.stx.as_ref() {
              let _ = self.report_excess_property(obj, expected_elem);
            }
          }
          let stored = if expected_elem != prim.unknown {
            self.contextual_widen_container(expr_ty, expected_elem)
          } else {
            self.widen_object_prop(expr_ty)
          };
          out.push(types_ts_interned::TupleElem {
            ty: stored,
            optional: false,
            rest: false,
            readonly: false,
          });
        }
        self.store.intern_type(TypeKind::Tuple(out))
      }
      ArrayLiteralContext::Array(expected_elem) => {
        let mut out = Vec::new();
        for expr in elems.into_iter() {
          let expr_ty = self.check_expr_with_expected(expr, expected_elem);
          if expected_elem != prim.unknown {
            if let AstExpr::LitObj(obj) = expr.stx.as_ref() {
              let _ = self.report_excess_property(obj, expected_elem);
            }
          }
          let stored = self.contextual_widen_container(expr_ty, expected_elem);
          out.push(stored);
        }
        // tsc still synthesizes `never[]`/`undefined[]` for empty `[]` even when
        // the contextual type is `T[]`; assignability (`never` <: `T`) carries
        // the contextual check.
        let elem_ty = if out.is_empty() {
          self.empty_array_element_type()
        } else {
          self.store.union(out)
        };
        self.store.intern_type(TypeKind::Array {
          ty: elem_ty,
          readonly: false,
        })
      }
    }
  }

  /// TS18016: private names are illegal as object-literal member keys.
  pub(crate) fn check_private_name_object_literal_key(&mut self, key: &ClassOrObjKey) {
    let ClassOrObjKey::Direct(direct) = key else {
      return;
    };
    if direct.stx.tt != TT::PrivateMember && !direct.stx.key.starts_with('#') {
      return;
    }
    self
      .diagnostics
      .push(codes::PRIVATE_IDENTIFIERS_OUTSIDE_CLASS.error(
        "Private identifiers are not allowed outside class bodies.",
        Span {
          file: self.file,
          range: loc_to_range(self.file, direct.loc),
        },
      ));
  }

  /// Return type of a getter's callable (object-literal accessor folding).
  fn object_accessor_return(&self, fn_ty: TypeId) -> TypeId {
    let sigs = callable_signatures(self.store.as_ref(), fn_ty);
    sigs
      .first()
      .map(|id| self.store.signature(*id).ret)
      .unwrap_or(self.store.primitive_ids().unknown)
  }

  /// First parameter type of a setter's callable (object-literal accessor
  /// folding).
  fn object_accessor_param(&self, fn_ty: TypeId) -> TypeId {
    let sigs = callable_signatures(self.store.as_ref(), fn_ty);
    sigs
      .first()
      .and_then(|id| self.store.signature(*id).params.first().map(|p| p.ty))
      .unwrap_or(self.store.primitive_ids().unknown)
  }

  /// Fold collected object-literal accessors into semantic property types:
  /// the property's type is the getter's return (setter's param when
  /// setter-only), writable when a setter exists — never the raw overloaded
  /// `(): R & (p: P) => void` callable that same-key interning would
  /// produce, so reads/writes see the accessor's value type
  /// (`emitCompoundExponentiationAssignmentWithIndexingOnLHS3`).
  fn push_object_accessors(&self, shape: &mut Shape, accessors: Vec<(PropKey, bool, TypeId)>) {
    let mut folded: Vec<(PropKey, Option<TypeId>, Option<TypeId>)> = Vec::new();
    for (key, is_getter, fn_ty) in accessors {
      if let Some(entry) = folded.iter_mut().find(|(k, _, _)| *k == key) {
        if is_getter {
          entry.1 = Some(self.object_accessor_return(fn_ty));
        } else {
          entry.2 = Some(self.object_accessor_param(fn_ty));
        }
      } else if is_getter {
        folded.push((key, Some(self.object_accessor_return(fn_ty)), None));
      } else {
        folded.push((key, None, Some(self.object_accessor_param(fn_ty))));
      }
    }
    for (key, getter_ret, setter_param) in folded {
      let (ty, readonly) = match (getter_ret, setter_param) {
        (Some(ret), Some(_)) => (ret, false),
        (Some(ret), None) => (ret, true),
        (None, Some(param)) => (param, false),
        (None, None) => continue,
      };
      super::stmts::upsert_shape_property(
        shape,
        types_ts_interned::Property {
          key,
          data: PropData {
            ty,
            optional: false,
            readonly,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        },
      );
    }
  }

  pub(crate) fn object_literal_type(
    &mut self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
  ) -> TypeId {
    if obj.stx.members.is_empty() {
      // TypeScript infers `{}` for empty object literals, which is semantically
      // the top type for non-nullish values (and is distinct from the `object`
      // keyword).
      return self.store.intern_type(TypeKind::EmptyObject);
    }
    let mut variants: Vec<Shape> = vec![Shape::new()];
    // `(key kind, value type)` contributions from computed keys; synthesized
    // into index signatures after the loop (tsc `getObjectLiteralIndexInfo`).
    let mut computed: Vec<(TypeId, TypeId)> = Vec::new();
    // Accessor entries (`(key, is_getter, fn_ty)`) folded after the loop into
    // semantic property types (see `push_object_accessors`).
    let mut accessors: Vec<(PropKey, bool, TypeId)> = Vec::new();
    for member in obj.stx.members.iter() {
      match &member.stx.typ {
        ObjMemberType::Valued { key, val } => {
          self.check_private_name_object_literal_key(key);
          enum Dest {
            Named(PropKey),
            Index(TypeId),
            Skip,
          }
          let dest = match key {
            ClassOrObjKey::Direct(direct) => Dest::Named(PropKey::String(
              self.store.intern_name(direct.stx.key.clone()),
            )),
            ClassOrObjKey::Computed(expr) => {
              let key_ty = self.check_expr(expr);
              match classify_computed_obj_key(&self.store, key_ty) {
                ComputedObjKey::Named(key) => Dest::Named(key),
                ComputedObjKey::Index(kind) => Dest::Index(kind),
                ComputedObjKey::Skip => Dest::Skip,
              }
            }
          };
          let push = |shape: &mut Shape,
                      computed: &mut Vec<(TypeId, TypeId)>,
                      ty: TypeId,
                      is_method: bool,
                      readonly: bool| match &dest {
            Dest::Named(prop_key) => {
              // Literal evaluation order: later members *replace* earlier ones
              // with the same key (`{ ...p, a: false }` → `a` from the prop,
              // never the intersection).
              super::stmts::upsert_shape_property(
                shape,
                types_ts_interned::Property {
                  key: prop_key.clone(),
                  data: PropData {
                    ty,
                    optional: false,
                    readonly,
                    accessibility: None,
                    is_method,
                    origin: None,
                    declared_on: None,
                  },
                },
              )
            }
            Dest::Index(kind) => computed.push((*kind, ty)),
            Dest::Skip => {}
          };
          match val {
            ClassOrObjVal::Prop(Some(expr)) => {
              let ty = self.check_expr(expr);
              let ty = if self.widen_object_literals {
                self.widen_object_prop(ty)
              } else {
                ty
              };
              for variant in variants.iter_mut() {
                push(variant, &mut computed, ty, false, false);
              }
            }
            ClassOrObjVal::Method(method) => {
              let ty = self.function_type(&method.stx.func);
              // Object literal methods are lowered into HIR as `ExprKind::FunctionExpr`
              // spans (keyed by `method.loc`), so ensure we record an expression type
              // for `type_at` queries.
              self.record_expr_type(method.loc, ty);
              for variant in variants.iter_mut() {
                push(variant, &mut computed, ty, true, false);
              }
            }
            ClassOrObjVal::Getter(getter) => {
              let ty = self.function_type(&getter.stx.func);
              self.record_expr_type(getter.loc, ty);
              match &dest {
                Dest::Named(prop_key) => accessors.push((prop_key.clone(), true, ty)),
                Dest::Index(kind) => computed.push((*kind, ty)),
                Dest::Skip => {}
              }
            }
            ClassOrObjVal::Setter(setter) => {
              let ty = self.function_type(&setter.stx.func);
              self.record_expr_type(setter.loc, ty);
              match &dest {
                Dest::Named(prop_key) => accessors.push((prop_key.clone(), false, ty)),
                Dest::Index(kind) => computed.push((*kind, ty)),
                Dest::Skip => {}
              }
            }
            _ => {}
          }
        }
        ObjMemberType::Shorthand { id } => {
          let key = PropKey::String(self.store.intern_name(id.stx.name.clone()));
          let ty = self
            .lookup(&id.stx.name)
            .map(|b| b.ty)
            .unwrap_or(self.store.primitive_ids().unknown);
          for variant in variants.iter_mut() {
            super::stmts::upsert_shape_property(
              variant,
              types_ts_interned::Property {
                key: key.clone(),
                data: PropData {
                  ty,
                  optional: false,
                  readonly: false,
                  accessibility: None,
                  is_method: false,
                  origin: None,
                  declared_on: None,
                },
              },
            );
          }
        }
        ObjMemberType::Rest { val } => {
          let spread_ty = self.check_expr(val);
          // tsc `getSpreadType`: spreading a union distributes into a union of
          // spreads (`{ ...u }` with `u: A | B` is `spread(A) | spread(B)`),
          // cross-producting across multiple union spreads. Below the fan-out
          // cap, keep the legacy single-shape merge.
          let expanded = self.expand_ref(spread_ty);
          let union_members = match self.store.type_kind(expanded) {
            TypeKind::Union(members) if members.len() > 1 => Some(members),
            _ => None,
          };
          match union_members {
            Some(members) if variants.len().saturating_mul(members.len()) <= 32 => {
              // tsc `getSpreadType` skips nullish union members entirely
              // (`{ ...({a: number} | undefined) }` is `{ a: number }`).
              let non_nullish: Vec<TypeId> = members
                .iter()
                .copied()
                .filter(|member| {
                  !matches!(
                    self.store.type_kind(self.store.canon(*member)),
                    TypeKind::Null | TypeKind::Undefined
                  )
                })
                .collect();
              if non_nullish.is_empty() {
                // Spread of a purely nullish union is `{}` (variant unchanged).
              } else {
                let mut fanned = Vec::with_capacity(variants.len() * non_nullish.len());
                for variant in variants.iter_mut() {
                  for member in non_nullish.iter().copied() {
                    let mut v = std::mem::replace(variant, Shape::new());
                    self.append_object_spread_properties(&mut v, member);
                    fanned.push(v);
                  }
                }
                variants = fanned;
              }
            }
            _ => {
              for variant in variants.iter_mut() {
                self.append_object_spread_properties(variant, spread_ty);
              }
            }
          }
        }
      }
    }
    let mut object_types: Vec<TypeId> = Vec::with_capacity(variants.len());
    for mut variant in variants {
      self.push_object_accessors(&mut variant, accessors.clone());
      synthesize_computed_indexers(&self.store, &mut variant, &computed);
      if variant.properties.is_empty() && variant.indexers.is_empty() {
        // Pure spreads of empty / non-object sources still infer `{}`.
        object_types.push(self.store.intern_type(TypeKind::EmptyObject));
        continue;
      }
      let shape_id = self.store.intern_shape(variant);
      let obj = self.store.intern_object(ObjectType { shape: shape_id });
      object_types.push(self.store.intern_type(TypeKind::Object(obj)));
    }
    if object_types
      .iter()
      .all(|ty| matches!(self.store.type_kind(*ty), TypeKind::EmptyObject))
    {
      return self.store.intern_type(TypeKind::EmptyObject);
    }
    self.store.union(object_types)
  }

  pub(crate) fn object_literal_type_with_expected(
    &mut self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    expected: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let mut shape = Shape::new();
    // `(key kind, value type)` contributions from computed keys; synthesized
    // into index signatures after the loop (tsc `getObjectLiteralIndexInfo`).
    let mut computed: Vec<(TypeId, TypeId)> = Vec::new();
    // Accessor entries (`(key, is_getter, fn_ty)`) folded after the loop into
    // semantic property types (see `push_object_accessors`).
    let mut accessors: Vec<(PropKey, bool, TypeId)> = Vec::new();
    for member in obj.stx.members.iter() {
      match &member.stx.typ {
        ObjMemberType::Valued { key, val } => {
          self.check_private_name_object_literal_key(key);
          enum Dest {
            Named(PropKey),
            Index(TypeId),
            Skip,
          }
          let (dest, expected_prop) = match key {
            ClassOrObjKey::Direct(direct) => {
              let name = direct.stx.key.clone();
              (
                Dest::Named(PropKey::String(self.store.intern_name(name.clone()))),
                self.member_type(expected, &name),
              )
            }
            ClassOrObjKey::Computed(expr) => {
              let key_ty = self.check_expr(expr);
              match classify_computed_obj_key(&self.store, key_ty) {
                ComputedObjKey::Named(prop_key) => {
                  let name = match &prop_key {
                    PropKey::String(id) => self.store.name(*id).to_string(),
                    PropKey::Number(n) => n.to_string(),
                    PropKey::Symbol(id) => self.store.name(*id).to_string(),
                  };
                  (
                    Dest::Named(prop_key),
                    self.member_type(expected, name.as_str()),
                  )
                }
                ComputedObjKey::Index(kind) => (
                  Dest::Index(kind),
                  self.member_type_for_index_key(expected, kind, false),
                ),
                ComputedObjKey::Skip => (Dest::Skip, prim.unknown),
              }
            }
          };
          let push = |shape: &mut Shape,
                      computed: &mut Vec<(TypeId, TypeId)>,
                      ty: TypeId,
                      is_method: bool,
                      readonly: bool| match &dest {
            Dest::Named(prop_key) => {
              // Literal evaluation order: later members *replace* earlier ones
              // with the same key (`{ ...p, a: false }` → `a` from the prop,
              // never the intersection).
              super::stmts::upsert_shape_property(
                shape,
                types_ts_interned::Property {
                  key: prop_key.clone(),
                  data: PropData {
                    ty,
                    optional: false,
                    readonly,
                    accessibility: None,
                    is_method,
                    origin: None,
                    declared_on: None,
                  },
                },
              )
            }
            Dest::Index(kind) => computed.push((*kind, ty)),
            Dest::Skip => {}
          };
          match val {
            ClassOrObjVal::Prop(Some(expr)) => {
              let expr_ty = if expected_prop != prim.unknown {
                self.check_expr_with_expected(expr, expected_prop)
              } else {
                self.check_expr(expr)
              };
              // Nested object literals are also "fresh" and participate in excess
              // property checks when contextually typed by an expected property
              // type.
              //
              // Without this, `let x: { nested: { foo: number } } = { nested: { foo: 1, bar: 2 } }`
              // would be accepted because `{ foo: 1, bar: 2 }` is structurally
              // assignable to `{ foo: number }` once it is no longer treated as a
              // fresh literal.
              if expected_prop != prim.unknown {
                if let AstExpr::LitObj(nested_obj) = expr.stx.as_ref() {
                  let _ = self.report_excess_property(nested_obj, expected_prop);
                }
              }
              let ty = if expected_prop != prim.unknown {
                self.contextual_widen_container(expr_ty, expected_prop)
              } else if self.widen_object_literals {
                self.widen_object_prop(expr_ty)
              } else {
                expr_ty
              };
              push(&mut shape, &mut computed, ty, false, false);
            }
            ClassOrObjVal::Method(method) => {
              let mut ty = self.function_type(&method.stx.func);
              if expected_prop != prim.unknown {
                let expected_callable = self
                  .contextual_callable_type(expected_prop)
                  .unwrap_or(expected_prop);
                if let Some(refined) =
                  self.refine_function_expr_with_expected(&method.stx.func, expected_callable)
                {
                  ty = refined;
                }
              }
              self.record_expr_type(method.loc, ty);
              push(&mut shape, &mut computed, ty, true, false);
            }
            ClassOrObjVal::Getter(getter) => {
              let ty = self.function_type(&getter.stx.func);
              self.record_expr_type(getter.loc, ty);
              match &dest {
                Dest::Named(prop_key) => accessors.push((prop_key.clone(), true, ty)),
                Dest::Index(kind) => computed.push((*kind, ty)),
                Dest::Skip => {}
              }
            }
            ClassOrObjVal::Setter(setter) => {
              let ty = self.function_type(&setter.stx.func);
              self.record_expr_type(setter.loc, ty);
              match &dest {
                Dest::Named(prop_key) => accessors.push((prop_key.clone(), false, ty)),
                Dest::Index(kind) => computed.push((*kind, ty)),
                Dest::Skip => {}
              }
            }
            _ => {}
          }
        }
        ObjMemberType::Shorthand { id } => {
          let name = id.stx.name.clone();
          let key = PropKey::String(self.store.intern_name(name.clone()));
          let value = self.lookup(&name).map(|b| b.ty).unwrap_or(prim.unknown);
          let expected_prop = self.member_type(expected, &name);
          let ty = if expected_prop != prim.unknown {
            self.contextual_widen_container(value, expected_prop)
          } else if self.widen_object_literals {
            self.widen_object_prop(value)
          } else {
            value
          };
          shape.properties.push(types_ts_interned::Property {
            key,
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
        ObjMemberType::Rest { val } => {
          let spread_ty = self.check_expr(val);
          self.append_object_spread_properties(&mut shape, spread_ty);
        }
      }
    }
    self.push_object_accessors(&mut shape, accessors);
    synthesize_computed_indexers(&self.store, &mut shape, &computed);
    if shape.properties.is_empty() && shape.indexers.is_empty() {
      return self.store.intern_type(TypeKind::EmptyObject);
    }
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  pub(crate) fn widen_object_prop(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::BooleanLiteral(_) => prim.boolean,
      TypeKind::BigIntLiteral(_) => prim.bigint,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_prop(m))
          .collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .into_iter()
          .map(|m| self.widen_object_prop(m))
          .collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  pub(crate) fn resolve_ident(&mut self, name: &str, expr: &Node<AstExpr>) -> TypeId {
    if let Some(binding) = self.lookup(name) {
      return binding.ty;
    }
    let mut range = loc_to_range(self.file, expr.loc);
    if range.start == range.end {
      let len = name.len() as u32;
      range.start = range.start.saturating_sub(len);
      range.end = range.start.saturating_add(len);
    }
    // Bare `#priv` is not a value-namespace name. Match tsc
    // `checkGrammarPrivateIdentifierExpression` (TS1451 / TS18016), not TS2304.
    // (Grammar diagnostics are suppressed later when the file has parse errors,
    // mirroring tsc `grammarErrorOnNode` + `hasParseDiagnostics`.)
    if name.starts_with('#') {
      let span = Span {
        file: self.file,
        range,
      };
      if self.enclosing_class_index.is_some() {
        self.diagnostics.push(codes::PRIVATE_IDENTIFIER_BAD_POSITION.error(
          "Private identifiers are only allowed in class bodies and may only be used as part of a class member declaration, property access, or on the left-hand-side of an 'in' expression",
          span,
        ));
      } else {
        self
          .diagnostics
          .push(codes::PRIVATE_IDENTIFIERS_OUTSIDE_CLASS.error(
            "Private identifiers are not allowed outside class bodies.",
            span,
          ));
      }
      return self.store.primitive_ids().any;
    }
    if std::env::var_os("DEBUG_RESOLVE_IDENT").is_some() {
      let mut scopes: Vec<(usize, usize, bool)> = self
        .scopes
        .iter()
        .enumerate()
        .map(|(idx, scope)| (idx, scope.bindings.len(), scope.bindings.contains_key(name)))
        .collect();
      scopes.reverse();
      let mut keys: Vec<String> = self
        .scopes
        .iter()
        .flat_map(|scope| scope.bindings.keys().cloned())
        .collect();
      keys.sort();
      keys.dedup();
      let preview: Vec<&str> = keys.iter().take(32).map(|s| s.as_str()).collect();
      eprintln!(
        "DEBUG_RESOLVE_IDENT: file={:?} name={:?} range={:?} scopes_rev={:?} keys={} preview={:?}",
        self.file,
        name,
        range,
        scopes,
        keys.len(),
        preview
      );
    }
    self.diagnostics.push(codes::CANNOT_FIND_NAME.error(
      codes::cannot_find_name_message(name),
      Span {
        file: self.file,
        range,
      },
    ));
    // tsc errorType is an any intrinsic; keep cascading checks any-like
    // (e.g. outside-class private access → TS18016 on `exports.#x`).
    self.store.primitive_ids().any
  }

  pub(crate) fn check_unary(&mut self, op: OperatorName, arg: &Node<AstExpr>) -> TypeId {
    match op {
      OperatorName::LogicalNot => self.store.primitive_ids().boolean,
      OperatorName::UnaryPlus | OperatorName::UnaryNegation | OperatorName::BitwiseNot => {
        self.store.primitive_ids().number
      }
      OperatorName::PrefixIncrement | OperatorName::PrefixDecrement => {
        // Compound update reads the target (tsc AssignmentKind.Compound).
        self.check_compound_update_target(arg);
        self.store.primitive_ids().number
      }
      OperatorName::Await => {
        let inner = self.check_expr(arg);
        awaited_type(self.store.as_ref(), inner, self.ref_expander)
      }
      OperatorName::Yield => {
        // Bare `yield;` parses with a synthetic `undefined` operand.
        let inner = self.check_expr(arg);
        self.yield_types.push(inner);
        self.store.primitive_ids().unknown
      }
      OperatorName::YieldDelegated => {
        // `yield* iterable` yields the iterable's element type.
        let inner = self.check_expr(arg);
        let elem = self.spread_element_type(inner);
        self.yield_types.push(elem);
        self.store.primitive_ids().unknown
      }
      OperatorName::Typeof => self.store.primitive_ids().string,
      OperatorName::Void => self.store.primitive_ids().undefined,
      OperatorName::Delete => {
        self.check_delete_expr(arg);
        self.store.primitive_ids().boolean
      }
      _ => {
        let _ = self.check_expr(arg);
        self.store.primitive_ids().unknown
      }
    }
  }

  /// tsc `checkDeleteExpression`: type-check the operand, then emit
  /// TS18011 for private-identifier targets and TS2790 when the deleted
  /// property is not optional under `strictNullChecks`.
  fn check_delete_expr(&mut self, arg: &Node<AstExpr>) {
    // Ordinary operand checking (member visibility, etc.) — once.
    let _ = self.check_expr(arg);
    let AstExpr::Member(mem) = arg.stx.as_ref() else {
      return;
    };
    let full_range = loc_to_range(self.file, mem.loc);
    let prop = mem.stx.right.as_str();
    if prop.starts_with('#') {
      self
        .diagnostics
        .push(codes::DELETE_PRIVATE_IDENTIFIER.error(
          "The operand of a 'delete' operator cannot be a private identifier.",
          Span {
            file: self.file,
            range: full_range,
          },
        ));
    }
    if !self.strict_null_checks {
      return;
    }
    // Re-resolve the object type for optionality. `this` / simple receivers do
    // not emit diagnostics, so a second walk is safe for the private-delete
    // fixtures; declared prop type (not the access type) matches tsc's
    // `getTypeOfSymbol`.
    let obj_ty = self.check_expr(&mem.stx.left);
    if !self.delete_operand_is_optional(obj_ty, prop) {
      self.diagnostics.push(codes::DELETE_MUST_BE_OPTIONAL.error(
        "The operand of a 'delete' operator must be optional.",
        Span {
          file: self.file,
          range: full_range,
        },
      ));
    }
  }

  /// Whether `delete obj.prop` should stay quiet for optionality (tsc
  /// `checkDeleteExpressionMustBeOptional`).
  fn delete_operand_is_optional(&mut self, obj: TypeId, prop: &str) -> bool {
    let declared_ty = self.member_type(obj, prop);
    let optional_flag = self.member_is_optional(obj, prop);
    let prim = self.store.primitive_ids();
    let canon = self.store.canon(declared_ty);
    // Unannotated class fields (`#v = 1`) often sit as `unknown` on synthesized
    // `this` shapes. That `unknown` is a missing-annotation stand-in, not a
    // user-written `unknown` (which tsc exempts). Prefer ClassInfo.
    if canon == prim.unknown {
      if let Some(is_opt) = self.class_info_delete_optional_hint(prop) {
        return is_opt;
      }
    }
    self.delete_prop_type_is_optional(declared_ty, optional_flag)
  }

  /// Declared / inferred type of a class field from ClassInfo when the instance
  /// shape still carries the `unknown` stand-in for unannotated fields.
  fn class_field_inferred_type(&mut self, prop: &str) -> Option<TypeId> {
    let class_index = self.enclosing_class_index?;
    self.class_field_inferred_type_for(class_index, prop)
  }

  fn class_field_inferred_type_for(&mut self, class_index: usize, prop: &str) -> Option<TypeId> {
    use super::super::ast_index::ClassValueMemberKind;
    if let Some(ty) = self.circular_field_init_type(class_index, prop) {
      return Some(ty);
    }
    let class = self.index.classes.get(class_index)?;
    let decl = class
      .value_member_decls
      .iter()
      .find(|d| d.name == prop && d.kind == ClassValueMemberKind::Field)?;
    if let Some(ann) = decl.type_annotation {
      return Some(self.lowerer.lower_type_expr(ann));
    }
    let init = decl.initializer?;
    self
      .field_init_type_stack
      .push((class_index, prop.to_string()));
    // Use the target field's initializer context so TS2729 use-before-init
    // compares against that field's member index (not the caller's).
    let prev_field_init = self.class_field_initializer.clone();
    if let Some(info) = self
      .index
      .class_field_initializers
      .values()
      .find(|info| info.class_index == class_index && info.prop_name == prop)
      .cloned()
    {
      self.class_field_initializer = Some(ClassFieldInitializerContext {
        class_index: info.class_index,
        member_index: info.member_index,
        is_static: info.is_static,
      });
    }
    // Field initializers widen like `let` (tsc): `10` → `number`.
    let init_ty = self.check_expr(init);
    self.class_field_initializer = prev_field_init;
    let _ = self.field_init_type_stack.pop();
    Some(self.base_type(init_ty))
  }

  /// When resolving `this.prop` / `this["prop"]` during field-init typing hits a
  /// name already on [`Self::field_init_type_stack`], return `any` and emit
  /// TS7022 (tsc `reportCircularityError`) under `--noImplicitAny`.
  fn circular_field_init_type(&mut self, class_index: usize, prop: &str) -> Option<TypeId> {
    if prop.is_empty() {
      return None;
    }
    let on_stack = self
      .field_init_type_stack
      .iter()
      .any(|(idx, name)| *idx == class_index && name == prop);
    if !on_stack {
      return None;
    }
    if self.no_implicit_any {
      // Re-entered name + current waiter (stack top), matching tsc's
      // reportCircularityError on both ends of a mutual cycle.
      self.emit_circular_initializer_implicit_any(class_index, prop);
      let waiter = self
        .field_init_type_stack
        .last()
        .filter(|(idx, name)| *idx == class_index && name != prop)
        .map(|(idx, name)| (*idx, name.clone()));
      if let Some((idx, name)) = waiter {
        self.emit_circular_initializer_implicit_any(idx, &name);
      }
    }
    Some(self.store.primitive_ids().any)
  }

  fn emit_circular_initializer_implicit_any(&mut self, class_index: usize, prop: &str) {
    let Some((key_range, display)) = self.field_init_name_span_and_display(class_index, prop)
    else {
      return;
    };
    if !self.implicit_any_reported.insert(key_range) {
      return;
    }
    self.diagnostics.push(codes::CIRCULAR_INITIALIZER_IMPLICIT_ANY.error(
      format!(
        "'{display}' implicitly has type 'any' because it does not have a type annotation and is referenced directly or indirectly in its own initializer."
      ),
      Span::new(self.file, key_range),
    ));
  }

  fn field_init_name_span_and_display(
    &self,
    class_index: usize,
    prop: &str,
  ) -> Option<(TextRange, String)> {
    // Prefer the initializer index entry (handles computed `["#bar"]` spans).
    if let Some(info) = self
      .index
      .class_field_initializers
      .values()
      .find(|info| info.class_index == class_index && info.prop_name == prop)
    {
      return Some((info.key_range, info.display_name.clone()));
    }
    let class = self.index.classes.get(class_index)?;
    let field = class
      .instance_fields
      .iter()
      .chain(class.static_fields.iter())
      .find(|f| f.name == prop)?;
    Some((field.key_range, prop.to_string()))
  }

  /// Recover `unknown` shape stand-ins for unannotated fields, with circularity.
  ///
  /// Only while typing a class field initializer (or when the resolution stack
  /// is already active). Must not run for arbitrary `unknown` receivers such as
  /// `thing.#bar` parameters — that falsely rewrites prop types and cascades
  /// into callability errors.
  fn recover_field_prop_type(&mut self, prop: &str, declared: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    if self.store.canon(declared) != prim.unknown {
      return declared;
    }
    let Some(class_index) = self.enclosing_class_index else {
      return declared;
    };
    let in_field_init = self.class_field_initializer.is_some()
      || self
        .field_init_type_stack
        .iter()
        .any(|(idx, _)| *idx == class_index);
    if !in_field_init {
      return declared;
    }
    if let Some(ty) = self.circular_field_init_type(class_index, prop) {
      return ty;
    }
    if let Some(inferred) = self.class_field_inferred_type(prop) {
      return inferred;
    }
    declared
  }

  /// ClassInfo-backed optionality when the shape type is the `unknown`
  /// stand-in for an unannotated field.
  ///
  /// - `prop?: T` / annotation including `undefined` → optional (quiet)
  /// - annotation `unknown`/`any` → optional (tsc AnyOrUnknown exemption)
  /// - unannotated definite field (with or without initializer) → not optional
  fn class_info_delete_optional_hint(&mut self, prop: &str) -> Option<bool> {
    let class_index = self.enclosing_class_index?;
    let class = self.index.classes.get(class_index)?;
    let field = class
      .instance_fields
      .iter()
      .chain(class.static_fields.iter())
      .find(|f| f.name == prop)?;
    if field.optional {
      return Some(true);
    }
    if let Some(ann) = field.type_annotation {
      let ty = self.lowerer.lower_type_expr(ann);
      return Some(self.delete_prop_type_is_optional(ty, false));
    }
    // Definite unannotated field: tsc infers a concrete type from the
    // initializer (or `any` under looseness) — never optional.
    Some(false)
  }

  fn delete_prop_type_is_optional(&self, prop_ty: TypeId, optional_flag: bool) -> bool {
    let prim = self.store.primitive_ids();
    let prop_ty = self.store.canon(prop_ty);
    if prop_ty == prim.any || prop_ty == prim.unknown || prop_ty == prim.never {
      return true;
    }
    if self.relate.options.exact_optional_property_types {
      return optional_flag;
    }
    // Without exactOptionalPropertyTypes, tsc uses TypeFacts.IsUndefined. Our
    // shapes often keep `optional: true` with a bare `T` rather than `T |
    // undefined`, so accept either.
    optional_flag || self.type_includes_undefined(prop_ty)
  }

  /// Whether `prop` is marked optional on `obj`'s shape.
  fn member_is_optional(&mut self, obj: TypeId, prop: &str) -> bool {
    self.member_optional_flag(obj, prop).unwrap_or_default()
  }

  fn member_optional_flag(&mut self, obj: TypeId, prop: &str) -> Option<bool> {
    let obj = self.expand_ref(obj);
    match self.store.type_kind(obj) {
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for candidate in shape.properties.iter() {
          let matches = match &candidate.key {
            PropKey::String(name_id) => self.store.name(*name_id) == prop,
            PropKey::Number(num) => prop.parse::<i64>().ok() == Some(*num),
            _ => false,
          };
          if matches {
            return Some(candidate.data.optional);
          }
        }
        None
      }
      TypeKind::Union(members) => {
        let mut saw = false;
        let mut all_optional = true;
        for member in members {
          if let Some(opt) = self.member_optional_flag(member, prop) {
            saw = true;
            all_optional &= opt;
          }
        }
        saw.then_some(all_optional)
      }
      TypeKind::Intersection(members) => {
        let mut flags = Vec::new();
        for member in members {
          if let Some(opt) = self.member_optional_flag(member, prop) {
            flags.push(opt);
          }
        }
        if flags.is_empty() {
          None
        } else {
          // Optional only if every declaring arm marks it optional.
          Some(flags.iter().all(|opt| *opt))
        }
      }
      TypeKind::Ref { .. } => None,
      _ => None,
    }
  }

  fn type_includes_undefined(&self, ty: TypeId) -> bool {
    fn inner(store: &types_ts_interned::TypeStore, ty: TypeId, seen: &mut HashSet<TypeId>) -> bool {
      let ty = store.canon(ty);
      if !seen.insert(ty) {
        return false;
      }
      match store.type_kind(ty) {
        TypeKind::Undefined => true,
        TypeKind::Union(members) => members.iter().any(|m| inner(store, *m, seen)),
        _ => false,
      }
    }
    let mut seen = HashSet::new();
    inner(self.store.as_ref(), ty, &mut seen)
  }

  pub(crate) fn check_binary(
    &mut self,
    op: OperatorName,
    left: &Node<AstExpr>,
    right: &Node<AstExpr>,
  ) -> TypeId {
    if op.is_assignment() {
      return self.check_assignment(op, left, right);
    }
    // `#priv in expr` / parenthesized private on the LHS of `in` must not go
    // through ordinary ident resolution (that would emit false TS2304).
    if matches!(op, OperatorName::In) {
      if let Some(prop) = Self::private_ident_name(left) {
        return self.check_private_in_expression(left, right, &prop);
      }
    }
    let lty = self.check_expr(left);
    let rty = self.check_expr(right);
    match op {
      OperatorName::Addition => {
        let left_kind = self.store.type_kind(lty);
        let right_kind = self.store.type_kind(rty);
        if matches!(left_kind, TypeKind::String | TypeKind::StringLiteral(_))
          || matches!(right_kind, TypeKind::String | TypeKind::StringLiteral(_))
        {
          self.store.primitive_ids().string
        } else if matches!(left_kind, TypeKind::Number | TypeKind::NumberLiteral(_))
          && matches!(right_kind, TypeKind::Number | TypeKind::NumberLiteral(_))
        {
          self.store.primitive_ids().number
        } else {
          self.store.union(vec![lty, rty])
        }
      }
      OperatorName::Subtraction
      | OperatorName::Multiplication
      | OperatorName::Division
      | OperatorName::Exponentiation
      | OperatorName::Remainder
      | OperatorName::BitwiseLeftShift
      | OperatorName::BitwiseRightShift
      | OperatorName::BitwiseUnsignedRightShift => self.store.primitive_ids().number,
      OperatorName::LogicalAnd | OperatorName::LogicalOr | OperatorName::NullishCoalescing => {
        self.store.union(vec![lty, rty])
      }
      OperatorName::Equality
      | OperatorName::Inequality
      | OperatorName::StrictEquality
      | OperatorName::StrictInequality
      | OperatorName::LessThan
      | OperatorName::LessThanOrEqual
      | OperatorName::GreaterThan
      | OperatorName::GreaterThanOrEqual
      | OperatorName::In
      | OperatorName::Instanceof => {
        if matches!(op, OperatorName::In) {
          // tsc `checkInExpression`: LHS assignable to string|number|symbol
          // (skipped for private identifiers — handled above).
          self.check_in_lhs(left, lty);
          self.check_in_rhs(right, rty);
        }
        self.store.primitive_ids().boolean
      }
      _ => self.store.union(vec![lty, rty]),
    }
  }

  /// `#name` identifier (possibly parenthesized). Used for `#x in` / TS1451.
  fn private_ident_name(expr: &Node<AstExpr>) -> Option<String> {
    match expr.stx.as_ref() {
      AstExpr::Id(id) if id.stx.name.starts_with('#') => Some(id.stx.name.clone()),
      _ => None,
    }
  }

  /// tsc `checkInExpression` for `PrivateIdentifier in ShiftExpression`.
  fn check_private_in_expression(
    &mut self,
    left: &Node<AstExpr>,
    right: &Node<AstExpr>,
    prop: &str,
  ) -> TypeId {
    let left_range = loc_to_range(self.file, left.loc);
    let parenthesized = left.assoc.get::<ParenthesizedExpr>().is_some();
    if parenthesized {
      // `(#field) in v` — private id is not a PrimaryExpression; TS1451.
      self
        .diagnostics
        .push(codes::PRIVATE_IDENTIFIER_BAD_POSITION.error(
          "Private identifiers are only allowed in class bodies and may only be used as part of a class member declaration, property access, or on the left-hand-side of an 'in' expression",
          Span {
            file: self.file,
            range: left_range,
          },
        ));
    } else if self.enclosing_class_index.is_none() {
      self
        .diagnostics
        .push(codes::PRIVATE_IDENTIFIERS_OUTSIDE_CLASS.error(
          "Private identifiers are not allowed outside class bodies.",
          Span {
            file: self.file,
            range: left_range,
          },
        ));
    } else {
      let lexical = self
        .index
        .lookup_lexical_private_class(self.enclosing_class_index, prop);
      if lexical.is_none() {
        // tsc `reportNonexistentProperty` on unresolved private in `#x in`.
        let prim = self.store.primitive_ids();
        self.diagnostics.push(codes::PROPERTY_DOES_NOT_EXIST.error(
          format!(
            "Property '{prop}' does not exist on type '{}'.",
            TypeDisplay::new(self.store.as_ref(), prim.any)
          ),
          Span {
            file: self.file,
            range: left_range,
          },
        ));
      }
    }
    let rty = self.check_expr(right);
    self.check_in_rhs(right, rty);
    self.store.primitive_ids().boolean
  }

  /// tsc `checkInExpression` LHS: assignable to `string | number | symbol`.
  fn check_in_lhs(&mut self, left: &Node<AstExpr>, lty: TypeId) {
    let prim = self.store.primitive_ids();
    let key_ty = self
      .store
      .union(vec![prim.string, prim.number, prim.symbol]);
    self.check_assignable(left, lty, key_ty, None);
  }

  /// Empty-shape `object` keyword type (tsc `nonPrimitiveType`).
  fn object_keyword_type(&self) -> TypeId {
    use types_ts_interned::{ObjectType, Shape};
    let shape = self.store.intern_shape(Shape::new());
    let obj = self.store.intern_object(ObjectType { shape });
    self.store.intern_type(TypeKind::Object(obj))
  }

  /// tsc `checkInExpression` RHS: non-null + assignable to non-primitive `object`.
  ///
  /// High-value nullish diagnostics: `unknown` → TS2571; `null` → TS18047;
  /// `undefined` → TS18048. Remaining types are checked against `object`
  /// (TS2322), matching tsc `nonPrimitiveType`.
  ///
  /// Bare identifier RHS is skipped here: tsc checks the *flow type* of a
  /// reference (`x !== null` must silence TS18047), which only CFA sees — the
  /// flow pass emits TS18046/TS18047/TS18048 for those. Assertions like
  /// `(v as unknown)` still error here.
  pub(crate) fn check_in_rhs(&mut self, right: &Node<AstExpr>, rty: TypeId) {
    let prim = self.store.primitive_ids();
    let ty = self.expand_ref(rty);
    // `parse-js` keeps paren locs on the inner expr; tsc spans include `(...)`.
    let mut range = loc_to_range(self.file, right.loc);
    if right.assoc.get::<ParenthesizedExpr>().is_some() {
      range = TextRange::new(range.start.saturating_sub(1), range.end.saturating_add(1));
    }
    let span = Span {
      file: self.file,
      range,
    };
    if matches!(right.stx.as_ref(), AstExpr::Id(_)) {
      // Flow pass owns bare-identifier `in` RHS checks.
      return;
    }
    if ty == prim.unknown {
      self
        .diagnostics
        .push(codes::OBJECT_IS_OF_TYPE_UNKNOWN.error("Object is of type 'unknown'.", span));
      return;
    }
    if self.strict_null_checks {
      match self.store.type_kind(ty) {
        TypeKind::Null => {
          self.diagnostics.push(codes::POSSIBLY_NULL.error(
            format!(
              "'{}' is possibly 'null'.",
              Self::expr_display_name(right).unwrap_or_else(|| "object".to_string())
            ),
            span,
          ));
          return;
        }
        TypeKind::Undefined => {
          self.diagnostics.push(codes::POSSIBLY_UNDEFINED.error(
            format!(
              "'{}' is possibly 'undefined'.",
              Self::expr_display_name(right).unwrap_or_else(|| "object".to_string())
            ),
            span,
          ));
          return;
        }
        TypeKind::Union(members) => {
          let has_null = members.iter().any(|&m| self.expand_ref(m) == prim.null);
          let has_undefined = members
            .iter()
            .any(|&m| self.expand_ref(m) == prim.undefined);
          let name = Self::expr_display_name(right).unwrap_or_else(|| "object".to_string());
          if has_null && !has_undefined {
            self
              .diagnostics
              .push(codes::POSSIBLY_NULL.error(format!("'{name}' is possibly 'null'."), span));
            return;
          } else if has_undefined && !has_null {
            self.diagnostics.push(
              codes::POSSIBLY_UNDEFINED.error(format!("'{name}' is possibly 'undefined'."), span),
            );
            return;
          } else if has_null && has_undefined {
            // Prefer the more specific null diagnostic when both are present and
            // the fixture expects TS18047 (typeof-object → object | null).
            self
              .diagnostics
              .push(codes::POSSIBLY_NULL.error(format!("'{name}' is possibly 'null'."), span));
            return;
          }
        }
        _ => {}
      }
    }
    // tsc `checkInExpression` uses assignability to non-primitive `object` without
    // fresh-literal excess property checks (`"k" in { a: 1 }` is fine).
    let object_ty = self.object_keyword_type();
    if matches!(self.store.type_kind(rty), TypeKind::Any | TypeKind::Unknown)
      || matches!(
        self.store.type_kind(object_ty),
        TypeKind::Any | TypeKind::Unknown
      )
    {
      return;
    }
    if self.relate.is_assignable(rty, object_ty) {
      return;
    }
    self.diagnostics.push(codes::TYPE_MISMATCH.error(
      format!(
        "Type '{}' is not assignable to type 'object'.",
        TypeDisplay::new(self.store.as_ref(), rty)
      ),
      span,
    ));
  }

  fn expr_display_name(expr: &Node<AstExpr>) -> Option<String> {
    match expr.stx.as_ref() {
      AstExpr::Id(id) => Some(id.stx.name.clone()),
      _ => None,
    }
  }

  /// Flow type after a successful assignment to an annotated binding.
  ///
  /// Union declarations narrow to the RHS (tsc CFA). Other annotations keep
  /// the declared type — subtype RHS values must not rewrite the binding for
  /// later reads (`assignmentCompatWithNumericIndexer3.ts`).
  fn assignment_flow_ty(&self, declared_ty: TypeId, value_ty: TypeId) -> TypeId {
    match self.store.type_kind(self.store.canon(declared_ty)) {
      TypeKind::Union(_) => value_ty,
      _ => declared_ty,
    }
  }

  /// TS2352 when `<T>e` / `e as T` asserts between types that do not overlap.
  /// Unions overlap when any constituent overlaps (tsc `isTypeOverlapping`).
  fn report_type_assertion_overlap(&mut self, src: TypeId, dst: TypeId, loc: Loc) {
    let range = loc_to_range(self.file, loc);
    if self.assertion_overlap_reported.contains(&range)
      || self.diagnostics.iter().any(|d| {
        d.code.as_str() == codes::TYPE_ASSERTION_NO_OVERLAP.as_str() && d.primary.range == range
      })
    {
      return;
    }
    let src = self.store.canon(src);
    let dst = self.store.canon(dst);
    if self.assertion_types_overlap(src, dst, 0) {
      return;
    }
    self.assertion_overlap_reported.insert(range);
    self.diagnostics.push(codes::TYPE_ASSERTION_NO_OVERLAP.error(
      format!(
        "Conversion of type '{}' to type '{}' may be a mistake because neither type sufficiently overlaps with the other. If this was intentional, convert the expression to 'unknown' first.",
        TypeDisplay::new(self.store.as_ref(), src),
        TypeDisplay::new(self.store.as_ref(), dst),
      ),
      Span {
        file: self.file,
        range,
      },
    ));
  }

  fn assertion_types_overlap(&self, src: TypeId, dst: TypeId, depth: usize) -> bool {
    if depth > 12 {
      return true;
    }
    let src = self.store.canon(src);
    let dst = self.store.canon(dst);
    if src == dst {
      return true;
    }
    if matches!(self.store.type_kind(dst), TypeKind::Any | TypeKind::Unknown)
      || matches!(self.store.type_kind(src), TypeKind::Any | TypeKind::Unknown)
    {
      return true;
    }
    match self.store.type_kind(src) {
      TypeKind::Union(members) => {
        return members
          .iter()
          .any(|m| self.assertion_types_overlap(*m, dst, depth + 1));
      }
      TypeKind::Intersection(members) => {
        return members
          .iter()
          .all(|m| self.assertion_types_overlap(*m, dst, depth + 1));
      }
      _ => {}
    }
    match self.store.type_kind(dst) {
      TypeKind::Union(members) => {
        return members
          .iter()
          .any(|m| self.assertion_types_overlap(src, *m, depth + 1));
      }
      TypeKind::Intersection(members) => {
        return members
          .iter()
          .any(|m| self.assertion_types_overlap(src, *m, depth + 1));
      }
      _ => {}
    }
    // tsc `checkAssertionDeferred`: the source expression type is *widened*
    // to its base literal form first (`getBaseTypeOfLiteralType` +
    // `getWidenedType`); the assertion is allowed when the target is
    // comparable to the widened source — `"foo" as "bar"` is fine because the
    // widened source is `string` and `"bar"` is comparable to `string`
    // (`stringLiteralsWithTypeAssertions01`). Only when that fails does tsc
    // check the source against the target. Both directions use tsc's
    // *comparable* relation, which relaxes the strictNullChecks optionality
    // gate (`optionalProperties01.ts`: `{required1, optional}` as Foo is legal
    // because Foo is comparable to the literal's type).
    let src_widened = self.widen_literals_for_assertion(src);
    self.is_comparable_for_check(dst, src_widened)
      || self.is_comparable_for_check(src, dst)
      || self.assertion_literal_comparable(src, dst, 0)
      || self.assertion_literal_comparable(dst, src, 0)
  }

  /// tsc `comparableRelation` variant of [`Self::is_assignable_for_check`]:
  /// same type-param source expansion, with the optionality gate relaxed for
  /// type-assertion overlap checks.
  fn is_comparable_for_check(&self, src: TypeId, dst: TypeId) -> bool {
    let mut keep = HashSet::new();
    self.collect_type_params(dst, &mut keep, 0);
    let src = self.expand_type_param_sources(src, &keep, 0);
    self.relate.is_assignable_comparable_optionality(src, dst)
  }

  /// tsc `getBaseTypeOfLiteralType`: literal types widen to their base
  /// primitive (`"a"` → `string`, `1` → `number`, …), unions widen per member.
  fn widen_literals_for_assertion(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::BooleanLiteral(_) => prim.boolean,
      TypeKind::BigIntLiteral(_) => prim.bigint,
      TypeKind::Union(members) => {
        let widened: Vec<_> = members
          .iter()
          .map(|&m| self.widen_literals_for_assertion(m))
          .collect();
        self.store.union(widened)
      }
      _ => ty,
    }
  }

  /// tsc `comparableRelation` literal relaxation: a primitive type is
  /// *comparable* to a literal of its own kind (`string` ↔ `"a"`), so type
  /// assertions between them are allowed even though assignability holds in
  /// only one direction (`str = t as string` where `t: S[] | S`, `S = "a"|"b"`,
  /// overlaps via the `S` constituent — `stringLiteralTypeAssertion01.ts`).
  fn assertion_literal_comparable(&self, src: TypeId, dst: TypeId, depth: usize) -> bool {
    if depth > 12 {
      return false;
    }
    let src = self.expand_ref(src);
    let dst = self.expand_ref(dst);
    if let TypeKind::Union(members) = self.store.type_kind(dst) {
      return members
        .iter()
        .any(|&m| self.assertion_literal_comparable(src, m, depth + 1));
    }
    if let TypeKind::Union(members) = self.store.type_kind(src) {
      return members
        .iter()
        .all(|&m| self.assertion_literal_comparable(m, dst, depth + 1));
    }
    matches!(
      (self.store.type_kind(src), self.store.type_kind(dst)),
      (TypeKind::String, TypeKind::StringLiteral(_))
        | (TypeKind::Number, TypeKind::NumberLiteral(_))
        | (TypeKind::Boolean, TypeKind::BooleanLiteral(_))
        | (TypeKind::BigInt, TypeKind::BigIntLiteral(_))
    )
  }

  /// Assignability with free type-parameter *sources* expanded to their
  /// constraints (`T extends Derived` → `Derived`), except params that also
  /// occur in the destination (keep `T` → `T`). Destinations keep nominal
  /// type-param rules (`Derived` ↛ `T`).
  pub(crate) fn is_assignable_for_check(&self, src: TypeId, dst: TypeId) -> bool {
    let mut keep = HashSet::new();
    self.collect_type_params(dst, &mut keep, 0);
    let src = self.expand_type_param_sources(src, &keep, 0);
    self.relate.is_assignable(src, dst)
  }

  fn collect_type_params(
    &self,
    ty: TypeId,
    out: &mut HashSet<types_ts_interned::TypeParamId>,
    depth: usize,
  ) {
    if depth > 16 {
      return;
    }
    let ty = self.store.canon(ty);
    match self.store.type_kind(ty) {
      TypeKind::TypeParam(param) => {
        out.insert(param);
      }
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        for prop in &shape.properties {
          self.collect_type_params(prop.data.ty, out, depth + 1);
        }
        for idx in &shape.indexers {
          self.collect_type_params(idx.value_type, out, depth + 1);
        }
      }
      TypeKind::Array { ty: elem, .. } => self.collect_type_params(elem, out, depth + 1),
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        for m in members {
          self.collect_type_params(m, out, depth + 1);
        }
      }
      TypeKind::Ref { args, .. } => {
        for a in args {
          self.collect_type_params(a, out, depth + 1);
        }
      }
      _ => {}
    }
  }

  pub(crate) fn expand_type_param_sources(
    &self,
    ty: TypeId,
    keep: &HashSet<types_ts_interned::TypeParamId>,
    depth: usize,
  ) -> TypeId {
    if depth > 16 {
      return ty;
    }
    let ty = self.store.canon(ty);
    match self.store.type_kind(ty) {
      TypeKind::TypeParam(param) if !keep.contains(&param) => self
        .type_param_constraint(param)
        .map(|c| self.expand_type_param_sources(c, keep, depth + 1))
        .unwrap_or(ty),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        let mut changed = false;
        let mut new_shape = shape.clone();
        for prop in &mut new_shape.properties {
          let next = self.expand_type_param_sources(prop.data.ty, keep, depth + 1);
          if next != prop.data.ty {
            prop.data.ty = next;
            changed = true;
          }
        }
        for idx in &mut new_shape.indexers {
          let next = self.expand_type_param_sources(idx.value_type, keep, depth + 1);
          if next != idx.value_type {
            idx.value_type = next;
            changed = true;
          }
        }
        if !changed {
          return ty;
        }
        let shape_id = self.store.intern_shape(new_shape);
        self.store.intern_type(TypeKind::Object(
          self.store.intern_object(ObjectType { shape: shape_id }),
        ))
      }
      TypeKind::Array { ty: elem, readonly } => {
        let next = self.expand_type_param_sources(elem, keep, depth + 1);
        if next == elem {
          ty
        } else {
          self
            .store
            .intern_type(TypeKind::Array { ty: next, readonly })
        }
      }
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members
          .iter()
          .map(|m| self.expand_type_param_sources(*m, keep, depth + 1))
          .collect();
        if mapped == members {
          ty
        } else {
          self.store.union(mapped)
        }
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members
          .iter()
          .map(|m| self.expand_type_param_sources(*m, keep, depth + 1))
          .collect();
        if mapped == members {
          ty
        } else {
          self.store.intersection(mapped)
        }
      }
      TypeKind::Ref { def, args } => {
        let mapped: Vec<_> = args
          .iter()
          .map(|a| self.expand_type_param_sources(*a, keep, depth + 1))
          .collect();
        if mapped == args {
          ty
        } else {
          self.store.intern_type(TypeKind::Ref { def, args: mapped })
        }
      }
      _ => ty,
    }
  }

  /// Whether `ty` is a call/construct signature carrier (after ref expansion).
  fn type_is_function_like(&self, ty: TypeId) -> bool {
    let ty = self.expand_callable_type(ty);
    match self.store.type_kind(ty) {
      TypeKind::Callable { .. } => true,
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        if !shape.call_signatures.is_empty() || !shape.construct_signatures.is_empty() {
          return true;
        }
        // Methodful interfaces (`{ f(x: number): void }`) must keep their
        // declared type across sequential assigns — same rationale as call-sig
        // bindings (`assignmentCompatWithCallSignatures2.ts`).
        shape.properties.iter().any(|prop| {
          if prop.data.is_method {
            return true;
          }
          let pt = self.store.canon(prop.data.ty);
          match self.store.type_kind(pt) {
            TypeKind::Callable { .. } => true,
            TypeKind::Object(inner) => {
              let inner_shape = self.store.shape(self.store.object(inner).shape);
              !inner_shape.call_signatures.is_empty()
                || !inner_shape.construct_signatures.is_empty()
            }
            _ => false,
          }
        })
      }
      _ => false,
    }
  }

  /// JS expando special assignment (tsc `bindSpecialPropertyAssignment`):
  /// `Outer.X = …` where `Outer` resolves to an expando var (`var Outer = {}`)
  /// and `X` was registered as an expando member. Only fires in `.js`/`.jsx`
  /// bodies (`jsdoc_source` is set) for registered members.
  fn is_js_expando_special_assignment(&self, obj: &Node<AstExpr>, member: &str) -> bool {
    let AstExpr::Id(id) = obj.stx.as_ref() else {
      return false;
    };
    let Some(outer_def) = self.js_expando_outer_def(&id.stx.name) else {
      return false;
    };
    self
      .expando_members
      .get(&outer_def)
      .is_some_and(|members| members.contains(member))
  }

  /// The def behind `name` when it is a registered JS expando outer var
  /// (`var Outer = {}` with `Outer.X = …` members), else `None`.
  fn js_expando_outer_def(&self, name: &str) -> Option<DefId> {
    if self.jsdoc_source.is_none() {
      return None;
    }
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_typeof(&[name.to_string()])?;
    self.expando_members.contains_key(&def).then_some(def)
  }

  /// Seeded member-augmented type for a JS expando outer var: tsc binds the
  /// registered `Outer.X = …` members onto the var's own type, so the var
  /// declarator keeps the seeded type instead of the bare `{}` initializer
  /// type. `None` when the seeded binding is missing or still `unknown`/`any`
  /// (e.g. mid-recursion while the var's own type is being computed).
  pub(crate) fn js_expando_seeded_outer_type(&self, name: &str) -> Option<TypeId> {
    self.js_expando_outer_def(name)?;
    let binding = self.lookup(name)?;
    let ty = binding.declared_ty;
    match self.store.type_kind(ty) {
      TypeKind::Unknown | TypeKind::Any => None,
      _ => Some(ty),
    }
  }

  pub(crate) fn check_assignment(
    &mut self,
    op: OperatorName,
    left: &Node<AstExpr>,
    right: &Node<AstExpr>,
  ) -> TypeId {
    self.check_cancelled();
    let prim = self.store.primitive_ids();
    match left.stx.as_ref() {
      AstExpr::Id(id) => {
        // tsc TS2539: ambient globals are not assignable variables.
        // Assignment LHS identifiers often lower as `IdPat` (see arm below).
        if matches!(id.stx.name.as_str(), "undefined" | "NaN" | "Infinity")
          && matches!(op, OperatorName::Assignment)
        {
          let value_ty = self.check_expr(right);
          self
            .diagnostics
            .push(codes::CANNOT_ASSIGN_NON_VARIABLE.error(
              codes::cannot_assign_non_variable_message(&id.stx.name),
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          return value_ty;
        }
        if let Some(binding) = self.lookup(&id.stx.name) {
          // Writes check against the declared type; CFA may have narrowed `ty`.
          let write_ty = binding.declared_ty;
          let value_ty = if matches!(op, OperatorName::Assignment) {
            self.check_expr_with_expected(right, write_ty)
          } else {
            self.check_expr(right)
          };
          if matches!(op, OperatorName::Assignment) {
            if let AstExpr::LitObj(obj) = right.stx.as_ref() {
              let _ = self.report_excess_property(obj, write_ty);
            }
          }
          let assignable = self.is_assignable_for_check(value_ty, write_ty);
          if assignable {
            // Narrow the flow type for subsequent reads. Do not touch
            // `declared_ty` — sequential assigns must still validate against
            // the annotation (`optionalPropertyAssignableToStringIndexSignature`).
            // Keep function-like declared types stable across sequential assigns.
            // Non-union annotations keep `declared_ty` as the flow type (tsc does
            // not refine `{ [n]: Derived }` to a subtype RHS — otherwise
            // `a = b2; b2 = a` loses the second TS2322 in NumericIndexer3).
            // Union annotations still narrow to the RHS (`string | null = "x"`).
            if !self.type_is_function_like(write_ty) {
              let next_ty = self.assignment_flow_ty(write_ty, value_ty);
              let _ = self.update_binding_ty(&id.stx.name, next_ty);
            }
          } else {
            // Anchor on the LHS binding name (tsc reports the identifier, not the RHS).
            // Keep the declared/current binding type — adopting an incompatible RHS
            // made the next `b = a` vacuously succeed after a failed `a = b`.
            // Prefer TS2741/TS2739 when the failure is only missing required props
            // (`assignmentCompatWithObjectMembers5.ts`: `foo` vs `fooo`).
            let code = self.assignability_mismatch_code(value_ty, write_ty, &codes::TYPE_MISMATCH);
            self.diagnostics.push(code.error(
              "assignment type mismatch",
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          }
          return value_ty;
        } else {
          let value_ty = self.check_expr(right);
          self.insert_binding(id.stx.name.clone(), value_ty, Vec::new());
          return value_ty;
        }
      }
      AstExpr::IdPat(id) => {
        // Assignment targets parse as `IdPat` (`undefined = null`).
        if matches!(id.stx.name.as_str(), "undefined" | "NaN" | "Infinity")
          && matches!(op, OperatorName::Assignment)
        {
          let value_ty = self.check_expr(right);
          self
            .diagnostics
            .push(codes::CANNOT_ASSIGN_NON_VARIABLE.error(
              codes::cannot_assign_non_variable_message(&id.stx.name),
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          return value_ty;
        }
        if let Some(binding) = self.lookup(&id.stx.name) {
          let write_ty = binding.declared_ty;
          let value_ty = if matches!(op, OperatorName::Assignment) {
            self.check_expr_with_expected(right, write_ty)
          } else {
            self.check_expr(right)
          };
          if matches!(op, OperatorName::Assignment) {
            if let AstExpr::LitObj(obj) = right.stx.as_ref() {
              let _ = self.report_excess_property(obj, write_ty);
            }
          }
          if self.is_assignable_for_check(value_ty, write_ty) {
            if !self.type_is_function_like(write_ty) {
              let next_ty = self.assignment_flow_ty(write_ty, value_ty);
              let _ = self.update_binding_ty(&id.stx.name, next_ty);
            }
          } else {
            // Anchor on the LHS binding name (tsc reports the identifier, not the RHS).
            let code = self.assignability_mismatch_code(value_ty, write_ty, &codes::TYPE_MISMATCH);
            self.diagnostics.push(code.error(
              "assignment type mismatch",
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          }
          return value_ty;
        } else {
          let value_ty = self.check_expr(right);
          self.insert_binding(id.stx.name.clone(), value_ty, Vec::new());
          return value_ty;
        }
      }
      AstExpr::Member(mem) => {
        let full_range = loc_to_range(self.file, mem.loc);
        let prop_len = mem.stx.right.len() as u32;
        let prop_span = TextRange::new(full_range.end.saturating_sub(prop_len), full_range.end);
        self.check_abstract_property_in_constructor(&mem.stx.left, &mem.stx.right, prop_span);
        // tsc reports TS2729 for writes as well as reads when a static field is
        // assigned in a static block that appears before the field declaration
        // (e.g. classStaticBlockUseBeforeDef2).
        self.check_property_not_used_before_initialization(
          &mem.stx.left,
          &mem.stx.right,
          full_range,
        );
        // Compound assignments read the LHS (TS2806 for setter-only private).
        // Definite `=` / logical assignments do not.
        if Self::is_compound_assignment_op(op) {
          self.check_private_write_only_accessor_read(&mem.stx.right, full_range);
        }
        // RHS may read other `this` props (TS2565) before this write counts.
        let obj_ty = self.check_expr(&mem.stx.left);
        // TS18013 / TS18014 / TS18030 / TS18046 on writes as well as reads.
        let optional_chain =
          mem.stx.optional_chaining || self.is_optional_chain_expr(&mem.stx.left);
        self.check_private_identifier_property_access(
          obj_ty,
          Some(&mem.stx.left),
          &mem.stx.right,
          prop_span,
          optional_chain,
        );
        let mut target_ty = self.member_type(obj_ty, &mem.stx.right);
        // Unannotated fields (`#a = 10`) sit as `unknown` on synthesized shapes;
        // recover the widened initializer type so `this.#a = "hello"` is TS2322.
        if target_ty == prim.unknown {
          if let Some(inferred) = self.class_field_inferred_type(&mem.stx.right) {
            target_ty = inferred;
          }
        }
        // JS expando special assignment (`Outer.X = …` where `Outer` is an
        // expando `var Outer = {}`): tsc binds the member from the RHS, so no
        // assignability check fires at the binding site (the RHS *is* the
        // member type, e.g. a JS-constructor function).
        let is_expando_special_assignment = matches!(op, OperatorName::Assignment)
          && self.is_js_expando_special_assignment(&mem.stx.left, &mem.stx.right);
        let value_ty = if matches!(op, OperatorName::Assignment) && target_ty != prim.unknown {
          self.check_expr_with_expected(right, target_ty)
        } else {
          self.check_expr(right)
        };
        if matches!(op, OperatorName::Assignment) {
          self.spi_note_assigned(&mem.stx.right);
        }
        // TS2803: private methods are never writable (including on `any`).
        // Do not suppress TS2322 — tsc reports both when the RHS is mistyped.
        let _ = self.check_assign_to_private_method(&mem.stx.right, prop_span);
        let readonly_diag =
          self.check_assign_to_readonly_property(&mem.stx.left, obj_ty, &mem.stx.right, prop_span);
        if target_ty != prim.unknown && !readonly_diag && !is_expando_special_assignment {
          if matches!(op, OperatorName::Assignment) {
            if let AstExpr::LitObj(obj) = right.stx.as_ref() {
              let _ = self.report_excess_property(obj, target_ty);
            }
          }
          if !self.relate.is_assignable(value_ty, target_ty) {
            let code = self.assignability_mismatch_code(value_ty, target_ty, &codes::TYPE_MISMATCH);
            self.diagnostics.push(code.error(
              "assignment type mismatch",
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          }
        }
        return value_ty;
      }
      AstExpr::ComputedMember(mem) => {
        let obj_ty = self.check_expr(&mem.stx.object);
        let key_ty = self.check_expr(&mem.stx.member);
        let prop = match mem.stx.member.stx.as_ref() {
          AstExpr::LitStr(str_lit) => Some(str_lit.stx.value.clone()),
          AstExpr::LitNum(num) => Some(num.stx.value.0.to_string()),
          _ => match self.store.type_kind(key_ty) {
            TypeKind::StringLiteral(id) => Some(self.store.name(id).to_string()),
            TypeKind::NumberLiteral(num) => Some(num.0.to_string()),
            _ => None,
          },
        };
        // Write-indexed-access: `T[A|B]` → `T[A] & T[B]` (may be `never`).
        let target_ty = self.member_type_for_index_key(obj_ty, key_ty, /*writing*/ true);
        let value_ty = if matches!(op, OperatorName::Assignment) && target_ty != prim.unknown {
          self.check_expr_with_expected(right, target_ty)
        } else {
          self.check_expr(right)
        };
        let readonly_diag = if let Some(prop_name) = prop.as_deref() {
          let prop_span = loc_to_range(self.file, mem.stx.member.loc);
          let _ = self.check_assign_to_private_method(prop_name, prop_span);
          self.check_assign_to_readonly_property(&mem.stx.object, obj_ty, prop_name, prop_span)
        } else {
          false
        };
        if target_ty != prim.unknown && !readonly_diag {
          if matches!(op, OperatorName::Assignment) {
            if let AstExpr::LitObj(obj) = right.stx.as_ref() {
              let _ = self.report_excess_property(obj, target_ty);
            }
          }
          if !self.relate.is_assignable(value_ty, target_ty) {
            let code = self.assignability_mismatch_code(value_ty, target_ty, &codes::TYPE_MISMATCH);
            self.diagnostics.push(code.error(
              "assignment type mismatch",
              Span {
                file: self.file,
                range: loc_to_range(self.file, left.loc),
              },
            ));
          }
        }
        return value_ty;
      }
      AstExpr::ArrPat(arr) => {
        // tsc infers tuples for array literals in destructuring positions, so
        // `[x, [y]] = [1, [2]]` destructures positionally rather than through
        // the union-element array type.
        let value_ty = match right.stx.as_ref() {
          AstExpr::LitArr(lit) => self.tuple_literal_type_for_destructuring(lit),
          _ => self.check_expr(right),
        };
        let span = loc_to_range(self.file, arr.loc);
        // Assignment LHS patterns are often absent from `index.pats` (only
        // binding/decl patterns are indexed). Fall back to the AST pattern so
        // nested `AssignTarget` reads still run (TS2806 on `this.#x.prop`).
        let prev_flag = self.destructuring_assignment;
        self.destructuring_assignment = true;
        if let Some(pat) = self.index.pats.get(&span).copied() {
          self.bind_pattern(pat, value_ty);
        } else {
          self.bind_array_pattern(arr, value_ty, Vec::new());
        }
        self.destructuring_assignment = prev_flag;
        return value_ty;
      }
      AstExpr::ObjPat(obj) => {
        self.check_abstract_props_destructured_from_this(obj, right);
        let value_ty = self.check_expr(right);
        let span = loc_to_range(self.file, obj.loc);
        let prev_flag = self.destructuring_assignment;
        self.destructuring_assignment = true;
        if let Some(pat) = self.index.pats.get(&span).copied() {
          self.bind_pattern(pat, value_ty);
        } else {
          self.bind_object_pattern(obj, value_ty, Vec::new());
        }
        self.destructuring_assignment = prev_flag;
        return value_ty;
      }
      _ => {}
    }
    self.check_expr(right)
  }

  pub(crate) fn check_expr_with_expected(
    &mut self,
    expr: &Node<AstExpr>,
    expected: TypeId,
  ) -> TypeId {
    let expected = self.store.canon(expected);
    let prim = self.store.primitive_ids();
    if expected == prim.unknown {
      return self.check_expr(expr);
    }

    match expr.stx.as_ref() {
      AstExpr::LitObj(obj) => {
        let ty = self.object_literal_type_with_expected(obj, expected);
        self.record_expr_type(expr.loc, ty);
        ty
      }
      AstExpr::LitArr(arr) => {
        let ty = self.array_literal_type_with_expected(arr, expected);
        self.record_expr_type(expr.loc, ty);
        ty
      }
      AstExpr::ArrowFunc(arrow) => {
        if let Some(refined) = self.refine_function_expr_with_expected(&arrow.stx.func, expected) {
          self.record_expr_type(expr.loc, refined);
          refined
        } else if let Some(callable) = self.contextual_callable_type(expected) {
          self.record_expr_type(expr.loc, callable);
          callable
        } else {
          self.check_expr(expr)
        }
      }
      AstExpr::Func(func) => {
        if let Some(refined) = self.refine_function_expr_with_expected(&func.stx.func, expected) {
          self.record_expr_type(expr.loc, refined);
          refined
        } else if let Some(callable) = self.contextual_callable_type(expected) {
          self.record_expr_type(expr.loc, callable);
          callable
        } else {
          self.check_expr(expr)
        }
      }
      AstExpr::Call(call) => {
        let contextual_return = match self.store.type_kind(expected) {
          TypeKind::Any | TypeKind::Unknown => None,
          _ => Some(expected),
        };
        let ty = self.check_call_expr(call, contextual_return);
        self.record_expr_type(expr.loc, ty);
        ty
      }
      AstExpr::Unary(un) if matches!(un.stx.operator, OperatorName::New) => {
        let contextual_return = match self.store.type_kind(expected) {
          TypeKind::Any | TypeKind::Unknown => None,
          _ => Some(expected),
        };
        let ty = self.check_new_expr(un, expr.loc, contextual_return);
        self.record_expr_type(expr.loc, ty);
        ty
      }
      _ => self.check_expr(expr),
    }
  }

  pub(crate) fn refine_function_expr_with_expected(
    &mut self,
    func: &Node<Func>,
    expected: TypeId,
  ) -> Option<TypeId> {
    let expected_sig = self.first_callable_signature(expected)?;

    let saved_expected = self.expected_return;
    let saved_expected_defer = self.expected_return_defer_type_params;
    let saved_async = self.in_async_function;
    let saved_returns = std::mem::take(&mut self.return_types);
    let saved_yields = std::mem::take(&mut self.yield_types);
    let saved_this = self.contextual_this_ty.take();
    // Nested functions are not class-initialization contexts (tsc
    // `isNodeUsedDuringClassInitialization` quits on function-likes).
    let saved_field_init = self.class_field_initializer.take();
    let saved_ctor_class = self.constructor_class_index.take();
    let saved_spi = self.spi_ctor.take();

    // Push the arrow/function type-param scope before binding params or lowering
    // annotations. Without this, `<T>(x: T) => …` assigned to a binding named /
    // typed with interface `T` resolves the annotation to that interface
    // (`assignmentCompatWithCallSignatures.ts`).
    let mut type_params = Vec::new();
    let mut pushed_type_params = false;
    if let Some(params) = func.stx.type_parameters.as_ref() {
      self.lowerer.push_type_param_scope();
      pushed_type_params = true;
      type_params = self.lower_type_params(params);
      self.type_param_scopes.push(type_params.clone());
    }

    self.in_async_function = func.stx.async_;
    self.contextual_this_ty = expected_sig.this_param;
    let contextual_ret = if func.stx.async_ {
      awaited_type(self.store.as_ref(), expected_sig.ret, self.ref_expander)
    } else {
      expected_sig.ret
    };
    self.expected_return = Some(contextual_ret);
    // The contextual signature's return is an inference target, not a declared
    // one: defer hard return-assignability diagnostics when it mentions type
    // params (tsc checks such returns only after the call instantiates them).
    self.expected_return_defer_type_params = self.type_mentions_type_param(contextual_ret);
    // Bind the body's parameters with the contextual signature's free type
    // params replaced by `unknown` — tsc's fallback for unresolved inference
    // when checking context-sensitive bodies. Body checks against them pass
    // trivially, and the post-resolution refine phase re-checks the body
    // against the instantiated signature (which remains authoritative).
    // (`new Promise(r => { r({}) })` against a free `T` — see
    // `defaultExportInAwaitExpression01`.)
    let mut defer_set = HashSet::new();
    for param in &expected_sig.params {
      self.collect_mentioned_type_params(param.ty, &mut defer_set);
    }
    self.collect_mentioned_type_params(expected_sig.ret, &mut defer_set);
    let prim = self.store.primitive_ids();
    let expected_sig_for_body = if defer_set.is_empty() {
      expected_sig.clone()
    } else {
      let subst: std::collections::HashMap<types_ts_interned::TypeParamId, TypeId> =
        defer_set.iter().map(|id| (*id, prim.unknown)).collect();
      let mut substituter = super::super::super::instantiate::Substituter::new(
        std::sync::Arc::clone(&self.store),
        subst,
      );
      types_ts_interned::Signature {
        params: expected_sig
          .params
          .iter()
          .map(|param| types_ts_interned::Param {
            ty: substituter.substitute_type(param.ty),
            ..param.clone()
          })
          .collect(),
        ..expected_sig.clone()
      }
    };
    self.scopes.push(Scope::default());
    self.bind_params(func, &[], Some(&expected_sig_for_body));
    self.check_function_body(func);
    self.scopes.pop();
    self.class_field_initializer = saved_field_init;
    self.constructor_class_index = saved_ctor_class;
    self.spi_ctor = saved_spi;

    let prim = self.store.primitive_ids();
    let inferred_ret = if self.return_types.is_empty() {
      prim.void
    } else {
      self.store.union(self.return_types.clone())
    };

    self.return_types = saved_returns;
    self.expected_return = saved_expected;
    self.expected_return_defer_type_params = saved_expected_defer;
    self.in_async_function = saved_async;
    self.contextual_this_ty = saved_this;

    let expected_ret = expected_sig.ret;
    let ret = if func.stx.async_ {
      self.async_function_return_type(inferred_ret)
    } else {
      inferred_ret
    };
    // Generators: tsc infers `Generator<Y, R, N>` from the body's yields and
    // checks THAT against the contextual return instead of adopting it
    // blindly — mismatched yields must surface TS2322 at the function
    // (`generatorTypeCheck25`). When the generator type relates to the
    // contextual return, the contextual type still wins (generic inference
    // targets like `generatorTypeCheck45`).
    let generator_ty = if func.stx.generator && !self.yield_types.is_empty() {
      let y = self.store.union(self.yield_types.clone());
      self.generator_type(y, ret)
    } else {
      None
    };
    self.yield_types = saved_yields;
    // Prefer the contextual return when the inferred return is not assignable
    // to it (body already checked against `expected_return`). Keeps literal
    // contextual returns like `3 | 4` from collapsing when inference widens.
    // Exception: an empty body infers `void`, and adopting a non-void
    // contextual return would silently accept `() => {}` where tsc reports
    // TS2322 (`staticMemberAssignsToConstructorFunctionMembers`).
    // Generators are exempt: a generator with no `return` still produces an
    // Iterator/Generator result, never `void` (`generatorTypeCheck45`).
    let ret = if let Some(gen_ty) = generator_ty {
      if self.relate.is_assignable(gen_ty, expected_ret) {
        expected_ret
      } else {
        gen_ty
      }
    } else if self.relate.is_assignable(ret, expected_ret) {
      ret
    } else if inferred_ret == prim.void
      && !func.stx.generator
      && !matches!(
        self.store.type_kind(expected_ret),
        TypeKind::Void | TypeKind::Undefined | TypeKind::Any | TypeKind::Unknown
      )
    {
      ret
    } else {
      expected_ret
    };

    // Build the *actual* parameter list: explicit annotations win over
    // contextual types. Returning `expected_sig` wholesale used to erase
    // `(...args: string[]) => …` into the target `(...args: number[]) => …`,
    // silencing TS2322 on rest/param mismatches
    // (`assignmentCompatWithCallSignaturesWithRestParameters.ts`).
    let mut params = Vec::with_capacity(func.stx.parameters.len());
    for (idx, p) in func.stx.parameters.iter().enumerate() {
      let annotated = self.hir_param_annotation_ty(func, idx).or_else(|| {
        p.stx
          .type_annotation
          .as_ref()
          .map(|t| self.lowerer.lower_type_expr(t))
      });
      let contextual = expected_sig
        .params
        .get(idx)
        .map(|param| {
          if param.rest && !p.stx.rest {
            self.spread_element_type(param.ty)
          } else {
            param.ty
          }
        })
        .or_else(|| {
          expected_sig
            .params
            .iter()
            .enumerate()
            .find(|(_, param)| param.rest)
            .filter(|(rest_idx, _)| idx >= *rest_idx)
            .map(|(_, rest_param)| {
              if p.stx.rest {
                rest_param.ty
              } else {
                self.spread_element_type(rest_param.ty)
              }
            })
        });
      let ty = annotated
        .or(contextual)
        .unwrap_or(self.store.primitive_ids().unknown);
      let name = match p.stx.pattern.stx.pat.stx.as_ref() {
        AstPat::Id(id) => Some(self.store.intern_name(id.stx.name.clone())),
        _ => None,
      };
      params.push(types_ts_interned::Param {
        name,
        ty,
        optional: p.stx.optional,
        rest: p.stx.rest,
      });
    }

    if pushed_type_params {
      self.type_param_scopes.pop();
      self.lowerer.pop_type_param_scope();
    }

    let mut instantiated = expected_sig;
    instantiated.params = params;
    instantiated.ret = ret;
    // Keep the source type parameters on the resulting signature whenever the
    // function expression is generic: the relate engine's CSI path
    // instantiates them against a non-generic target (`t = <T>(x: T) => 1`
    // into `(x: number) => void` instantiates `T := number`). Stripping them
    // would leave a *free* `TypeParam` in a non-generic signature, which the
    // nominal type-param target rules reject.
    if !type_params.is_empty() {
      instantiated.type_params = type_params;
    }
    let sig_id = self.store.intern_signature(instantiated);
    Some(self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    }))
  }

  pub(crate) fn first_callable_signature(&self, ty: TypeId) -> Option<Signature> {
    let ty = self.expand_callable_type(ty);
    match self.store.type_kind(ty) {
      TypeKind::Callable { overloads } => overloads.first().map(|sig| self.store.signature(*sig)),
      TypeKind::Object(obj) => {
        let shape = self.store.shape(self.store.object(obj).shape);
        shape
          .call_signatures
          .first()
          .map(|sig_id| self.store.signature(*sig_id))
      }
      TypeKind::Union(members) | TypeKind::Intersection(members) => members
        .iter()
        .copied()
        .find_map(|member| self.first_callable_signature(member)),
      TypeKind::Ref { .. } => None,
      _ => None,
    }
  }

  pub(crate) fn contextual_callable_type(&mut self, ty: TypeId) -> Option<TypeId> {
    pub(crate) fn inner(
      checker: &mut Checker<'_>,
      ty: TypeId,
      seen: &mut HashSet<TypeId>,
    ) -> Option<TypeId> {
      if !seen.insert(ty) {
        return None;
      }
      match checker.store.type_kind(ty) {
        TypeKind::Callable { .. } => Some(ty),
        TypeKind::TypeParam(param) => checker
          .type_param_constraint(param)
          .and_then(|constraint| inner(checker, constraint, seen)),
        TypeKind::Object(obj) => {
          let shape = checker.store.shape(checker.store.object(obj).shape);
          if shape.call_signatures.is_empty() {
            None
          } else {
            let mut overloads = Vec::new();
            let mut seen = HashSet::new();
            for sig_id in shape.call_signatures.iter().copied() {
              if seen.insert(sig_id) {
                overloads.push(sig_id);
              }
            }
            Some(checker.store.intern_type(TypeKind::Callable { overloads }))
          }
        }
        TypeKind::Union(members) | TypeKind::Intersection(members) => members
          .iter()
          .copied()
          .find_map(|member| inner(checker, member, seen)),
        TypeKind::Ref { def, args } => checker
          .ref_expander
          .and_then(|expander| expander.expand_ref(checker.store.as_ref(), def, &args))
          .and_then(|expanded| inner(checker, expanded, seen)),
        _ => None,
      }
    }
    inner(self, ty, &mut HashSet::new())
  }

  pub(crate) fn base_type(&self, ty: TypeId) -> TypeId {
    match self.store.type_kind(ty) {
      TypeKind::BooleanLiteral(_) => self.store.primitive_ids().boolean,
      TypeKind::NumberLiteral(_) => self.store.primitive_ids().number,
      TypeKind::StringLiteral(_) => self.store.primitive_ids().string,
      TypeKind::BigIntLiteral(_) => self.store.primitive_ids().bigint,
      TypeKind::Union(members) => {
        let mapped: Vec<_> = members.into_iter().map(|m| self.base_type(m)).collect();
        self.store.union(mapped)
      }
      TypeKind::Intersection(members) => {
        let mapped: Vec<_> = members.into_iter().map(|m| self.base_type(m)).collect();
        self.store.intersection(mapped)
      }
      _ => ty,
    }
  }

  pub(crate) fn promise_type(&self, inner: TypeId) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&["Promise".to_string()])?;
    Some(self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: vec![inner],
    })))
  }

  /// Global `Generator<Y, R, N>` for generator function return inference
  /// (tsc aggregates the body's yield union and relates it to the contextual
  /// return type). `None` when the global interface cannot be resolved.
  pub(crate) fn generator_type(&self, y: TypeId, ret: TypeId) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&["Generator".to_string()])?;
    let prim = self.store.primitive_ids();
    Some(self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: vec![y, ret, prim.unknown],
    })))
  }

  /// Global `RegExp` interface type for regex literals (tsc literal type).
  /// `None` when the global interface cannot be resolved (e.g. no lib).
  pub(crate) fn regexp_literal_type(&self) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&["RegExp".to_string()])?;
    let ref_ty = self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: Vec::new(),
    }));
    let expanded = self.expand_ref(ref_ty);
    if matches!(
      self.store.type_kind(expanded),
      TypeKind::Unknown | TypeKind::Any | TypeKind::Ref { .. }
    ) {
      return None;
    }
    Some(expanded)
  }

  /// Apparent `Array<T>` interface for a `TypeKind::Array` element type (tsc
  /// `getGlobalArrayType` / apparent-type path). Used for named members such as
  /// `push` / `pop` that live on the lib interface, not on the intrinsic array.
  pub(crate) fn array_interface_type(&self, elem_ty: TypeId) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&["Array".to_string()])?;
    let ref_ty = self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: vec![elem_ty],
    }));
    let expanded = self.expand_ref(ref_ty);
    // Guard against a missing/cycle expansion that leaves a bare array/ref.
    if matches!(
      self.store.type_kind(expanded),
      TypeKind::Array { .. } | TypeKind::Unknown | TypeKind::Any | TypeKind::Ref { .. }
    ) {
      return None;
    }
    Some(expanded)
  }

  pub(crate) fn async_function_return_type(&self, ret: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let inner = awaited_type(self.store.as_ref(), ret, self.ref_expander);
    self.promise_type(inner).unwrap_or(prim.unknown)
  }

  /// Type a class expression as its constructor value type (static side +
  /// construct signatures returning an instance that includes private members).
  ///
  /// Prefer the HIR-lowered value type when available so method signatures
  /// (e.g. `static getInstance(): C`) stay accurate; fall back to a ClassInfo
  /// synthesis that still carries `#`-prefixed members for TS18013.
  pub(crate) fn check_class_expression(
    &mut self,
    class_expr: &Node<parse_js::ast::expr::ClassExpr>,
    expr_loc: Loc,
  ) -> TypeId {
    for decorator in class_expr.stx.decorators.iter() {
      let _ = self.check_expr(&decorator.stx.expression);
    }
    let mut pushed_type_params = false;
    if let Some(params) = class_expr.stx.type_parameters.as_ref() {
      self.lowerer.push_type_param_scope();
      let decls = self.lower_type_params(params);
      self.type_param_scopes.push(decls);
      pushed_type_params = true;
    }
    if let Some(extends) = class_expr.stx.extends.as_ref() {
      let _ = self.check_expr(extends);
    }
    if pushed_type_params {
      self.type_param_scopes.pop();
      self.lowerer.pop_type_param_scope();
    }
    let range = loc_to_range(self.file, expr_loc);
    let ty = if let Some(ty) = self.class_expr_value_tys.get(&range).copied() {
      ty
    } else if let Some(&class_index) = self.index.classes_by_span.get(&range) {
      self
        .synthesize_class_expression_value_type(class_index)
        .unwrap_or_else(|| self.store.primitive_ids().unknown)
    } else {
      self.store.primitive_ids().unknown
    };
    // Class expression names are in scope for the class body (checked as a
    // separate body). Seeding here also covers `new Named()` at the same
    // statement level when binder seed bindings were missing/unknown.
    if let Some(name) = class_expr.stx.name.as_ref() {
      self.insert_binding(name.stx.name.clone(), ty, Vec::new());
    }
    ty
  }

  pub(crate) fn function_type(&mut self, func: &Node<Func>) -> TypeId {
    let mut type_params = Vec::new();
    let mut pushed_type_params = false;
    if let Some(params) = func.stx.type_parameters.as_ref() {
      self.lowerer.push_type_param_scope();
      pushed_type_params = true;
      type_params = self.lower_type_params(params);
    }
    let jsdoc = self
      .jsdoc_tags_for_function(func)
      .map(|tags| tags.into_owned());
    if !pushed_type_params {
      if let Some(tags) = jsdoc.as_ref() {
        if !tags.templates.is_empty() {
          self.lowerer.push_type_param_scope();
          pushed_type_params = true;
          type_params = self.register_jsdoc_templates(&tags.templates);
        }
      }
    }
    // checkJs: whole-signature `@type {function…}` / `(…) => T` wins when there
    // are no per-param `@param` / `@returns` tags (those still override below).
    // Also accepts constructable `@type {function(new:…)}` object types.
    if let Some(tags) = jsdoc.as_ref() {
      if tags.params.is_empty() && tags.returns.is_none() && !tags.constructor {
        if let Some(raw) = tags.type_tag.as_deref() {
          let ty = self.lower_jsdoc_ty(raw);
          if matches!(
            self.store.type_kind(ty),
            TypeKind::Callable { .. } | TypeKind::Object(_)
          ) {
            // Only short-circuit for callables / constructable objects.
            let use_ty = match self.store.type_kind(ty) {
              TypeKind::Callable { .. } => true,
              TypeKind::Object(obj) => {
                let shape = self.store.shape(self.store.object(obj).shape);
                !shape.construct_signatures.is_empty() || !shape.call_signatures.is_empty()
              }
              _ => false,
            };
            if use_ty {
              if pushed_type_params {
                self.lowerer.pop_type_param_scope();
              }
              return ty;
            }
          }
        }
      }
    }
    let mut params = Vec::with_capacity(func.stx.parameters.len());
    let mut param_ty_by_name: std::collections::HashMap<String, TypeId> =
      std::collections::HashMap::new();
    // Fold nested `@param opts.x` into root param types (TS8032 reported from
    // `bind_params` to avoid duplicate diagnostics).
    let jsdoc_resolved = self.jsdoc_resolved_param_types(func, false);
    for (idx, p) in func.stx.parameters.iter().enumerate() {
      let name_str = match p.stx.pattern.stx.pat.stx.as_ref() {
        AstPat::Id(id) => Some(id.stx.name.as_str()),
        _ => None,
      };
      let name = name_str.map(|n| self.store.intern_name(n.to_string()));
      // Prefer HIR when `func` is this body's FunctionData; nested function /
      // method expressions in an outer body keep AST TypeLowerer.
      let annotated = self.hir_param_annotation_ty(func, idx).or_else(|| {
        p.stx
          .type_annotation
          .as_ref()
          .map(|t| self.lowerer.lower_type_expr(t))
      });
      let jsdoc_resolved_param = name_str.and_then(|n| jsdoc_resolved.get(n));
      let jsdoc_ty = annotated
        .is_none()
        .then(|| jsdoc_resolved_param.map(|p| p.ty))
        .flatten();
      let mut optional = p.stx.optional;
      if let Some(p) = jsdoc_resolved_param {
        optional = optional || p.optional;
      }
      let ty = annotated
        .or(jsdoc_ty)
        .unwrap_or(self.store.primitive_ids().unknown);
      if let Some(n) = name_str {
        param_ty_by_name.insert(n.to_owned(), ty);
      }
      params.push(SigParam {
        name,
        ty,
        optional,
        rest: p.stx.rest,
      });
    }
    let annotated_ret = self.hir_return_annotation_ty(func).or_else(|| {
      func
        .stx
        .return_type
        .as_ref()
        .map(|t| self.lowerer.lower_type_expr(t))
    });
    let jsdoc_ret = annotated_ret
      .is_none()
      .then(|| {
        jsdoc
          .as_ref()
          .and_then(|tags| tags.returns.as_deref())
          .map(|raw| self.lower_jsdoc_ty(raw))
      })
      .flatten();
    let ret = annotated_ret
      .or(jsdoc_ret)
      .unwrap_or(self.store.primitive_ids().unknown);
    let ret = if func.stx.async_ {
      self.async_function_return_type(ret)
    } else {
      ret
    };
    if pushed_type_params {
      self.lowerer.pop_type_param_scope();
    }
    // `@constructor` function expressions → constructable object type.
    if jsdoc.as_ref().is_some_and(|t| t.constructor) {
      let body_src = self.jsdoc_source.and_then(|src| {
        let range = loc_to_range(self.file, func.loc);
        let start = range.start as usize;
        let end = range.end as usize;
        src.get(start..end)
      });
      let instance = if let Some(body) = body_src {
        crate::jsdoc::infer_constructor_instance_type(self.store.as_ref(), body, &param_ty_by_name)
      } else {
        let shape = self.store.intern_shape(Shape::new());
        let obj = self.store.intern_object(ObjectType { shape });
        self.store.intern_type(TypeKind::Object(obj))
      };
      return crate::jsdoc::constructable_type(self.store.as_ref(), params, instance);
    }
    let sig = Signature {
      params,
      ret,
      type_params,
      this_param: None,
    };
    let sig_id = self.store.intern_signature(sig);
    let ty = self.store.intern_type(TypeKind::Callable {
      overloads: vec![sig_id],
    });
    ty
  }

  pub(crate) fn record_expr_type(&mut self, loc: Loc, ty: TypeId) {
    let range = loc_to_range(self.file, loc);
    if let Some(id) = self.expr_map.get(&range) {
      if let Some(slot) = self.expr_types.get_mut(id.0 as usize) {
        *slot = ty;
      }
    }
  }

  pub(crate) fn record_pat_type(&mut self, loc: Loc, ty: TypeId) {
    let range = loc_to_range(self.file, loc);
    if let Some(id) = self.pat_map.get(&range) {
      if let Some(slot) = self.pat_types.get_mut(id.0 as usize) {
        *slot = ty;
      }
    }
  }

  pub(crate) fn contextual_arg_type(&self, arg_ty: TypeId, param_ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match (self.store.type_kind(arg_ty), self.store.type_kind(param_ty)) {
      (TypeKind::NumberLiteral(_), TypeKind::Number) => prim.number,
      (TypeKind::StringLiteral(_), TypeKind::String) => prim.string,
      (TypeKind::BooleanLiteral(_), TypeKind::Boolean) => prim.boolean,
      (TypeKind::Union(members), TypeKind::Number) => {
        if members
          .iter()
          .all(|m| matches!(self.store.type_kind(*m), TypeKind::NumberLiteral(_)))
        {
          prim.number
        } else {
          arg_ty
        }
      }
      (TypeKind::Union(members), TypeKind::String) => {
        if members
          .iter()
          .all(|m| matches!(self.store.type_kind(*m), TypeKind::StringLiteral(_)))
        {
          prim.string
        } else {
          arg_ty
        }
      }
      (TypeKind::Union(members), TypeKind::Boolean) => {
        if members
          .iter()
          .all(|m| matches!(self.store.type_kind(*m), TypeKind::BooleanLiteral(_)))
        {
          prim.boolean
        } else {
          arg_ty
        }
      }
      _ => arg_ty,
    }
  }
}
