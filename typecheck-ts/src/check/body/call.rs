use std::collections::HashSet;

use diagnostics::{Span, TextRange};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::node::Node;
use parse_js::loc::Loc;
use types_ts_interned::{ObjectType, PredicateParam, Shape, TypeDisplay, TypeId, TypeKind};

use super::super::super::expr::{resolve_call, resolve_construct};
use super::super::super::flow_narrow::narrow_non_nullish;
use super::super::super::overload::{
  callable_signatures_with_expander, construct_signatures_with_expander, expected_arg_type_at,
  signature_allows_arg_count, signature_contains_literal_types, CallArgType,
};
use crate::codes;

use super::super::{fixed_spread_len, loc_to_range, Checker};

impl<'a> Checker<'a> {
  pub(crate) fn check_call_expr(
    &mut self,
    call: &Node<parse_js::ast::expr::CallExpr>,
    contextual_return: Option<TypeId>,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    // tsc: a super call expression has type `void` (`superCalls.ts`). Argument
    // expressions are still checked for their own diagnostics; matching the
    // base constructor's signature for arity/param checks is a separate gap.
    if matches!(call.stx.callee.stx.as_ref(), AstExpr::Super(_)) {
      for arg in call.stx.arguments.iter() {
        self.check_expr(&arg.stx.value);
      }
      return prim.void;
    }
    let callee_ty = self.check_expr(&call.stx.callee);

    let call_optional = call.stx.optional_chaining || self.is_optional_chain_expr(&call.stx.callee);

    let callee_base = if call_optional {
      narrow_non_nullish(callee_ty, &self.store).0
    } else {
      callee_ty
    };
    let callee_base = self.expand_callable_type(callee_base);

    let all_candidate_sigs =
      callable_signatures_with_expander(self.store.as_ref(), callee_base, self.ref_expander);
    let mut candidate_sigs = all_candidate_sigs.clone();
    let has_spread = call.stx.arguments.iter().any(|arg| arg.stx.spread);
    let mut callee_for_resolution = callee_base;
    let sigs_for_context = {
      let base_for_context = if has_spread {
        let sigs_without_excess_props: Vec<_> = all_candidate_sigs
          .iter()
          .copied()
          .filter(|sig_id| {
            let sig = self.store.signature(*sig_id);
            call
              .stx
              .arguments
              .iter()
              .enumerate()
              .take_while(|(_, arg)| !arg.stx.spread)
              .all(|(idx, arg)| {
                let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, idx) else {
                  return false;
                };
                !self.has_contextual_excess_properties(&arg.stx.value, param_ty)
              })
          })
          .collect();

        if sigs_without_excess_props.is_empty() {
          candidate_sigs.clone()
        } else {
          candidate_sigs = sigs_without_excess_props;
          callee_for_resolution = self.store.intern_type(TypeKind::Callable {
            overloads: candidate_sigs.clone(),
          });
          candidate_sigs.clone()
        }
      } else {
        let sigs_by_arity: Vec<_> = all_candidate_sigs
          .iter()
          .copied()
          .filter(|sig_id| {
            let sig = self.store.signature(*sig_id);
            signature_allows_arg_count(self.store.as_ref(), &sig, call.stx.arguments.len())
          })
          .collect();

        let sigs_without_excess_props: Vec<_> = sigs_by_arity
          .iter()
          .copied()
          .filter(|sig_id| {
            let sig = self.store.signature(*sig_id);
            call.stx.arguments.iter().enumerate().all(|(idx, arg)| {
              let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, idx) else {
                return false;
              };
              !self.has_contextual_excess_properties(&arg.stx.value, param_ty)
            })
          })
          .collect();

        if sigs_without_excess_props.is_empty() {
          if sigs_by_arity.is_empty() {
            all_candidate_sigs.clone()
          } else {
            sigs_by_arity
          }
        } else {
          candidate_sigs = sigs_without_excess_props;
          callee_for_resolution = self.store.intern_type(TypeKind::Callable {
            overloads: candidate_sigs.clone(),
          });
          candidate_sigs.clone()
        }
      };

      let specialized: Vec<_> = base_for_context
        .iter()
        .copied()
        .filter(|sig_id| {
          let sig = self.store.signature(*sig_id);
          signature_contains_literal_types(self.store.as_ref(), &sig)
        })
        .collect();

      if specialized.is_empty() {
        base_for_context
      } else {
        specialized
      }
    };

    let mut arg_types = Vec::with_capacity(call.stx.arguments.len());
    let mut const_arg_types = Vec::with_capacity(call.stx.arguments.len());
    // For each argument expression, record which parameter index it corresponds
    // to. Spread arguments (and arguments after an unknown-length spread) have no
    // stable mapping.
    let mut param_index_map = Vec::with_capacity(call.stx.arguments.len());
    let mut spread_param_index_map = Vec::with_capacity(call.stx.arguments.len());
    let mut mapping_known = true;
    let mut next_param_index = 0usize;

    for arg in call.stx.arguments.iter() {
      if arg.stx.spread {
        spread_param_index_map.push(mapping_known.then_some(next_param_index));
        let ty = if mapping_known {
          match arg.stx.value.stx.as_ref() {
            AstExpr::LitArr(arr) => {
              use parse_js::ast::expr::lit::LitArrElem;

              if arr
                .stx
                .elements
                .iter()
                .all(|elem| matches!(elem, LitArrElem::Single(_)))
              {
                let arity = arr.stx.elements.len();
                let mut expected_elems = Vec::with_capacity(arity);
                for offset in 0..arity {
                  let param_index = next_param_index.saturating_add(offset);
                  let mut expected_tys = Vec::new();
                  for sig_id in sigs_for_context.iter().copied() {
                    let sig = self.store.signature(sig_id);
                    if let Some(param_ty) =
                      expected_arg_type_at(self.store.as_ref(), &sig, param_index)
                    {
                      expected_tys.push(param_ty);
                    }
                  }
                  let expected = if expected_tys.is_empty() {
                    prim.unknown
                  } else {
                    self.store.union(expected_tys)
                  };
                  expected_elems.push(types_ts_interned::TupleElem {
                    ty: expected,
                    optional: false,
                    rest: false,
                    readonly: false,
                  });
                }
                let expected_tuple = self.store.intern_type(TypeKind::Tuple(expected_elems));
                self.check_expr_with_expected(&arg.stx.value, expected_tuple)
              } else {
                self.check_expr(&arg.stx.value)
              }
            }
            _ => self.check_expr(&arg.stx.value),
          }
        } else {
          self.check_expr(&arg.stx.value)
        };
        let arg_span = Span {
          file: self.file,
          range: loc_to_range(self.file, arg.stx.value.loc),
        };
        arg_types.push(CallArgType::spread(ty).with_span(arg_span));
        const_arg_types.push(self.const_inference_type(&arg.stx.value));
        param_index_map.push(None);

        if mapping_known {
          let mut seen = HashSet::new();
          let fixed_len = fixed_spread_len(self.store.as_ref(), ty, self.ref_expander, &mut seen);
          if let Some(fixed_len) = fixed_len {
            next_param_index = next_param_index.saturating_add(fixed_len);
          } else {
            mapping_known = false;
          }
        }
        continue;
      }

      let param_index = mapping_known.then_some(next_param_index);
      param_index_map.push(param_index);
      spread_param_index_map.push(None);

      let ty = if let Some(param_index) = param_index {
        let mut expected_tys = Vec::new();
        for sig_id in sigs_for_context.iter().copied() {
          let sig = self.store.signature(sig_id);
          if let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) {
            expected_tys.push(param_ty);
          }
        }
        let expected = if expected_tys.is_empty() {
          prim.unknown
        } else {
          self.store.union(expected_tys)
        };
        self.check_expr_with_expected(&arg.stx.value, expected)
      } else {
        self.check_expr(&arg.stx.value)
      };

      let arg_span = Span {
        file: self.file,
        range: self.error_range_for_expr(&arg.stx.value),
      };
      arg_types.push(CallArgType::new(ty).with_span(arg_span));
      const_arg_types.push(self.const_inference_type(&arg.stx.value));
      if mapping_known {
        next_param_index = next_param_index.saturating_add(1);
      }
    }

    let mut this_arg = match call.stx.callee.stx.as_ref() {
      AstExpr::Member(mem) => self.recorded_expr_type(mem.stx.left.loc),
      AstExpr::ComputedMember(mem) => self.recorded_expr_type(mem.stx.object.loc),
      _ => None,
    };
    if call_optional {
      if let Some(this_arg_ty) = this_arg.as_mut() {
        *this_arg_ty = narrow_non_nullish(*this_arg_ty, &self.store).0;
      }
    }

    let span = Span {
      file: self.file,
      range: loc_to_range(self.file, call.loc),
    };
    // tsc anchors TS2349 ("This expression is not callable") on the callee, not
    // the whole call. Empty candidate sets use that span; other failures keep the
    // call/argument spans from overload resolution.
    let callee_span = Span {
      file: self.file,
      range: loc_to_range(self.file, call.stx.callee.loc),
    };
    let resolve_span = if all_candidate_sigs.is_empty() {
      callee_span
    } else {
      span
    };

    let mut ty = if call_optional && callee_base == prim.never {
      prim.undefined
    } else {
      let mut resolution = resolve_call(
        &self.store,
        &self.relate,
        &self.instantiation_cache,
        callee_for_resolution,
        &arg_types,
        Some(&const_arg_types),
        this_arg,
        contextual_return,
        resolve_span,
        self.ref_expander,
      );
      if let Some(sig_id) = resolution.signature.or(resolution.contextual_signature) {
        let sig = self.store.signature(sig_id);
        let mut refined = false;
        for (idx, arg) in call.stx.arguments.iter().enumerate() {
          if arg.stx.spread {
            let Some(param_index) = spread_param_index_map.get(idx).and_then(|idx| *idx) else {
              continue;
            };
            let AstExpr::LitArr(arr) = arg.stx.value.stx.as_ref() else {
              continue;
            };
            use parse_js::ast::expr::lit::LitArrElem;
            if arr
              .stx
              .elements
              .iter()
              .any(|elem| !matches!(elem, LitArrElem::Single(_)))
            {
              continue;
            }

            let arity = arr.stx.elements.len();
            let mut expected_elems = Vec::with_capacity(arity);
            for offset in 0..arity {
              let Some(param_ty) = expected_arg_type_at(
                self.store.as_ref(),
                &sig,
                param_index.saturating_add(offset),
              ) else {
                expected_elems.clear();
                break;
              };
              expected_elems.push(types_ts_interned::TupleElem {
                ty: param_ty,
                optional: false,
                rest: false,
                readonly: false,
              });
            }
            if expected_elems.len() != arity {
              continue;
            }

            let expected_tuple = self.store.intern_type(TypeKind::Tuple(expected_elems));
            let spread_ty = self.check_expr_with_expected(&arg.stx.value, expected_tuple);
            if let Some(slot) = arg_types.get_mut(idx) {
              slot.ty = spread_ty;
              refined = true;
            }
            if let Some(slot) = const_arg_types.get_mut(idx) {
              *slot = spread_ty;
            }
            continue;
          }

          let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
            continue;
          };
          let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
            continue;
          };
          let Some(func) = (match arg.stx.value.stx.as_ref() {
            AstExpr::ArrowFunc(arrow) => Some(&arrow.stx.func),
            AstExpr::Func(func) => Some(&func.stx.func),
            _ => None,
          }) else {
            continue;
          };

          let Some(refined_ty) = self.refine_function_expr_with_expected(func, param_ty) else {
            continue;
          };
          if let Some(slot) = arg_types.get_mut(idx) {
            slot.ty = refined_ty;
            refined = true;
          }
          if let Some(slot) = const_arg_types.get_mut(idx) {
            *slot = refined_ty;
          }
          self.record_expr_type(arg.stx.value.loc, refined_ty);
        }

        if refined {
          let next = resolve_call(
            &self.store,
            &self.relate,
            &self.instantiation_cache,
            callee_for_resolution,
            &arg_types,
            Some(&const_arg_types),
            this_arg,
            contextual_return,
            resolve_span,
            self.ref_expander,
          );
          if next.diagnostics.is_empty() && next.signature.is_some() {
            resolution = next;
          }
        }
      }

      let allow_assignable_fallback = resolution.diagnostics.len() == 1
        && is_no_match_overload_code(resolution.diagnostics[0].code.as_str())
        && candidate_sigs.len() == 1;
      let mut reported_assignability = false;
      if allow_assignable_fallback {
        if let Some(sig_id) = resolution
          .contextual_signature
          .or_else(|| candidate_sigs.first().copied())
        {
          let sig = self.store.signature(sig_id);
          let before = self.diagnostics.len();
          for (idx, arg) in call.stx.arguments.iter().enumerate() {
            let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
              continue;
            };
            let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index)
            else {
              continue;
            };
            let arg_ty = arg_types.get(idx).map(|arg| arg.ty).unwrap_or(prim.unknown);
            let expected = match self.store.type_kind(param_ty) {
              TypeKind::TypeParam(id) => sig
                .type_params
                .iter()
                .find(|tp| tp.id == id)
                .and_then(|tp| tp.constraint)
                .unwrap_or(param_ty),
              _ => param_ty,
            };
            self.check_assignable_with_code(
              &arg.stx.value,
              arg_ty,
              expected,
              None,
              &codes::ARGUMENT_TYPE_MISMATCH,
            );
          }
          reported_assignability = self.diagnostics.len() > before;
        }
      }

      if !reported_assignability {
        // Single-signature arity misses: emit TS2554 on the callee name (tsc)
        // instead of leaving the generic TC2000 from overload resolution.
        let reported_arity = if allow_assignable_fallback {
          if let Some(sig_id) = resolution
            .contextual_signature
            .or_else(|| candidate_sigs.first().copied())
          {
            let sig = self.store.signature(sig_id);
            if !has_spread
              && !signature_allows_arg_count(self.store.as_ref(), &sig, arg_types.len())
            {
              let arity_span = self.call_callee_name_span(call, span);
              self
                .diagnostics
                .push(codes::ARGUMENT_COUNT_MISMATCH.error("argument count mismatch", arity_span));
              true
            } else {
              false
            }
          } else {
            false
          }
        } else {
          false
        };
        if !reported_arity {
          for diag in &resolution.diagnostics {
            self.diagnostics.push(diag.clone());
          }
        }
      }
      if resolution.diagnostics.is_empty() {
        if let Some(sig_id) = resolution.signature {
          let sig = self.store.signature(sig_id);
          for (idx, arg) in call.stx.arguments.iter().enumerate() {
            let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
              continue;
            };
            let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index)
            else {
              continue;
            };
            let arg_expr = &arg.stx.value;
            let arg_ty = match arg_expr.stx.as_ref() {
              AstExpr::LitObj(_) | AstExpr::LitArr(_) => {
                let contextual = self.check_expr_with_expected(arg_expr, param_ty);
                if let Some(slot) = arg_types.get_mut(idx) {
                  slot.ty = contextual;
                }
                contextual
              }
              _ => arg_types.get(idx).map(|arg| arg.ty).unwrap_or(prim.unknown),
            };
            let assignable_ty = match arg_expr.stx.as_ref() {
              AstExpr::LitObj(_) | AstExpr::LitArr(_) => {
                let const_ty = const_arg_types.get(idx).copied().unwrap_or(arg_ty);
                if !self.relate.is_assignable(arg_ty, param_ty)
                  && self.relate.is_assignable(const_ty, param_ty)
                {
                  const_ty
                } else {
                  arg_ty
                }
              }
              _ => arg_ty,
            };
            self.check_assignable_with_code(
              arg_expr,
              assignable_ty,
              param_ty,
              None,
              &codes::ARGUMENT_TYPE_MISMATCH,
            );
          }
          if let TypeKind::Predicate {
            parameter,
            asserted: Some(asserted),
            asserts: true,
          } = self.store.type_kind(sig.ret)
          {
            if let PredicateParam::Param(param_idx) = parameter.unwrap_or(PredicateParam::Param(0))
            {
              let param_idx = param_idx as usize;
              if let Some(arg_idx) = param_index_map
                .iter()
                .position(|idx| *idx == Some(param_idx))
              {
                if let Some(arg) = call.stx.arguments.get(arg_idx) {
                  if let AstExpr::Id(id) = arg.stx.value.stx.as_ref() {
                    self.insert_binding(id.stx.name.clone(), asserted, Vec::new());
                  }
                }
              }
            }
          }
          if !has_spread && !signature_allows_arg_count(self.store.as_ref(), &sig, arg_types.len())
          {
            let arity_span = self.call_callee_name_span(call, span);
            self
              .diagnostics
              .push(codes::ARGUMENT_COUNT_MISMATCH.error("argument count mismatch", arity_span));
          }
        }
      }
      let contextual_sig = resolution
        .signature
        .or(resolution.contextual_signature)
        .or_else(|| candidate_sigs.first().copied());
      if let Some(sig_id) = contextual_sig {
        let sig = self.store.signature(sig_id);
        for (idx, arg) in call.stx.arguments.iter().enumerate() {
          let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
            continue;
          };
          let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
            continue;
          };
          let arg_ty = arg_types.get(idx).map(|arg| arg.ty).unwrap_or(prim.unknown);
          let contextual = match arg.stx.value.stx.as_ref() {
            AstExpr::ArrowFunc(_) | AstExpr::Func(_)
              if self.first_callable_signature(param_ty).is_some() =>
            {
              arg_ty
            }
            _ => self.contextual_arg_type(arg_ty, param_ty),
          };
          self.record_expr_type(arg.stx.value.loc, contextual);
        }
      }

      resolution.return_type
    };

    if call_optional {
      ty = self.store.union(vec![ty, prim.undefined]);
    }
    ty
  }

  pub(crate) fn check_new_expr(
    &mut self,
    un: &Node<parse_js::ast::expr::UnaryExpr>,
    expr_loc: Loc,
    contextual_return: Option<TypeId>,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    let (callee_expr, arg_exprs, span_loc) = match un.stx.argument.stx.as_ref() {
      AstExpr::Call(call) => (
        &call.stx.callee,
        Some(call.stx.arguments.as_slice()),
        call.loc,
      ),
      _ => (&un.stx.argument, None, expr_loc),
    };
    let callee_ty = self.check_expr(callee_expr);
    let callee_ty = self.expand_callable_type(callee_ty);
    let arg_exprs = arg_exprs.unwrap_or(&[]);
    let all_candidate_sigs =
      construct_signatures_with_expander(self.store.as_ref(), callee_ty, self.ref_expander);
    let mut candidate_sigs = all_candidate_sigs.clone();
    let has_spread = arg_exprs.iter().any(|arg| arg.stx.spread);
    let mut callee_for_resolution = callee_ty;
    let sigs_for_context = {
      let base_for_context = if has_spread {
        let sigs_without_excess_props: Vec<_> = all_candidate_sigs
          .iter()
          .copied()
          .filter(|sig_id| {
            let sig = self.store.signature(*sig_id);
            arg_exprs
              .iter()
              .enumerate()
              .take_while(|(_, arg)| !arg.stx.spread)
              .all(|(idx, arg)| {
                let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, idx) else {
                  return false;
                };
                !self.has_contextual_excess_properties(&arg.stx.value, param_ty)
              })
          })
          .collect();

        if sigs_without_excess_props.is_empty() {
          candidate_sigs.clone()
        } else {
          candidate_sigs = sigs_without_excess_props;

          let mut shape = Shape::new();
          shape.construct_signatures = candidate_sigs.clone();
          let shape_id = self.store.intern_shape(shape);
          let obj_id = self.store.intern_object(ObjectType { shape: shape_id });
          callee_for_resolution = self.store.intern_type(TypeKind::Object(obj_id));

          candidate_sigs.clone()
        }
      } else {
        let sigs_by_arity: Vec<_> = all_candidate_sigs
          .iter()
          .copied()
          .filter(|sig_id| {
            let sig = self.store.signature(*sig_id);
            signature_allows_arg_count(self.store.as_ref(), &sig, arg_exprs.len())
          })
          .collect();

        let sigs_without_excess_props: Vec<_> = sigs_by_arity
          .iter()
          .copied()
          .filter(|sig_id| {
            let sig = self.store.signature(*sig_id);
            arg_exprs.iter().enumerate().all(|(idx, arg)| {
              let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, idx) else {
                return false;
              };
              !self.has_contextual_excess_properties(&arg.stx.value, param_ty)
            })
          })
          .collect();

        if sigs_without_excess_props.is_empty() {
          if sigs_by_arity.is_empty() {
            all_candidate_sigs.clone()
          } else {
            sigs_by_arity
          }
        } else {
          candidate_sigs = sigs_without_excess_props;

          let mut shape = Shape::new();
          shape.construct_signatures = candidate_sigs.clone();
          let shape_id = self.store.intern_shape(shape);
          let obj_id = self.store.intern_object(ObjectType { shape: shape_id });
          callee_for_resolution = self.store.intern_type(TypeKind::Object(obj_id));

          candidate_sigs.clone()
        }
      };

      let specialized: Vec<_> = base_for_context
        .iter()
        .copied()
        .filter(|sig_id| {
          let sig = self.store.signature(*sig_id);
          signature_contains_literal_types(self.store.as_ref(), &sig)
        })
        .collect();

      if specialized.is_empty() {
        base_for_context
      } else {
        specialized
      }
    };

    let mut arg_types = Vec::with_capacity(arg_exprs.len());
    let mut const_arg_types = Vec::with_capacity(arg_exprs.len());
    // For each argument expression, record which parameter index it corresponds
    // to. Spread arguments (and arguments after an unknown-length spread) have no
    // stable mapping.
    let mut param_index_map = Vec::with_capacity(arg_exprs.len());
    let mut spread_param_index_map = Vec::with_capacity(arg_exprs.len());
    let mut mapping_known = true;
    let mut next_param_index = 0usize;

    for arg in arg_exprs.iter() {
      if arg.stx.spread {
        spread_param_index_map.push(mapping_known.then_some(next_param_index));
        let ty = self.check_expr(&arg.stx.value);
        let arg_span = Span {
          file: self.file,
          range: loc_to_range(self.file, arg.stx.value.loc),
        };
        arg_types.push(CallArgType::spread(ty).with_span(arg_span));
        const_arg_types.push(self.const_inference_type(&arg.stx.value));
        param_index_map.push(None);

        if mapping_known {
          let fixed_len = match arg.stx.value.stx.as_ref() {
            AstExpr::LitArr(arr) => {
              use parse_js::ast::expr::lit::LitArrElem;

              if arr
                .stx
                .elements
                .iter()
                .all(|elem| matches!(elem, LitArrElem::Single(_)))
              {
                Some(arr.stx.elements.len())
              } else {
                None
              }
            }
            _ => {
              let mut seen = HashSet::new();
              fixed_spread_len(self.store.as_ref(), ty, self.ref_expander, &mut seen)
            }
          };
          if let Some(fixed_len) = fixed_len {
            next_param_index = next_param_index.saturating_add(fixed_len);
          } else {
            mapping_known = false;
          }
        }
        continue;
      }

      let param_index = mapping_known.then_some(next_param_index);
      param_index_map.push(param_index);
      spread_param_index_map.push(None);

      let ty = if let Some(param_index) = param_index {
        let mut expected_tys = Vec::new();
        for sig_id in sigs_for_context.iter().copied() {
          let sig = self.store.signature(sig_id);
          if let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) {
            expected_tys.push(param_ty);
          }
        }
        let expected = if expected_tys.is_empty() {
          prim.unknown
        } else {
          self.store.union(expected_tys)
        };
        self.check_expr_with_expected(&arg.stx.value, expected)
      } else {
        self.check_expr(&arg.stx.value)
      };

      let arg_span = Span {
        file: self.file,
        range: self.error_range_for_expr(&arg.stx.value),
      };
      arg_types.push(CallArgType::new(ty).with_span(arg_span));
      const_arg_types.push(self.const_inference_type(&arg.stx.value));
      if mapping_known {
        next_param_index = next_param_index.saturating_add(1);
      }
    }
    let span = Span {
      file: self.file,
      range: loc_to_range(self.file, span_loc),
    };
    let mut resolution = resolve_construct(
      &self.store,
      &self.relate,
      &self.instantiation_cache,
      callee_for_resolution,
      &arg_types,
      Some(&const_arg_types),
      None,
      contextual_return,
      span,
      self.ref_expander,
    );
    if let Some(sig_id) = resolution.signature.or(resolution.contextual_signature) {
      let sig = self.store.signature(sig_id);
      let mut refined = false;
      for (idx, arg) in arg_exprs.iter().enumerate() {
        if arg.stx.spread {
          let Some(param_index) = spread_param_index_map.get(idx).and_then(|idx| *idx) else {
            continue;
          };
          let AstExpr::LitArr(arr) = arg.stx.value.stx.as_ref() else {
            continue;
          };
          use parse_js::ast::expr::lit::LitArrElem;
          if arr
            .stx
            .elements
            .iter()
            .any(|elem| !matches!(elem, LitArrElem::Single(_)))
          {
            continue;
          }

          let arity = arr.stx.elements.len();
          let mut expected_elems = Vec::with_capacity(arity);
          for offset in 0..arity {
            let Some(param_ty) = expected_arg_type_at(
              self.store.as_ref(),
              &sig,
              param_index.saturating_add(offset),
            ) else {
              expected_elems.clear();
              break;
            };
            expected_elems.push(types_ts_interned::TupleElem {
              ty: param_ty,
              optional: false,
              rest: false,
              readonly: false,
            });
          }
          if expected_elems.is_empty() {
            continue;
          }

          let expected_tuple = self.store.intern_type(TypeKind::Tuple(expected_elems));
          let spread_ty = self.check_expr_with_expected(&arg.stx.value, expected_tuple);
          if let Some(slot) = arg_types.get_mut(idx) {
            slot.ty = spread_ty;
            refined = true;
          }
          if let Some(slot) = const_arg_types.get_mut(idx) {
            *slot = spread_ty;
          }
          continue;
        }

        let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
          continue;
        };
        let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
          continue;
        };
        let Some(func) = (match arg.stx.value.stx.as_ref() {
          AstExpr::ArrowFunc(arrow) => Some(&arrow.stx.func),
          AstExpr::Func(func) => Some(&func.stx.func),
          _ => None,
        }) else {
          continue;
        };

        let Some(refined_ty) = self.refine_function_expr_with_expected(func, param_ty) else {
          continue;
        };
        if let Some(slot) = arg_types.get_mut(idx) {
          slot.ty = refined_ty;
          refined = true;
        }
        if let Some(slot) = const_arg_types.get_mut(idx) {
          *slot = refined_ty;
        }
        self.record_expr_type(arg.stx.value.loc, refined_ty);
      }

      if refined {
        let next = resolve_construct(
          &self.store,
          &self.relate,
          &self.instantiation_cache,
          callee_for_resolution,
          &arg_types,
          Some(&const_arg_types),
          None,
          contextual_return,
          span,
          self.ref_expander,
        );
        if next.diagnostics.is_empty() && next.signature.is_some() {
          resolution = next;
        }
      }
    }

    let allow_assignable_fallback = resolution.diagnostics.len() == 1
      && is_no_match_overload_code(resolution.diagnostics[0].code.as_str())
      && candidate_sigs.len() == 1;
    let mut reported_assignability = false;
    if allow_assignable_fallback {
      if let Some(sig_id) = resolution
        .contextual_signature
        .or_else(|| candidate_sigs.first().copied())
      {
        let sig = self.store.signature(sig_id);
        let before = self.diagnostics.len();
        for (idx, arg) in arg_exprs.iter().enumerate() {
          let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
            continue;
          };
          let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
            continue;
          };
          let arg_ty = arg_types.get(idx).map(|arg| arg.ty).unwrap_or(prim.unknown);
          let expected = match self.store.type_kind(param_ty) {
            TypeKind::TypeParam(id) => sig
              .type_params
              .iter()
              .find(|tp| tp.id == id)
              .and_then(|tp| tp.constraint)
              .unwrap_or(param_ty),
            _ => param_ty,
          };
          self.check_assignable_with_code(
            &arg.stx.value,
            arg_ty,
            expected,
            None,
            &codes::ARGUMENT_TYPE_MISMATCH,
          );
        }
        reported_assignability = self.diagnostics.len() > before;
      }
    }

    if !reported_assignability {
      for diag in &resolution.diagnostics {
        self.diagnostics.push(diag.clone());
      }
    }
    if resolution.diagnostics.is_empty() {
      if let Some(sig_id) = resolution.signature {
        let sig = self.store.signature(sig_id);
        for (idx, arg) in arg_exprs.iter().enumerate() {
          let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
            continue;
          };
          let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
            continue;
          };
          let arg_expr = &arg.stx.value;
          let arg_ty = match arg_expr.stx.as_ref() {
            AstExpr::LitObj(_) | AstExpr::LitArr(_) => {
              let contextual = self.check_expr_with_expected(arg_expr, param_ty);
              if let Some(slot) = arg_types.get_mut(idx) {
                slot.ty = contextual;
              }
              contextual
            }
            _ => arg_types.get(idx).map(|arg| arg.ty).unwrap_or(prim.unknown),
          };
          self.check_assignable_with_code(
            arg_expr,
            arg_ty,
            param_ty,
            None,
            &codes::ARGUMENT_TYPE_MISMATCH,
          );
        }
      }
    }
    let contextual_sig = resolution
      .signature
      .or(resolution.contextual_signature)
      .or_else(|| candidate_sigs.first().copied());
    if let Some(sig_id) = contextual_sig {
      let sig = self.store.signature(sig_id);
      for (idx, arg) in arg_exprs.iter().enumerate() {
        let Some(param_index) = param_index_map.get(idx).and_then(|idx| *idx) else {
          continue;
        };
        let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
          continue;
        };
        let arg_ty = arg_types.get(idx).map(|arg| arg.ty).unwrap_or(prim.unknown);
        let contextual = match arg.stx.value.stx.as_ref() {
          AstExpr::ArrowFunc(_) | AstExpr::Func(_)
            if self.first_callable_signature(param_ty).is_some() =>
          {
            arg_ty
          }
          _ => self.contextual_arg_type(arg_ty, param_ty),
        };
        self.record_expr_type(arg.stx.value.loc, contextual);
      }
    }
    resolution.return_type
  }

  /// Type-check a tagged template (`tag\`...\``).
  ///
  /// Packs arguments as `(TemplateStringsArray, ...substitutions)` and resolves
  /// against the tag's call signatures (tsc). Reports TS2349 (via TC2000) on the
  /// tag span when the tag is not callable.
  pub(crate) fn check_tagged_template_expr(
    &mut self,
    tagged: &Node<parse_js::ast::expr::TaggedTemplateExpr>,
  ) -> TypeId {
    use parse_js::ast::expr::lit::LitTemplatePart;

    let prim = self.store.primitive_ids();
    let tag_ty = self.check_expr(&tagged.stx.function);
    let tag_ty = self.expand_callable_type(tag_ty);

    let mut subst_exprs = Vec::new();
    for part in tagged.stx.parts.iter() {
      if let LitTemplatePart::Substitution(expr) = part {
        subst_exprs.push(expr);
      }
    }

    if matches!(
      self.store.type_kind(tag_ty),
      TypeKind::Any | TypeKind::Unknown
    ) {
      for expr in subst_exprs.iter() {
        let _ = self.check_expr(expr);
      }
      return prim.unknown;
    }

    let sigs = callable_signatures_with_expander(self.store.as_ref(), tag_ty, self.ref_expander);
    if sigs.is_empty() {
      for expr in subst_exprs.iter() {
        let _ = self.check_expr(expr);
      }
      let tag_span = Span {
        file: self.file,
        range: loc_to_range(self.file, tagged.stx.function.loc),
      };
      self.diagnostics.push(
        codes::NO_OVERLOAD
          .error("expression is not callable", tag_span)
          .with_note(format!(
            "callee has type {}",
            TypeDisplay::new(self.store.as_ref(), tag_ty)
          )),
      );
      return prim.unknown;
    }

    let strings_ty = self.template_strings_array_type();
    let mut arg_types = Vec::with_capacity(subst_exprs.len() + 1);
    let mut const_arg_types = Vec::with_capacity(subst_exprs.len() + 1);
    arg_types.push(CallArgType::new(strings_ty));
    const_arg_types.push(strings_ty);

    for (subst_idx, expr) in subst_exprs.iter().enumerate() {
      // Parameter index 0 is TemplateStringsArray; substitutions start at 1.
      let param_index = subst_idx + 1;
      let mut expected_tys = Vec::new();
      for sig_id in sigs.iter().copied() {
        let sig = self.store.signature(sig_id);
        if let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) {
          expected_tys.push(param_ty);
        }
      }
      let expected = if expected_tys.is_empty() {
        None
      } else if expected_tys.len() == 1 {
        Some(expected_tys[0])
      } else {
        Some(self.store.union(expected_tys))
      };
      if std::env::var("DEBUG_TAGGED").is_ok() {
        eprintln!(
          "DEBUG_TAGGED subst {} expected={}",
          subst_idx,
          expected
            .map(|t| TypeDisplay::new(self.store.as_ref(), t).to_string())
            .unwrap_or_else(|| "none".to_string())
        );
      }
      let ty = match expected {
        Some(expected) => self.check_expr_with_expected(expr, expected),
        None => self.check_expr(expr),
      };
      let arg_span = Span {
        file: self.file,
        range: loc_to_range(self.file, expr.loc),
      };
      arg_types.push(CallArgType::new(ty).with_span(arg_span));
      const_arg_types.push(self.const_inference_type(expr));
    }

    let tagged_span = Span {
      file: self.file,
      range: loc_to_range(self.file, tagged.loc),
    };
    let mut resolution = resolve_call(
      &self.store,
      &self.relate,
      &self.instantiation_cache,
      tag_ty,
      &arg_types,
      Some(&const_arg_types),
      None,
      None,
      tagged_span,
      self.ref_expander,
    );

    if let Some(sig_id) = resolution.signature.or(resolution.contextual_signature) {
      let sig = self.store.signature(sig_id);
      let mut refined = false;
      for (idx, expr) in subst_exprs.iter().enumerate() {
        let param_index = idx + 1;
        let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
          continue;
        };
        let Some(func) = (match expr.stx.as_ref() {
          AstExpr::ArrowFunc(arrow) => Some(&arrow.stx.func),
          AstExpr::Func(func) => Some(&func.stx.func),
          _ => None,
        }) else {
          continue;
        };
        let Some(refined_ty) = self.refine_function_expr_with_expected(func, param_ty) else {
          continue;
        };
        if let Some(slot) = arg_types.get_mut(param_index) {
          slot.ty = refined_ty;
          refined = true;
        }
        if let Some(slot) = const_arg_types.get_mut(param_index) {
          *slot = refined_ty;
        }
        self.record_expr_type(expr.loc, refined_ty);
      }
      if refined {
        let next = resolve_call(
          &self.store,
          &self.relate,
          &self.instantiation_cache,
          tag_ty,
          &arg_types,
          Some(&const_arg_types),
          None,
          None,
          tagged_span,
          self.ref_expander,
        );
        if next.diagnostics.is_empty() && next.signature.is_some() {
          resolution = next;
        }
      }
    }

    // Single-signature misses: rewrite TC2000 → TS2345 on the first mismatched
    // substitution (tsc reports only the first rest-arg failure).
    let allow_assignable_fallback = resolution.diagnostics.len() == 1
      && is_no_match_overload_code(resolution.diagnostics[0].code.as_str())
      && sigs.len() == 1;
    let mut reported_assignability = false;
    if allow_assignable_fallback {
      if let Some(sig_id) = resolution
        .contextual_signature
        .or_else(|| sigs.first().copied())
      {
        let sig = self.store.signature(sig_id);
        let before = self.diagnostics.len();
        for (idx, expr) in subst_exprs.iter().enumerate() {
          let param_index = idx + 1;
          let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
            continue;
          };
          let arg_ty = arg_types
            .get(param_index)
            .map(|arg| arg.ty)
            .unwrap_or(prim.unknown);
          let len_before = self.diagnostics.len();
          self.check_assignable_with_code(
            expr,
            arg_ty,
            param_ty,
            None,
            &codes::ARGUMENT_TYPE_MISMATCH,
          );
          if self.diagnostics.len() > len_before {
            break;
          }
        }
        reported_assignability = self.diagnostics.len() > before;
      }
    }

    if !reported_assignability {
      for diag in &resolution.diagnostics {
        self.diagnostics.push(diag.clone());
      }
    }

    if resolution.diagnostics.is_empty() {
      if let Some(sig_id) = resolution.signature {
        let sig = self.store.signature(sig_id);
        for (idx, expr) in subst_exprs.iter().enumerate() {
          let param_index = idx + 1;
          let Some(param_ty) = expected_arg_type_at(self.store.as_ref(), &sig, param_index) else {
            continue;
          };
          let arg_ty = arg_types
            .get(param_index)
            .map(|arg| arg.ty)
            .unwrap_or(prim.unknown);
          let len_before = self.diagnostics.len();
          self.check_assignable_with_code(
            expr,
            arg_ty,
            param_ty,
            None,
            &codes::ARGUMENT_TYPE_MISMATCH,
          );
          // Match tsc: one TS2345 per tagged-template call for rest mismatches.
          if self.diagnostics.len() > len_before {
            break;
          }
        }
      }
    }

    resolution.return_type
  }

  /// First argument type of a tagged template: global `TemplateStringsArray`, or
  /// a structural `readonly string[]` + `raw` stand-in when the lib type is absent.
  pub(crate) fn template_strings_array_type(&mut self) -> TypeId {
    if let Some(resolver) = self.type_resolver.as_ref() {
      if let Some(def) = resolver.resolve_type_name(&["TemplateStringsArray".to_string()]) {
        let ref_ty = self.store.canon(self.store.intern_type(TypeKind::Ref {
          def,
          args: Vec::new(),
        }));
        let expanded = self.expand_ref(ref_ty);
        if !matches!(
          self.store.type_kind(expanded),
          TypeKind::Unknown | TypeKind::Any
        ) {
          return expanded;
        }
      }
    }

    let prim = self.store.primitive_ids();
    let string_arr = self.store.intern_type(TypeKind::Array {
      ty: prim.string,
      readonly: true,
    });
    let mut shape = Shape::new();
    shape.properties.push(types_ts_interned::Property {
      key: types_ts_interned::PropKey::String(self.store.intern_name("raw")),
      data: types_ts_interned::PropData {
        ty: string_arr,
        optional: false,
        readonly: true,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    });
    shape.indexers.push(types_ts_interned::Indexer {
      key_type: prim.number,
      value_type: prim.string,
      readonly: true,
    });
    let shape_id = self.store.intern_shape(shape);
    let obj = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj))
  }

  /// Span for TS2554: callee property / identifier name (tsc anchors `#method`).
  fn call_callee_name_span(
    &self,
    call: &Node<parse_js::ast::expr::CallExpr>,
    fallback: Span,
  ) -> Span {
    match call.stx.callee.stx.as_ref() {
      AstExpr::Member(mem) => {
        let full = loc_to_range(self.file, mem.loc);
        let prop_len = mem.stx.right.len() as u32;
        Span {
          file: self.file,
          range: TextRange::new(full.end.saturating_sub(prop_len), full.end),
        }
      }
      AstExpr::Id(id) => Span {
        file: self.file,
        range: loc_to_range(self.file, id.loc),
      },
      _ => fallback,
    }
  }
}

fn is_no_match_overload_code(code: &str) -> bool {
  code == codes::NO_OVERLOAD.as_str() || code == codes::NO_OVERLOAD_MATCHES.as_str()
}
