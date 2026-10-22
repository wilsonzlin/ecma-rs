use std::collections::{HashMap, HashSet};

use diagnostics::{FileId, Span};
use hir_js::hir::SwitchCase;
use hir_js::{
  BinaryOp, ExprId, ExprKind, MemberExpr, NameId, ObjectKey, ObjectLiteral, ObjectProperty, PatId,
  PatKind, StmtKind, UnaryOp,
};
use types_ts_interned::{
  ObjectType, Param as SigParam, PropData, PropKey, RelateTypeExpander, Shape, Signature,
  SignatureId, TypeDisplay, TypeId, TypeKind, TypeStore,
};

use super::super::super::flow::{BindingKey, Env, FlowKey, InitState, PathSegment};
use super::super::super::flow_bindings::FlowBindingId;
use super::super::super::flow_narrow::{
  narrow_by_assignability, narrow_by_discriminant_path, narrow_by_literal,
  narrow_by_nullish_equality, narrow_by_typeof, narrow_non_nullish, truthy_falsy_types, Facts,
  LiteralValue,
};
use super::super::super::overload::{callable_signatures, callable_signatures_with_expander};
use crate::codes;

use super::super::parse_canonical_index_str;

use super::bindings::DaSubstTarget;
use super::{
  classify_computed_obj_key, synthesize_computed_indexers, BindingMode, ComputedObjKey,
  FlowBodyChecker, Reference, SwitchDiscriminant,
};

/// Expand a `TypeKind::Ref` chain with an optional relation expander (same
/// visited-set guard as `FlowBodyChecker::expand_ref`).
fn expand_with_expander(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
) -> TypeId {
  let mut current = store.canon(ty);
  let Some(expander) = expander else {
    return current;
  };
  let mut seen = HashSet::new();
  while seen.insert(current) {
    match store.type_kind(current) {
      TypeKind::Ref { def, args } => {
        if let Some(expanded) = expander.expand_ref(store, def, &args) {
          current = store.canon(expanded);
          continue;
        }
      }
      _ => {}
    }
    break;
  }
  current
}

/// Find a named property on an object-shaped type. Intersection members are
/// searched in declaration order; unions are distributed by the callers.
fn protocol_prop(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
  pred: &dyn Fn(&TypeStore, PropKey) -> bool,
) -> Option<TypeId> {
  let ty = expand_with_expander(store, expander, ty);
  match store.type_kind(ty) {
    TypeKind::Object(obj) => {
      let shape = store.shape(store.object(obj).shape);
      shape
        .properties
        .iter()
        .find(|prop| pred(store, prop.key.clone()))
        .map(|prop| prop.data.ty)
    }
    TypeKind::Intersection(members) => members
      .iter()
      .find_map(|member| protocol_prop(store, expander, *member, pred)),
    _ => None,
  }
}

/// Return type of the first call signature of a callable-typed property.
fn protocol_call_return(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
) -> Option<TypeId> {
  let ty = expand_with_expander(store, expander, ty);
  let sigs = callable_signatures_with_expander(store, ty, expander);
  sigs.first().map(|id| store.signature(*id).ret)
}

/// `next()`'s return type, awaited: the async iterator protocol resolves
/// `Promise<IteratorResult<T>>`, the sync one `IteratorResult<T>` (awaiting
/// is a no-op for non-thenables). tsc unwraps the promise before reading
/// `value` (`types.forAwait.es2018.1.ts`).
fn protocol_call_return_awaited(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
) -> Option<TypeId> {
  protocol_call_return(store, expander, ty)
    .map(|ret| crate::check::hir_body::awaited_type(store, ret, expander))
}

fn value_key(_store: &TypeStore, key: PropKey) -> bool {
  matches!(key, PropKey::String(name) if _store.name(name) == "value")
}

fn done_key(_store: &TypeStore, key: PropKey) -> bool {
  matches!(key, PropKey::String(name) if _store.name(name) == "done")
}

/// `value` of an `IteratorResult`-ish return type. Union members whose `done`
/// is the `true` literal sit in the *return* position, not the yield position,
/// so they are skipped when a yielding member exists — this is how tsc keeps
/// `IteratorResult<T, TReturn>` iterating as `T` rather than `T | TReturn`.
fn iterator_result_value(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
) -> Option<TypeId> {
  let ty = expand_with_expander(store, expander, ty);
  match store.type_kind(ty) {
    TypeKind::Union(members) => {
      let mut kept = Vec::new();
      let mut all = Vec::new();
      for member in members {
        let Some(value) = protocol_prop(store, expander, member, &value_key) else {
          continue;
        };
        all.push(value);
        let done_true = protocol_prop(store, expander, member, &done_key)
          .map(|done| {
            matches!(
              store.type_kind(expand_with_expander(store, expander, done)),
              TypeKind::BooleanLiteral(true)
            )
          })
          .unwrap_or(false);
        if !done_true {
          kept.push(value);
        }
      }
      let pick = if kept.is_empty() { all } else { kept };
      if pick.is_empty() {
        None
      } else {
        Some(store.union(pick))
      }
    }
    _ => protocol_prop(store, expander, ty, &value_key),
  }
}

/// `next().value` element for one candidate iterator object.
fn iterator_element_via_next(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  iterator: TypeId,
) -> Option<TypeId> {
  let next = protocol_prop(store, expander, iterator, &|store, key| match key {
    PropKey::String(name) => store.name(name) == "next",
    _ => false,
  })?;
  let next_ret = protocol_call_return_awaited(store, expander, next)?;
  iterator_result_value(store, expander, next_ret)
}

/// Element type of the synchronous iterable protocol
/// (`[Symbol.iterator]().next().value`) for spreading or `for…of` over a
/// non-array object type — the structural counterpart of tsc
/// `getIterationTypeOfIterable`'s sync path.
///
/// Returns `None` when the type does not expose the protocol; callers keep
/// their existing `unknown` fallback (no TS2488-style diagnostics yet).
pub(crate) fn iterable_protocol_element(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
) -> Option<TypeId> {
  iterable_protocol_element_for(store, expander, ty, "iterator")
}

/// Like [`iterable_protocol_element`], but resolved through a chosen
/// well-known-symbol protocol (`"iterator"` for sync, `"asyncIterator"` for
/// `for await`).
pub(crate) fn iterable_protocol_element_for(
  store: &TypeStore,
  expander: Option<&dyn RelateTypeExpander>,
  ty: TypeId,
  symbol: &str,
) -> Option<TypeId> {
  let qualified = format!("Symbol.{symbol}");
  let iterator_method = protocol_prop(store, expander, ty, &|store, key| match key {
    PropKey::Symbol(name) => {
      let name = store.name(name);
      name == symbol || name == qualified
    }
    _ => false,
  })?;
  let iterator = protocol_call_return(store, expander, iterator_method)?;
  // Hand-written iterables overwhelmingly `return this`. When the method's
  // return type is a stale or degraded snapshot (e.g. method return inference
  // that saw `this` before other members' returns were refined) and yields no
  // usable `next`, retry with the input object as its own iterator.
  if let Some(elem) = iterator_element_via_next(store, expander, iterator) {
    return Some(elem);
  }
  iterator_element_via_next(store, expander, ty)
}

impl<'a> FlowBodyChecker<'a> {
  pub(crate) fn optional_chain_equality_facts(
    &mut self,
    expr: ExprId,
    other: ExprId,
    other_ty: TypeId,
    op: BinaryOp,
    env: &Env,
    out: &mut Facts,
  ) {
    let prim = self.store.primitive_ids();
    let mut bases = Vec::new();
    self.optional_chain_base_keys(expr, &mut bases);
    if bases.is_empty() {
      return;
    }

    let effective_other_ty = match self.literal_value(other) {
      Some(LiteralValue::Undefined) => {
        let binding = self.ident_binding(other);
        let binding_key = binding.and_then(|id| self.bindings.binding_for_flow(id));
        if binding_key.is_none() || matches!(binding_key, Some(BindingKey::External(_))) {
          prim.undefined
        } else {
          other_ty
        }
      }
      Some(LiteralValue::Null) => prim.null,
      _ => other_ty,
    };

    pub(crate) fn insert_fact(
      store: &TypeStore,
      target: &mut HashMap<FlowKey, TypeId>,
      key: FlowKey,
      ty: TypeId,
    ) {
      target
        .entry(key)
        .and_modify(|existing| *existing = store.intersection(vec![*existing, ty]))
        .or_insert(ty);
    }

    let negate = matches!(op, BinaryOp::Inequality | BinaryOp::StrictInequality);
    let (eq_target, neq_target) = if negate {
      (&mut out.falsy, &mut out.truthy)
    } else {
      (&mut out.truthy, &mut out.falsy)
    };

    if self.excludes_nullish(effective_other_ty) {
      for base in bases.iter() {
        let base_ty = self.flow_key_type(env, base);
        let (non_nullish, _) = narrow_non_nullish(base_ty, &self.store);
        if non_nullish != prim.never {
          insert_fact(self.store.as_ref(), eq_target, base.clone(), non_nullish);
        }
      }
      return;
    }

    if self.is_nullish_only(effective_other_ty) {
      let op_for_equality = match op {
        BinaryOp::Inequality => BinaryOp::Equality,
        BinaryOp::StrictInequality => BinaryOp::StrictEquality,
        _ => op,
      };
      let (other_undefined, _) = narrow_by_nullish_equality(
        effective_other_ty,
        op_for_equality,
        &LiteralValue::Undefined,
        &self.store,
      );
      if other_undefined != prim.never {
        for base in bases.iter() {
          let base_ty = self.flow_key_type(env, base);
          let (non_nullish, _) = narrow_non_nullish(base_ty, &self.store);
          if non_nullish != prim.never {
            insert_fact(self.store.as_ref(), neq_target, base.clone(), non_nullish);
          }
        }
        if bases.len() == 1 {
          if let Some(exec_ty) = self.optional_chain_exec_type(expr) {
            let (_, exec_nullish) = narrow_non_nullish(exec_ty, &self.store);
            if exec_nullish == prim.never {
              let base = &bases[0];
              let base_ty = self.flow_key_type(env, base);
              let (_, base_nullish) = narrow_non_nullish(base_ty, &self.store);
              if base_nullish != prim.never {
                insert_fact(self.store.as_ref(), eq_target, base.clone(), base_nullish);
              }
            }
          }
        }
      }
    }
  }

  pub(crate) fn flow_key_for_expr(&self, expr_id: ExprId) -> Option<FlowKey> {
    if let Some(binding) = self.ident_binding(expr_id) {
      return Some(FlowKey::root(binding));
    }
    if let ExprKind::Member(mem) = &self.body.exprs[expr_id.0 as usize].kind {
      let (binding, segments, _) = self.member_path_target(mem.object, &mem.property)?;
      let mut key = FlowKey::root(binding);
      for seg in segments {
        key = key.with_segment(seg);
      }
      return Some(key);
    }
    None
  }

  pub(crate) fn optional_chain_exec_type(&self, expr_id: ExprId) -> Option<TypeId> {
    self
      .optional_chain_exec_types
      .get(expr_id.0 as usize)
      .copied()
      .flatten()
  }

  pub(crate) fn optional_chain_exec_type_for(&self, expr_id: ExprId, fallback: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    let Some(exec) = self.optional_chain_exec_type(expr_id) else {
      return fallback;
    };
    let (overlap, _) = narrow_by_assignability(exec, fallback, &self.store, &self.relate);
    if overlap != prim.never {
      overlap
    } else {
      fallback
    }
  }

  pub(crate) fn record_optional_chain_exec_type(&mut self, expr_id: ExprId, ty: TypeId) {
    let prim = self.store.primitive_ids();
    let slot = self
      .optional_chain_exec_types
      .get_mut(expr_id.0 as usize)
      .unwrap();
    let merged = match slot {
      None => ty,
      Some(prev) if *prev == prim.unknown => ty,
      Some(prev) => self.store.union(vec![*prev, ty]),
    };
    *slot = Some(merged);
  }

  pub(crate) fn optional_chain_base_exprs(&self, expr_id: ExprId, out: &mut Vec<ExprId>) {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Member(mem) => {
        self.optional_chain_base_exprs(mem.object, out);
        if mem.optional {
          out.push(mem.object);
        }
      }
      ExprKind::Call(call) => {
        self.optional_chain_base_exprs(call.callee, out);
        if call.optional {
          out.push(call.callee);
        }
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. } => {
        self.optional_chain_base_exprs(*expr, out);
      }
      _ => {}
    }
  }

  pub(crate) fn optional_chain_base_keys(&self, expr_id: ExprId, out: &mut Vec<FlowKey>) {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Member(mem) => {
        self.optional_chain_base_keys(mem.object, out);
        if mem.optional {
          if let Some(key) = self.flow_key_for_expr(mem.object) {
            out.push(key);
          }
        }
      }
      ExprKind::Call(call) => {
        self.optional_chain_base_keys(call.callee, out);
        if call.optional {
          if let Some(key) = self.flow_key_for_expr(call.callee) {
            out.push(key);
          }
        }
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. } => {
        self.optional_chain_base_keys(*expr, out);
      }
      _ => {}
    }
  }

  pub(crate) fn flow_key_type(&self, env: &Env, key: &FlowKey) -> TypeId {
    let prim = self.store.primitive_ids();
    if let Some(ty) = env.get_path(key) {
      return ty;
    }
    let root_ty = env
      .get(key.root)
      .or_else(|| self.initial.get(&key.root).copied())
      .unwrap_or(prim.unknown);
    if key.segments.is_empty() {
      return root_ty;
    }
    self
      .object_prop_type_path(root_ty, &key.segments)
      .unwrap_or(prim.unknown)
  }

  pub(crate) fn optional_chain_short_circuits(&self, expr_id: ExprId, env: &Env) -> bool {
    let prim = self.store.primitive_ids();
    let mut bases = Vec::new();
    self.optional_chain_base_exprs(expr_id, &mut bases);
    for base in bases {
      let base_ty = if let Some(key) = self.flow_key_for_expr(base) {
        self.flow_key_type(env, &key)
      } else {
        self
          .expr_types
          .get(base.0 as usize)
          .copied()
          .unwrap_or(prim.unknown)
      };
      let (_, nullish) = narrow_non_nullish(base_ty, &self.store);
      if nullish != prim.never {
        return true;
      }
    }
    false
  }

  pub(crate) fn insert_optional_chain_truthy_facts(
    &self,
    expr_id: ExprId,
    env: &Env,
    facts: &mut Facts,
  ) {
    let prim = self.store.primitive_ids();
    let mut bases = Vec::new();
    self.optional_chain_base_keys(expr_id, &mut bases);
    for base in bases {
      let base_ty = self.flow_key_type(env, &base);
      let (non_nullish, _) = narrow_non_nullish(base_ty, &self.store);
      if non_nullish != prim.never {
        facts.truthy.insert(base, non_nullish);
      }
    }
  }

  pub(crate) fn excludes_nullish(&self, ty: TypeId) -> bool {
    let prim = self.store.primitive_ids();
    let (_, nullish) = narrow_non_nullish(ty, &self.store);
    nullish == prim.never
  }

  pub(crate) fn is_nullish_only(&self, ty: TypeId) -> bool {
    let prim = self.store.primitive_ids();
    let (non_nullish, nullish) = narrow_non_nullish(ty, &self.store);
    non_nullish == prim.never && nullish != prim.never
  }

  pub(crate) fn type_contains_undefined(&self, ty: TypeId) -> bool {
    pub(crate) fn inner(
      checker: &FlowBodyChecker<'_>,
      ty: TypeId,
      seen: &mut HashSet<TypeId>,
    ) -> bool {
      let ty = checker.store.canon(ty);
      if !seen.insert(ty) {
        return false;
      }
      let ty = checker.expand_ref(ty);
      match checker.store.type_kind(ty) {
        TypeKind::Any | TypeKind::Unknown => false,
        TypeKind::Undefined => true,
        TypeKind::Union(members) | TypeKind::Intersection(members) => members
          .iter()
          .copied()
          .any(|member| inner(checker, member, seen)),
        _ => false,
      }
    }

    let mut seen = HashSet::new();
    inner(self, ty, &mut seen)
  }

  pub(crate) fn ident_binding(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    match self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.bindings.binding_for_expr(expr_id),
      _ => None,
    }
  }

  pub(crate) fn nullish_coalesce_binding(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.ident_binding(expr_id),
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. } => self.nullish_coalesce_binding(*expr),
      _ => None,
    }
  }

  pub(crate) fn literal_value(&self, expr_id: ExprId) -> Option<LiteralValue> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) if self.hir_name(*name) == "undefined" => {
        let binding = self.ident_binding(expr_id);
        let binding_key = binding.and_then(|id| self.bindings.binding_for_flow(id));
        match binding_key {
          Some(BindingKey::External(_)) | None => Some(LiteralValue::Undefined),
          _ => None,
        }
      }
      ExprKind::Literal(lit) => match lit {
        hir_js::Literal::String(s) => Some(LiteralValue::String(s.lossy.clone())),
        hir_js::Literal::Number(n) => Some(LiteralValue::Number(n.clone())),
        hir_js::Literal::Boolean(b) => Some(LiteralValue::Boolean(*b)),
        hir_js::Literal::Null => Some(LiteralValue::Null),
        hir_js::Literal::Undefined => Some(LiteralValue::Undefined),
        _ => None,
      },
      // `` `lit` `` (no substitutions) is a string literal for narrowing.
      ExprKind::Template(t) if t.spans.is_empty() => Some(LiteralValue::String(t.head.clone())),
      _ => None,
    }
  }

  pub(crate) fn literal_prop(&self, expr_id: ExprId) -> Option<String> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Literal(hir_js::Literal::String(s)) => Some(s.lossy.clone()),
      ExprKind::Template(t) if t.spans.is_empty() => Some(t.head.clone()),
      _ => None,
    }
  }

  /// `#priv` left operand of `#priv in expr` (HIR lowers private-in as Ident).
  pub(crate) fn private_ident_name(&self, expr_id: ExprId) -> Option<String> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(name) => {
        let s = self.hir_name(*name);
        s.starts_with('#').then_some(s)
      }
      _ => None,
    }
  }

  /// Flow-aware `in`-RHS operand checks for bare identifiers (TS18046 /
  /// TS18047 / TS18048). tsc `checkInExpression` uses the flow type of a
  /// reference RHS, so `x !== null` / `typeof` narrowing must be visible here.
  pub(crate) fn check_in_rhs_flow(&mut self, right: ExprId, right_ty: TypeId) {
    let prim = self.store.primitive_ids();
    let ty = self.expand_ref(right_ty);
    let span = Span {
      file: self.file,
      range: self.body.exprs[right.0 as usize].span,
    };
    let name = match &self.body.exprs[right.0 as usize].kind {
      ExprKind::Ident(id) => self.hir_name(*id),
      _ => "object".to_string(),
    };
    if ty == prim.unknown {
      self
        .diagnostics
        .push(codes::IS_OF_TYPE_UNKNOWN.error(format!("'{name}' is of type 'unknown'."), span));
      return;
    }
    match self.store.type_kind(ty) {
      TypeKind::Null => {
        self
          .diagnostics
          .push(codes::POSSIBLY_NULL.error(format!("'{name}' is possibly 'null'."), span));
      }
      TypeKind::Undefined => {
        self.diagnostics.push(
          codes::POSSIBLY_UNDEFINED.error(format!("'{name}' is possibly 'undefined'."), span),
        );
      }
      TypeKind::Union(members) => {
        let has_null = members.iter().any(|&m| self.expand_ref(m) == prim.null);
        let has_undefined = members
          .iter()
          .any(|&m| self.expand_ref(m) == prim.undefined);
        if has_null && !has_undefined {
          self
            .diagnostics
            .push(codes::POSSIBLY_NULL.error(format!("'{name}' is possibly 'null'."), span));
        } else if has_undefined && !has_null {
          self.diagnostics.push(
            codes::POSSIBLY_UNDEFINED.error(format!("'{name}' is possibly 'undefined'."), span),
          );
        } else if has_null && has_undefined {
          self
            .diagnostics
            .push(codes::POSSIBLY_NULL.error(format!("'{name}' is possibly 'null'."), span));
        }
      }
      _ => {}
    }
  }

  pub(crate) fn assignment_target_root_expr(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.ident_binding(expr_id),
      ExprKind::Member(mem) => self.assignment_target_root_expr(mem.object),
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. }
      | ExprKind::Await { expr }
      | ExprKind::Yield {
        expr: Some(expr), ..
      } => self.assignment_target_root_expr(*expr),
      _ => None,
    }
  }

  pub(crate) fn record_assignment_facts(
    &self,
    root: Option<FlowBindingId>,
    ty: TypeId,
    facts: &mut Facts,
  ) {
    if let Some(binding) = root {
      let (truthy, falsy) = truthy_falsy_types(ty, &self.store);
      let key = FlowKey::root(binding);
      facts.truthy.insert(key.clone(), truthy);
      facts.falsy.insert(key, falsy);
    }
  }

  pub(crate) fn apply_binding_mode(&self, ty: TypeId, mode: BindingMode) -> TypeId {
    match mode {
      BindingMode::Declare => ty,
      BindingMode::Assign => self.base_type(ty),
    }
  }

  pub(crate) fn expand_ref(&self, ty: TypeId) -> TypeId {
    let mut current = self.store.canon(ty);
    if let Some(expander) = self.ref_expander {
      let mut seen = HashSet::new();
      while seen.insert(current) {
        match self.store.type_kind(current) {
          TypeKind::Ref { def, args } => {
            if let Some(expanded) = expander.expand_ref(&self.store, def, &args) {
              current = self.store.canon(expanded);
              continue;
            }
          }
          _ => {}
        }
        break;
      }
    }
    current
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

  pub(crate) fn for_of_element_type(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      // `any` iterates as `any` (not `unknown`): downstream assignment checks
      // must not be poisoned by the loop variable's type.
      TypeKind::Any => prim.any,
      TypeKind::Union(members) => {
        let mut elems = Vec::new();
        for member in members {
          elems.push(self.for_of_element_type(member));
        }
        self.store.union(elems)
      }
      TypeKind::Intersection(members) => {
        let mut elems = Vec::new();
        for member in members {
          elems.push(self.for_of_element_type(member));
        }
        self.store.intersection(elems)
      }
      TypeKind::Array { ty, .. } => ty,
      TypeKind::Tuple(elems) => {
        let mut members = Vec::new();
        for elem in elems {
          members.push(elem.ty);
        }
        self.store.union(members)
      }
      TypeKind::String | TypeKind::StringLiteral(_) => prim.string,
      _ => iterable_protocol_element(&self.store, self.ref_expander, ty).unwrap_or(prim.unknown),
    }
  }

  pub(crate) fn is_bigint_like(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::BigInt | TypeKind::BigIntLiteral(_) => true,
      TypeKind::Union(members) => members.iter().all(|m| self.is_bigint_like(*m)),
      TypeKind::Intersection(members) => members.iter().all(|m| self.is_bigint_like(*m)),
      _ => false,
    }
  }

  pub(crate) fn maybe_string(&self, ty: TypeId) -> bool {
    match self.store.type_kind(ty) {
      TypeKind::String | TypeKind::StringLiteral(_) => true,
      TypeKind::Union(members) | TypeKind::Intersection(members) => {
        members.iter().any(|m| self.maybe_string(*m))
      }
      _ => false,
    }
  }

  pub(crate) fn split_nullish(&self, ty: TypeId) -> (TypeId, TypeId) {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::Union(members) => {
        let mut non_nullish = Vec::new();
        let mut nullish = Vec::new();
        for member in members {
          let (nonnull, nulls) = self.split_nullish(member);
          if nonnull != prim.never {
            non_nullish.push(nonnull);
          }
          if nulls != prim.never {
            nullish.push(nulls);
          }
        }
        (self.store.union(non_nullish), self.store.union(nullish))
      }
      TypeKind::Null | TypeKind::Undefined => (prim.never, ty),
      _ => (ty, prim.never),
    }
  }

  pub(crate) fn hir_name(&self, id: NameId) -> String {
    self
      .names
      .resolve(id)
      .map(|s| s.to_owned())
      .unwrap_or_default()
  }

  pub(crate) fn member_property_name(&self, property: &ObjectKey) -> Option<String> {
    match property {
      ObjectKey::Ident(id) => Some(self.hir_name(*id)),
      ObjectKey::String(s) => Some(s.clone()),
      ObjectKey::Number(n) => Some(n.clone()),
      ObjectKey::Computed(expr) => self.literal_value(*expr).and_then(|lit| match lit {
        LiteralValue::String(s) | LiteralValue::Number(s) => Some(s),
        _ => None,
      }),
    }
  }

  pub(crate) fn member_path_segment(&self, property: &ObjectKey) -> Option<PathSegment> {
    match property {
      ObjectKey::Ident(id) => Some(PathSegment::String(self.hir_name(*id))),
      ObjectKey::String(s) => Some(PathSegment::String(s.clone())),
      ObjectKey::Number(n) => Some(PathSegment::Number(n.clone())),
      ObjectKey::Computed(expr) => self.literal_value(*expr).and_then(|lit| match lit {
        LiteralValue::String(s) => Some(PathSegment::String(s)),
        LiteralValue::Number(s) => Some(PathSegment::Number(s)),
        _ => None,
      }),
    }
  }

  pub(crate) fn member_path_target(
    &self,
    object: ExprId,
    property: &ObjectKey,
  ) -> Option<(FlowBindingId, Vec<PathSegment>, ExprId)> {
    let segment = self.member_path_segment(property)?;
    if let Some(binding) = self.ident_binding(object) {
      return Some((binding, vec![segment], object));
    }
    if let ExprKind::Member(MemberExpr {
      object, property, ..
    }) = &self.body.exprs[object.0 as usize].kind
    {
      let (binding, mut segments, root_expr) = self.member_path_target(*object, property)?;
      segments.push(segment);
      return Some((binding, segments, root_expr));
    }
    None
  }

  pub(crate) fn object_prop_type_path(&self, obj: TypeId, path: &[PathSegment]) -> Option<TypeId> {
    let mut ty = obj;
    for seg in path {
      let key = match seg {
        PathSegment::String(s) | PathSegment::Number(s) => s.as_str(),
      };
      ty = self.object_prop_type(ty, key)?;
    }
    Some(ty)
  }

  pub(crate) fn narrow_object_by_path_assignability(
    &self,
    obj_ty: TypeId,
    path: &[PathSegment],
    required_prop_ty: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    if required_prop_ty == prim.never {
      return prim.never;
    }
    match self.store.type_kind(obj_ty) {
      TypeKind::Union(members) => {
        let mut narrowed = Vec::new();
        for member in members {
          let filtered = self.narrow_object_by_path_assignability(member, path, required_prop_ty);
          if filtered != prim.never {
            narrowed.push(filtered);
          }
        }
        self.store.union(narrowed)
      }
      _ => {
        if let Some(prop_ty) = self.object_prop_type_path(obj_ty, path) {
          let (overlap, _) =
            narrow_by_assignability(prop_ty, required_prop_ty, &self.store, &self.relate);
          if overlap != prim.never {
            return obj_ty;
          }
          return prim.never;
        }
        obj_ty
      }
    }
  }

  pub(crate) fn member_chain_target(
    &self,
    expr_id: ExprId,
  ) -> Option<(FlowBindingId, Vec<(PathSegment, bool)>, ExprId)> {
    let ExprKind::Member(MemberExpr {
      object,
      property,
      optional,
    }) = &self.body.exprs[expr_id.0 as usize].kind
    else {
      return None;
    };
    let segment = self.member_path_segment(property)?;
    if let Some(binding) = self.ident_binding(*object) {
      return Some((binding, vec![(segment, *optional)], *object));
    }
    if matches!(
      &self.body.exprs[object.0 as usize].kind,
      ExprKind::Member(_)
    ) {
      let (binding, mut segments, root_expr) = self.member_chain_target(*object)?;
      segments.push((segment, *optional));
      return Some((binding, segments, root_expr));
    }
    None
  }

  pub(crate) fn discriminant_member(
    &self,
    expr_id: ExprId,
  ) -> Option<(
    FlowBindingId,
    Vec<PathSegment>,
    ExprId,
    Vec<Vec<PathSegment>>,
  )> {
    let (binding, segments, root_expr) = self.member_chain_target(expr_id)?;
    let mut path = Vec::with_capacity(segments.len());
    let mut optional_bases = Vec::new();
    let mut prefix: Vec<PathSegment> = Vec::new();
    for (idx, (segment, optional)) in segments.iter().enumerate() {
      if *optional && idx > 0 {
        optional_bases.push(prefix.clone());
      }
      path.push(segment.clone());
      prefix.push(segment.clone());
    }
    Some((binding, path, root_expr, optional_bases))
  }

  pub(crate) fn typeof_comparison(
    &self,
    left: ExprId,
    right: ExprId,
  ) -> Option<(FlowBindingId, TypeId, String)> {
    // A no-substitution template literal (`` `string` ``) is a string literal
    // tag for typeof comparisons (tsc `controlFlowWithTemplateLiterals`).
    fn string_tag(kind: &ExprKind) -> Option<String> {
      match kind {
        ExprKind::Literal(hir_js::Literal::String(s)) => Some(s.lossy.clone()),
        ExprKind::Template(t) if t.spans.is_empty() => Some(t.head.clone()),
        _ => None,
      }
    }
    let left_expr = &self.body.exprs[left.0 as usize].kind;
    let right_expr = &self.body.exprs[right.0 as usize].kind;
    match (left_expr, right_expr) {
      (
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        },
        tag_expr,
      ) => {
        if let (Some(binding), Some(tag)) = (self.ident_binding(*expr), string_tag(tag_expr)) {
          return Some((binding, self.expr_types[expr.0 as usize], tag));
        }
      }
      (
        tag_expr,
        ExprKind::Unary {
          op: UnaryOp::Typeof,
          expr,
        },
      ) => {
        if let (Some(binding), Some(tag)) = (self.ident_binding(*expr), string_tag(tag_expr)) {
          return Some((binding, self.expr_types[expr.0 as usize], tag));
        }
      }
      _ => {}
    }
    None
  }
  pub(crate) fn assignment_expr_info(
    &mut self,
    expr_id: ExprId,
    env: &mut Env,
  ) -> (TypeId, Option<FlowBindingId>, bool) {
    let prim = self.store.primitive_ids();
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => {
        let binding = self.ident_binding(expr_id);
        let ty = binding
          .and_then(|id| env.get(id).or_else(|| self.initial.get(&id).copied()))
          .unwrap_or(prim.unknown);
        (ty, binding, false)
      }
      ExprKind::Member(mem) => {
        let obj_ty = self.eval_expr(mem.object, env).0;
        if let ObjectKey::Computed(prop) = &mem.property {
          let _ = self.eval_expr(*prop, env);
        }
        let prop_ty = self.member_type(obj_ty, mem);
        let root = self.assignment_target_root_expr(mem.object);
        (
          prop_ty,
          root,
          matches!(mem.property, ObjectKey::Computed(_)),
        )
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. } => self.assignment_expr_info(*expr, env),
      _ => (prim.unknown, None, false),
    }
  }

  pub(crate) fn assignment_target_info(
    &mut self,
    pat_id: PatId,
    env: &mut Env,
  ) -> (TypeId, Option<FlowBindingId>, bool) {
    let pat = &self.body.pats[pat_id.0 as usize];
    let prim = self.store.primitive_ids();
    match &pat.kind {
      PatKind::Ident(_) => {
        let binding = self.bindings.binding_for_pat(pat_id);
        let ty = binding
          .and_then(|id| env.get(id).or_else(|| self.initial.get(&id).copied()))
          .unwrap_or(prim.unknown);
        (ty, binding, false)
      }
      PatKind::Assign { target, .. } => self.assignment_target_info(*target, env),
      PatKind::Rest(inner) => self.assignment_target_info(**inner, env),
      PatKind::AssignTarget(expr) => self.assignment_expr_info(*expr, env),
      _ => (prim.unknown, None, false),
    }
  }

  pub(crate) fn reference_from_expr(&self, expr_id: ExprId, expr_ty: TypeId) -> Option<Reference> {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => self.ident_binding(expr_id).map(|id| Reference::Ident {
        name: id,
        ty: expr_ty,
      }),
      ExprKind::Member(mem) => {
        let base = self.ident_binding(mem.object)?;
        let prop = match &mem.property {
          ObjectKey::Ident(id) => self.hir_name(*id),
          ObjectKey::String(s) => s.clone(),
          ObjectKey::Number(n) => n.clone(),
          ObjectKey::Computed(_) => return None,
        };
        let base_ty = self.expr_types[mem.object.0 as usize];
        Some(Reference::Member {
          base,
          prop,
          base_ty,
          prop_ty: expr_ty,
        })
      }
      _ => None,
    }
  }

  pub(crate) fn narrow_reference_against(
    &self,
    reference: &Reference,
    other_value_ty: TypeId,
  ) -> TypeId {
    match reference {
      Reference::Ident { ty, .. } => {
        let (yes, _) = narrow_by_assignability(*ty, other_value_ty, &self.store, &self.relate);
        yes
      }
      Reference::Member { base_ty, prop, .. } => {
        self.narrow_object_by_prop_assignability(*base_ty, prop, other_value_ty)
      }
    }
  }

  pub(crate) fn narrow_object_by_prop_assignability(
    &self,
    obj_ty: TypeId,
    prop: &str,
    required_prop_ty: TypeId,
  ) -> TypeId {
    let prim = self.store.primitive_ids();
    if required_prop_ty == prim.never {
      return prim.never;
    }
    match self.store.type_kind(obj_ty) {
      TypeKind::Union(members) => {
        let mut narrowed = Vec::new();
        for member in members {
          let filtered = self.narrow_object_by_prop_assignability(member, prop, required_prop_ty);
          if filtered != prim.never {
            narrowed.push(filtered);
          }
        }
        self.store.union(narrowed)
      }
      _ => {
        if let Some(prop_ty) = self.object_prop_type(obj_ty, prop) {
          let (overlap, _) =
            narrow_by_assignability(prop_ty, required_prop_ty, &self.store, &self.relate);
          if overlap != prim.never {
            return obj_ty;
          }
          return prim.never;
        }
        obj_ty
      }
    }
  }

  pub(crate) fn numeric_assign_result(&self, left: TypeId, right: TypeId) -> TypeId {
    let left_base = self.base_type(left);
    let right_base = self.base_type(right);
    if self.is_bigint_like(left_base) && self.is_bigint_like(right_base) {
      self.store.primitive_ids().bigint
    } else {
      self.store.primitive_ids().number
    }
  }

  pub(crate) fn add_assign_result(&self, left: TypeId, right: TypeId) -> TypeId {
    let left_base = self.base_type(left);
    let right_base = self.base_type(right);
    let prim = self.store.primitive_ids();
    if self.is_bigint_like(left_base) && self.is_bigint_like(right_base) {
      return prim.bigint;
    }
    if self.maybe_string(left_base) || self.maybe_string(right_base) {
      self.store.union(vec![prim.string, prim.number])
    } else {
      prim.number
    }
  }

  pub(crate) fn logical_and_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<FlowBindingId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (left_truthy, left_falsy) = truthy_falsy_types(left_base, &self.store);
    let mut right_env = env.clone();
    if let Some(binding) = root {
      right_env.set(binding, left_truthy);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self.store.union(vec![left_falsy, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  pub(crate) fn logical_or_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<FlowBindingId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (left_truthy, left_falsy) = truthy_falsy_types(left_base, &self.store);
    let mut right_env = env.clone();
    if let Some(binding) = root {
      right_env.set(binding, left_falsy);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self
      .store
      .union(vec![left_truthy, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  pub(crate) fn nullish_assign(
    &mut self,
    target: PatId,
    left: TypeId,
    value: ExprId,
    root: Option<FlowBindingId>,
    env: &mut Env,
    facts: &mut Facts,
  ) -> TypeId {
    let left_base = self.base_type(left);
    let (nonnullish, nullish) = self.split_nullish(left_base);
    let mut right_env = env.clone();
    if let Some(binding) = root {
      right_env.set(binding, nullish);
    }
    let right_ty = self.eval_expr(value, &mut right_env).0;
    let result_ty = self.store.union(vec![nonnullish, self.base_type(right_ty)]);
    self.assign_pat(target, result_ty, env);
    self.record_assignment_facts(root, result_ty, facts);
    result_ty
  }

  pub(crate) fn assign_pat(&mut self, pat_id: PatId, value_ty: TypeId, env: &mut Env) {
    self.bind_pat_with_mode(pat_id, value_ty, env, BindingMode::Assign);
    self.mark_pat_state(pat_id, env, InitState::Assigned);
  }

  /// Bind `var`/`let`/`const` declarators, recording TS2454 DA exemptions from
  /// type annotations (tsc: `any`/`unknown`/`void` or includes `undefined`).
  pub(crate) fn bind_var_declarators(&mut self, decl: &hir_js::VarDecl, env: &mut Env) {
    let mode = match decl.kind {
      hir_js::VarDeclKind::Const | hir_js::VarDeclKind::Using | hir_js::VarDeclKind::AwaitUsing => {
        BindingMode::Declare
      }
      _ => BindingMode::Assign,
    };
    let prim = self.store.primitive_ids();
    for declarator in decl.declarators.iter() {
      self.note_da_exempt_annotation(declarator.pat, declarator.type_annotation);
      let mut init_ty = declarator
        .init
        .map(|id| self.eval_expr(id, env).0)
        .unwrap_or(prim.unknown);
      // tsc: a bare `[]` initializer binds as `any[]` when `--noImplicitAny`
      // is on (control-flow `autoArrayType`; ours does not evolve per-push,
      // staying `any[]`) or when `--strictNullChecks` is off
      // (`undefinedWideningType` widens to `any` for variable declarations).
      // Otherwise (strictNullChecks on, noImplicitAny off) the binding keeps
      // the synthesized `never[]` and `push` errors TS2345 (tsc).
      let empty_array_init = declarator.init.is_some_and(|id| {
        matches!(
          &self.body.exprs[id.0 as usize].kind,
          ExprKind::Array(arr) if arr.elements.is_empty()
        )
      });
      if (self.no_implicit_any || !self.store.options().strict_null_checks)
        && declarator.type_annotation.is_none()
        && empty_array_init
      {
        init_ty = self.store.intern_type(TypeKind::Array {
          ty: prim.any,
          readonly: false,
        });
      }
      // Ambient (`declare`) or annotation-only declarators have no initializer
      // to bind from: bind the caller-seeded declared type instead of
      // `unknown` (tsc erases ambient declarations; the annotation IS the
      // declared type). Binding still runs so DA/`var` hoisting semantics and
      // const-ness modes stay intact.
      let init_ty =
        if declarator.init.is_none() && (decl.declare || declarator.type_annotation.is_some()) {
          self
            .bindings
            .binding_key_for_pat(declarator.pat)
            .and_then(|key| self.bindings.flow_binding_for_key(key))
            .and_then(|id| self.initial.get(&id).copied())
            .unwrap_or(init_ty)
        } else {
          init_ty
        };
      self.bind_pat_with_mode(declarator.pat, init_ty, env, mode);
      // Ambient `declare let/var` (and `.d.ts` vars) are assumed initialized —
      // tsc never emits TS2454 for them (`literalTypesAndDestructuring`,
      // `logicalAssignment9`). `declare const` is already Assigned via Const.
      let state = if decl.declare
        || declarator.init.is_some()
        || declarator.definite_assignment
        || matches!(decl.kind, hir_js::VarDeclKind::Const)
      {
        InitState::Assigned
      } else {
        InitState::Unassigned
      };
      self.mark_pat_state(declarator.pat, env, state);
    }
  }

  /// tsc only emits TS2454 under `strictNullChecks`, and suppresses it when the
  /// declared type is `any`/`unknown`/`void` or includes `undefined`.
  pub(crate) fn should_report_use_before_assignment(&self, binding: BindingKey, env: &Env) -> bool {
    if !self.store.options().strict_null_checks {
      return false;
    }
    // tsc: identifiers under UnreachableFlow get the declared type (no
    // synthetic `| undefined`), so TS2454 is not reported on dead branches of
    // bare `true`/`false` conditions.
    if env.suppress_da() {
      return false;
    }
    if env.init_state(binding) == InitState::Assigned {
      return false;
    }
    if self.da_exempt_bindings.contains(&binding) {
      return false;
    }
    true
  }

  /// Bare `true` / `false` keywords (not parenthesized) — matches tsc binder
  /// `createFlowCondition` unreachable opposite branch.
  pub(crate) fn bare_boolean_literal(&self, expr_id: ExprId) -> Option<bool> {
    let expr = &self.body.exprs[expr_id.0 as usize];
    if expr.parenthesized {
      return None;
    }
    match &expr.kind {
      ExprKind::Literal(hir_js::Literal::Boolean(b)) => Some(*b),
      _ => None,
    }
  }

  pub(crate) fn note_da_exempt_annotation(
    &mut self,
    pat_id: PatId,
    type_annotation: Option<hir_js::TypeExprId>,
  ) {
    let Some(ann) = type_annotation else {
      return;
    };
    if !self.type_expr_is_da_exempt(ann) {
      return;
    }
    self.mark_pat_da_exempt(pat_id);
  }

  fn mark_pat_da_exempt(&mut self, pat_id: PatId) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(_) => {
        if let Some(binding) = self.bindings.binding_key_for_pat(pat_id) {
          self.da_exempt_bindings.insert(binding);
        }
      }
      PatKind::Assign { target, .. } => self.mark_pat_da_exempt(*target),
      PatKind::Rest(inner) => self.mark_pat_da_exempt(**inner),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.mark_pat_da_exempt(elem.pat);
        }
        if let Some(rest) = arr.rest {
          self.mark_pat_da_exempt(rest);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.mark_pat_da_exempt(prop.value);
        }
        if let Some(rest) = obj.rest {
          self.mark_pat_da_exempt(rest);
        }
      }
      // Assignment targets (`for (x of …)`) resolve to an existing binding;
      // exemption is recorded on that binding's declaration, not here.
      PatKind::AssignTarget(_) => {}
    }
  }

  /// Structural walk of a HIR type annotation for tsc-shaped DA exemption.
  ///
  /// Mirrors `assumeInitialized` (`AnyOrUnknown|Void`) and
  /// `containsUndefinedType` on the declared type. Expands `type` aliases
  /// (including generics with type-arg / default substitution, and imported
  /// aliases registered in [`Self::type_aliases`]) cycle-safely.
  fn type_expr_is_da_exempt(&self, id: hir_js::TypeExprId) -> bool {
    let Some(arenas) = self.type_arenas else {
      return false;
    };
    let mut visited = HashSet::new();
    let subst = HashMap::new();
    self.type_expr_is_da_exempt_in(arenas, id, self.file, self.names, &subst, &mut visited)
  }

  fn type_expr_is_da_exempt_in(
    &self,
    arenas: &hir_js::TypeArenas,
    id: hir_js::TypeExprId,
    file: FileId,
    names: &hir_js::NameInterner,
    subst: &HashMap<hir_js::NameId, DaSubstTarget<'_>>,
    visited: &mut HashSet<(u32, String)>,
  ) -> bool {
    let Some(expr) = arenas.type_exprs.get(id.0 as usize) else {
      return false;
    };
    self.type_expr_kind_is_da_exempt_in(arenas, &expr.kind, file, names, subst, visited)
  }

  fn type_expr_kind_is_da_exempt_in(
    &self,
    arenas: &hir_js::TypeArenas,
    kind: &hir_js::TypeExprKind,
    file: FileId,
    names: &hir_js::NameInterner,
    subst: &HashMap<hir_js::NameId, DaSubstTarget<'_>>,
    visited: &mut HashSet<(u32, String)>,
  ) -> bool {
    use hir_js::{TypeExprKind, TypeName};
    match kind {
      TypeExprKind::Any | TypeExprKind::Unknown | TypeExprKind::Void | TypeExprKind::Undefined => {
        true
      }
      TypeExprKind::Parenthesized(inner) => {
        self.type_expr_is_da_exempt_in(arenas, *inner, file, names, subst, visited)
      }
      TypeExprKind::Union(members) => members
        .iter()
        .any(|m| self.type_expr_is_da_exempt_in(arenas, *m, file, names, subst, visited)),
      TypeExprKind::TypeRef(r) => {
        let TypeName::Ident(name) = &r.name else {
          return false;
        };
        // Generic type-parameter substitution (annotation args / defaults).
        if let Some(target) = subst.get(name) {
          return self.type_expr_is_da_exempt_in(
            target.arenas,
            target.expr,
            target.file,
            target.names,
            &HashMap::new(),
            visited,
          );
        }
        // Re-export / ambient nullary fallback (resolved type_id, no body).
        if r.type_args.is_empty() {
          if let Some(aliases) = self.type_aliases {
            if let Some(&exempt) = aliases.nullary_exempt.get(name) {
              return exempt;
            }
          }
        }
        let Some(name_str) = names.resolve(*name) else {
          return false;
        };
        let visit_key = (file.0, name_str.to_string());
        if !visited.insert(visit_key.clone()) {
          return false;
        }
        let Some(aliases) = self.type_aliases else {
          visited.remove(&visit_key);
          return false;
        };
        // Prefer annotation-site local / import NameId, then defining-file
        // qualified lookup (nested refs inside a foreign alias body).
        let alias = aliases
          .by_name
          .get(name)
          .copied()
          .or_else(|| aliases.by_qualified.get(&visit_key).copied());
        let Some(alias) = alias else {
          visited.remove(&visit_key);
          return false;
        };
        let mut inner_subst = HashMap::new();
        for (i, param_id) in alias.type_params.iter().enumerate() {
          let Some(param) = alias.arenas.type_params.get(param_id.0 as usize) else {
            continue;
          };
          let target = if let Some(arg) = r.type_args.get(i) {
            // Chase through outer params so `type V<T> = Id<T>` + `V<any>`
            // substitutes `any` into `Id`, not a bare `T` ref.
            Self::chase_da_subst(arenas, *arg, file, names, subst)
          } else if let Some(default) = param.default {
            Self::chase_da_subst(alias.arenas, default, alias.file, alias.names, subst)
          } else {
            continue;
          };
          inner_subst.insert(param.name, target);
        }
        let exempt = self.type_expr_is_da_exempt_in(
          alias.arenas,
          alias.type_expr,
          alias.file,
          alias.names,
          &inner_subst,
          visited,
        );
        visited.remove(&visit_key);
        exempt
      }
      _ => false,
    }
  }

  /// Resolve a type-arg through the active DA subst map when it is a naked
  /// type-parameter reference (no type arguments).
  fn chase_da_subst<'s>(
    arenas: &'s hir_js::TypeArenas,
    id: hir_js::TypeExprId,
    file: FileId,
    names: &'s hir_js::NameInterner,
    subst: &HashMap<hir_js::NameId, DaSubstTarget<'s>>,
  ) -> DaSubstTarget<'s> {
    use hir_js::{TypeExprKind, TypeName};
    let mut arenas = arenas;
    let mut id = id;
    let mut file = file;
    let mut names = names;
    let mut seen = HashSet::new();
    loop {
      if !seen.insert((file.0, id.0)) {
        break;
      }
      let Some(expr) = arenas.type_exprs.get(id.0 as usize) else {
        break;
      };
      let TypeExprKind::TypeRef(r) = &expr.kind else {
        break;
      };
      if !r.type_args.is_empty() {
        break;
      }
      let TypeName::Ident(name) = &r.name else {
        break;
      };
      let Some(next) = subst.get(name).copied() else {
        break;
      };
      arenas = next.arenas;
      id = next.expr;
      file = next.file;
      names = next.names;
    }
    DaSubstTarget {
      arenas,
      expr: id,
      file,
      names,
    }
  }

  pub(crate) fn bind_pat(&mut self, pat_id: PatId, value_ty: TypeId, env: &mut Env) {
    self.bind_pat_with_mode(pat_id, value_ty, env, BindingMode::Declare);
  }

  pub(crate) fn bind_pat_with_mode(
    &mut self,
    pat_id: PatId,
    value_ty: TypeId,
    env: &mut Env,
    mode: BindingMode,
  ) {
    let pat = &self.body.pats[pat_id.0 as usize];
    let prim = self.store.primitive_ids();
    let write_ty = self.apply_binding_mode(value_ty, mode);
    let slot = &mut self.pat_types[pat_id.0 as usize];
    *slot = if *slot == prim.unknown {
      write_ty
    } else {
      self.store.union(vec![*slot, write_ty])
    };
    match &pat.kind {
      PatKind::Ident(_) => {
        if let Some(id) = self.bindings.binding_for_pat(pat_id) {
          if matches!(mode, BindingMode::Assign) {
            env.invalidate(id);
          }
          env.set(id, write_ty);
        }
        // Mark assigned at the binding leaf so later sibling defaults in the
        // same pattern (tsc left-to-right destructuring order) see prior names
        // as initialized: `const { a, b = a } = …`, `const [a, b = a] = …`,
        // `let [{ ...a }, b = a] = …`. `bind_var_declarators` may still overwrite
        // with Unassigned when the declarator has no initializer.
        self.mark_pat_state(pat_id, env, InitState::Assigned);
      }
      PatKind::Assign {
        target,
        default_value,
      } => {
        // Default runs before the target is initialized (self-ref stays an error).
        let default_eval = self.eval_expr(*default_value, env).0;
        let default_ty = self.apply_binding_mode(default_eval, mode);
        let combined = self.store.union(vec![write_ty, default_ty]);
        self.bind_pat_with_mode(*target, combined, env, mode);
      }
      PatKind::Rest(inner) => self.bind_pat_with_mode(**inner, write_ty, env, mode),
      PatKind::Array(arr) => {
        let element_ty = match self.store.type_kind(value_ty) {
          TypeKind::Array { ty, .. } => ty,
          TypeKind::Tuple(elems) => elems.first().map(|e| e.ty).unwrap_or(prim.unknown),
          _ => prim.unknown,
        };
        for (idx, elem) in arr.elements.iter().enumerate() {
          if let Some(elem) = elem {
            let mut ty = element_ty;
            if let TypeKind::Tuple(elems) = self.store.type_kind(value_ty) {
              if let Some(specific) = elems.get(idx) {
                ty = specific.ty;
              }
            }
            ty = self.apply_binding_mode(ty, mode);
            if let Some(default) = elem.default_value {
              let default_eval = self.eval_expr(default, env).0;
              let default_ty = self.apply_binding_mode(default_eval, mode);
              ty = self.store.union(vec![ty, default_ty]);
            }
            self.bind_pat_with_mode(elem.pat, ty, env, mode);
          }
        }
        if let Some(rest) = arr.rest {
          let rest_ty = self.apply_binding_mode(value_ty, mode);
          self.bind_pat_with_mode(rest, rest_ty, env, mode);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          let prop_name = match &prop.key {
            ObjectKey::Ident(id) => Some(self.hir_name(*id)),
            ObjectKey::String(s) => Some(s.clone()),
            ObjectKey::Number(n) => Some(n.clone()),
            _ => None,
          };
          let mut prop_ty = prim.unknown;
          if let Some(name) = prop_name {
            if let Some(found) = self.object_prop_type(value_ty, &name) {
              prop_ty = found;
            }
          }
          prop_ty = self.apply_binding_mode(prop_ty, mode);
          if let Some(default) = prop.default_value {
            let default_eval = self.eval_expr(default, env).0;
            let default_ty = self.apply_binding_mode(default_eval, mode);
            prop_ty = self.store.union(vec![prop_ty, default_ty]);
          }
          self.bind_pat_with_mode(prop.value, prop_ty, env, mode);
        }
        if let Some(rest) = obj.rest {
          let rest_ty = self.apply_binding_mode(value_ty, mode);
          self.bind_pat_with_mode(rest, rest_ty, env, mode);
        }
      }
      PatKind::AssignTarget(expr) => {
        self.write_assign_target_expr(*expr, write_ty, env, mode);
        self.mark_expr_state(*expr, env, InitState::Assigned);
      }
    }
  }

  pub(crate) fn mark_expr_state(&self, expr_id: ExprId, env: &mut Env, state: InitState) {
    if let Some(binding) = self.bindings.binding_key_for_expr(expr_id) {
      env.set_init_state(binding, state);
    }
  }

  pub(crate) fn mark_pat_state(&self, pat_id: PatId, env: &mut Env, state: InitState) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(_) => {
        if let Some(binding) = self.bindings.binding_key_for_pat(pat_id) {
          env.set_init_state(binding, state);
        }
      }
      PatKind::Assign { target, .. } => self.mark_pat_state(*target, env, state),
      PatKind::Rest(inner) => self.mark_pat_state(**inner, env, state),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.mark_pat_state(elem.pat, env, state);
        }
        if let Some(rest) = arr.rest {
          self.mark_pat_state(rest, env, state);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.mark_pat_state(prop.value, env, state);
        }
        if let Some(rest) = obj.rest {
          self.mark_pat_state(rest, env, state);
        }
      }
      PatKind::AssignTarget(expr) => self.mark_expr_state(*expr, env, state),
    }
  }

  pub(crate) fn write_assign_target_expr(
    &mut self,
    expr_id: ExprId,
    value_ty: TypeId,
    env: &mut Env,
    mode: BindingMode,
  ) {
    match &self.body.exprs[expr_id.0 as usize].kind {
      ExprKind::Ident(_) => {
        if let Some(id) = self.ident_binding(expr_id) {
          if matches!(mode, BindingMode::Assign) {
            env.invalidate(id);
          }
          env.set(id, value_ty);
        }
      }
      ExprKind::Member(mem) => {
        if let Some(root) = self.assignment_target_root_expr(mem.object) {
          let root_ty = env
            .get(root)
            .or_else(|| self.initial.get(&root).copied())
            .unwrap_or(self.store.primitive_ids().unknown);
          let widened = self.widen_object_prop(root_ty);
          env.invalidate(root);
          env.set(root, self.base_type(widened));
        } else if matches!(mem.property, ObjectKey::Computed(_)) {
          env.clear_all_properties();
        }
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. } => {
        self.write_assign_target_expr(*expr, value_ty, env, mode);
      }
      _ => {}
    }
  }

  pub(crate) fn object_type(&mut self, obj: &ObjectLiteral, env: &mut Env) -> TypeId {
    if obj.properties.is_empty() {
      // Keep the flow checker consistent with the AST checker: `{}` expression
      // literals infer the `{}` (empty object) type, not the `object` keyword.
      return self.store.intern_type(TypeKind::EmptyObject);
    }
    let mut shape = Shape::new();
    // `(key kind, value type)` contributions from computed keys; synthesized
    // into index signatures after the loop (tsc `getObjectLiteralIndexInfo`).
    let mut computed: Vec<(TypeId, TypeId)> = Vec::new();
    for prop in obj.properties.iter() {
      match prop {
        ObjectProperty::KeyValue { key, value, .. } => {
          enum Dest {
            Named(PropKey),
            Index(TypeId),
            Skip,
          }
          let dest = match key {
            ObjectKey::Ident(id) => {
              Dest::Named(PropKey::String(self.store.intern_name(self.hir_name(*id))))
            }
            ObjectKey::String(s) => Dest::Named(PropKey::String(self.store.intern_name(s.clone()))),
            ObjectKey::Number(n) => Dest::Named(match n.parse::<i64>() {
              Ok(parsed) => PropKey::Number(parsed),
              // Fractional numeric keys are string keys, never key `0`.
              Err(_) => PropKey::String(self.store.intern_name(n.clone())),
            }),
            ObjectKey::Computed(expr) => {
              let key_ty = self.eval_expr(*expr, env).0;
              match classify_computed_obj_key(&self.store, key_ty) {
                ComputedObjKey::Named(key) => Dest::Named(key),
                ComputedObjKey::Index(kind) => Dest::Index(kind),
                ComputedObjKey::Skip => Dest::Skip,
              }
            }
          };
          let ty = self.eval_expr(*value, env).0;
          let ty = if self.widen_object_literals {
            self.widen_object_prop(ty)
          } else {
            ty
          };
          match dest {
            Dest::Named(prop_key) => shape.properties.push(types_ts_interned::Property {
              key: prop_key,
              data: PropData {
                ty,
                optional: false,
                readonly: false,
                accessibility: None,
                is_method: false,
                origin: None,
                declared_on: None,
              },
            }),
            Dest::Index(kind) => computed.push((kind, ty)),
            Dest::Skip => {}
          }
        }
        ObjectProperty::Getter { key, .. } | ObjectProperty::Setter { key, .. } => {
          let prop_key = match key {
            ObjectKey::Ident(id) => {
              Some(PropKey::String(self.store.intern_name(self.hir_name(*id))))
            }
            ObjectKey::String(s) => Some(PropKey::String(self.store.intern_name(s.clone()))),
            ObjectKey::Number(n) => Some(match n.parse::<i64>() {
              Ok(parsed) => PropKey::Number(parsed),
              // Fractional numeric keys are string keys, never key `0`.
              Err(_) => PropKey::String(self.store.intern_name(n.clone())),
            }),
            ObjectKey::Computed(_) => None,
          };
          if let Some(prop_key) = prop_key {
            shape.properties.push(types_ts_interned::Property {
              key: prop_key,
              data: PropData {
                ty: self.store.primitive_ids().unknown,
                optional: false,
                readonly: false,
                accessibility: None,
                is_method: true,
                origin: None,
                declared_on: None,
              },
            });
          }
        }
        ObjectProperty::Spread(expr) => {
          let spread_ty = self.eval_expr(*expr, env).0;
          self.append_object_spread_properties(&mut shape, spread_ty);
        }
      }
    }
    synthesize_computed_indexers(&self.store, &mut shape, &computed);
    if shape.properties.is_empty() && shape.indexers.is_empty() {
      return self.store.intern_type(TypeKind::EmptyObject);
    }
    let shape_id = self.store.intern_shape(shape);
    let obj_id = self.store.intern_object(ObjectType { shape: shape_id });
    self.store.intern_type(TypeKind::Object(obj_id))
  }

  /// Merge enumerable own properties from an object-spread source into `shape`.
  pub(crate) fn append_object_spread_properties(&mut self, shape: &mut Shape, source: TypeId) {
    let source = self.expand_ref(source);
    match self.store.type_kind(source) {
      TypeKind::Object(obj_id) => {
        let src_shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in src_shape.properties.iter() {
          let is_private = match &prop.key {
            PropKey::String(n) | PropKey::Symbol(n) => self.store.name(*n).starts_with('#'),
            PropKey::Number(_) => false,
          };
          if is_private {
            continue;
          }
          let mut data = prop.data.clone();
          data.origin = None;
          data.accessibility = None;
          if let Some(existing) = shape.properties.iter_mut().find(|p| p.key == prop.key) {
            existing.data = data;
          } else {
            shape.properties.push(types_ts_interned::Property {
              key: prop.key.clone(),
              data,
            });
          }
        }
      }
      TypeKind::Intersection(members) => {
        for member in members {
          self.append_object_spread_properties(shape, member);
        }
      }
      TypeKind::Union(members) => {
        if members.is_empty() {
          return;
        }
        let mut merged: Vec<(PropKey, PropData, usize)> = Vec::new();
        let n = members.len();
        for member in members.iter().copied() {
          let mut part = Shape::new();
          self.append_object_spread_properties(&mut part, member);
          for prop in part.properties {
            if let Some((_, data, count)) = merged.iter_mut().find(|(k, _, _)| *k == prop.key) {
              *count += 1;
              data.ty = self.store.union(vec![data.ty, prop.data.ty]);
              data.optional = data.optional || prop.data.optional;
            } else {
              merged.push((prop.key, prop.data, 1));
            }
          }
        }
        for (key, mut data, count) in merged {
          if count < n {
            data.optional = true;
          }
          if let Some(existing) = shape.properties.iter_mut().find(|p| p.key == key) {
            existing.data = data;
          } else {
            shape
              .properties
              .push(types_ts_interned::Property { key, data });
          }
        }
      }
      _ => {}
    }
  }

  pub(crate) fn widen_object_prop(&self, ty: TypeId) -> TypeId {
    let prim = self.store.primitive_ids();
    match self.store.type_kind(ty) {
      TypeKind::NumberLiteral(_) => prim.number,
      TypeKind::StringLiteral(_) => prim.string,
      TypeKind::BooleanLiteral(_) => prim.boolean,
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

  pub(crate) fn member_type(&mut self, obj: TypeId, mem: &MemberExpr) -> TypeId {
    let prim = self.store.primitive_ids();

    let mut ty = match &mem.property {
      ObjectKey::Computed(expr) => {
        let key_ty = self.expr_types[expr.0 as usize];
        let literal_key = self
          .literal_value(*expr)
          .and_then(|lit| match lit {
            LiteralValue::String(s) | LiteralValue::Number(s) => Some(s),
            _ => None,
          })
          .or_else(|| match self.store.type_kind(key_ty) {
            TypeKind::StringLiteral(id) => Some(self.store.name(id)),
            TypeKind::NumberLiteral(num) => Some(num.0.to_string()),
            _ => None,
          });

        if let Some(key) = literal_key {
          self.maybe_report_tuple_index_oob(obj, &key, *expr);
          self.member_type_for_known_key(obj, &key)
        } else {
          self.member_type_for_index_key(obj, key_ty, /*writing*/ false)
        }
      }
      _ => {
        let Some(key) = self.member_property_name(&mem.property) else {
          return prim.unknown;
        };
        self.member_type_for_known_key(obj, &key)
      }
    };

    if matches!(
      mem.property,
      ObjectKey::Computed(_) | ObjectKey::String(_) | ObjectKey::Number(_)
    ) && self.relate.options.no_unchecked_indexed_access
    {
      ty = self.store.union(vec![ty, prim.undefined]);
    }

    ty
  }

  pub(crate) fn member_type_for_known_key(&self, obj: TypeId, key: &str) -> TypeId {
    let prim = self.store.primitive_ids();
    let obj = self.expand_ref(obj);
    match self.store.type_kind(obj) {
      TypeKind::Any => prim.any,
      TypeKind::Union(members) => {
        let mut collected = Vec::new();
        for member in members {
          collected.push(self.member_type_for_known_key(member, key));
        }
        self.store.union(collected)
      }
      TypeKind::Intersection(members) => {
        let mut collected = Vec::new();
        for member in members {
          collected.push(self.member_type_for_known_key(member, key));
        }
        self.store.intersection(collected)
      }
      TypeKind::Ref { .. } => prim.unknown,
      TypeKind::Tuple(elems) => match key.parse::<usize>() {
        Ok(idx) if !key.contains('.') && !key.starts_with('-') => {
          let options = self.relate.options;
          if let Some(elem) = elems.get(idx) {
            let mut ty = elem.ty;
            if elem.optional && !options.exact_optional_property_types {
              ty = self.store.union(vec![ty, prim.undefined]);
            }
            ty
          } else if let Some(rest) = elems.iter().rev().find(|e| e.rest) {
            rest.ty
          } else {
            prim.undefined
          }
        }
        Err(_) => {
          let Ok(parsed) = key.parse::<f64>() else {
            return prim.unknown;
          };
          if parsed.fract() != 0.0 || parsed < 0.0 {
            return prim.unknown;
          }
          let idx = parsed as usize;
          let options = self.relate.options;
          if let Some(elem) = elems.get(idx) {
            let mut ty = elem.ty;
            if elem.optional && !options.exact_optional_property_types {
              ty = self.store.union(vec![ty, prim.undefined]);
            }
            ty
          } else if let Some(rest) = elems.iter().rev().find(|e| e.rest) {
            rest.ty
          } else {
            prim.undefined
          }
        }
        _ => prim.unknown,
      },
      _ => self.object_prop_type(obj, key).unwrap_or(prim.unknown),
    }
  }

  /// TS2493 when a numeric literal indexes past a fixed-length tuple.
  pub(crate) fn maybe_report_tuple_index_oob(
    &mut self,
    obj_ty: TypeId,
    key: &str,
    index_expr: ExprId,
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
      range: self.body.exprs[index_expr.0 as usize].span,
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

  /// Indexed access `obj[key]` (see AST checker for write-distribution notes).
  pub(crate) fn member_type_for_index_key(
    &self,
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
        let named = self.member_type_for_known_key(obj, name);
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

    // Index signatures are keyed by JS property keys: string, number, and symbol.
    // For computed member access, model key matching in terms of those key kinds
    // rather than generic type assignability (which can be overly permissive for
    // intersection key types).
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
        // Fall back to probing key kinds via assignability for non-primitive key
        // types (e.g. type parameters).
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

    if candidates.is_empty() {
      return false;
    }

    candidates
      .into_iter()
      .any(|key| crate::type_queries::indexer_accepts_key(&key, indexer_key, &self.store))
  }

  /// Global interface that supplies members for a primitive (tsc apparent type:
  /// `string` → `String`, `number` → `Number`, …).
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

  /// Apparent `Array<T>` for intrinsic array types (named members like `push`).
  pub(crate) fn array_interface_type(&self, elem_ty: TypeId) -> Option<TypeId> {
    let resolver = self.type_resolver.as_ref()?;
    let def = resolver.resolve_type_name(&["Array".to_string()])?;
    let ref_ty = self.store.canon(self.store.intern_type(TypeKind::Ref {
      def,
      args: vec![elem_ty],
    }));
    let expanded = self.expand_ref(ref_ty);
    if matches!(
      self.store.type_kind(expanded),
      TypeKind::Array { .. } | TypeKind::Unknown | TypeKind::Any | TypeKind::Ref { .. }
    ) {
      return None;
    }
    Some(expanded)
  }

  pub(crate) fn object_prop_type(&self, obj: TypeId, key: &str) -> Option<TypeId> {
    let prim = self.store.primitive_ids();
    let obj = self.expand_ref(obj);
    match self.store.type_kind(obj) {
      TypeKind::Union(members) => {
        let mut tys = Vec::new();
        for member in members {
          if let Some(prop_ty) = self.object_prop_type(member, key) {
            tys.push(prop_ty);
          }
        }
        if tys.is_empty() {
          None
        } else {
          Some(self.store.union(tys))
        }
      }
      TypeKind::Intersection(members) => {
        let mut tys = Vec::new();
        for member in members {
          if let Some(prop_ty) = self.object_prop_type(member, key) {
            tys.push(prop_ty);
          }
        }
        if tys.is_empty() {
          None
        } else {
          Some(self.store.intersection(tys))
        }
      }
      TypeKind::Ref { .. } => None,
      TypeKind::Callable { .. } => self.callable_prop_type(obj, key),
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        for prop in shape.properties.iter() {
          let matches = match prop.key {
            PropKey::String(name) => self.store.name(name) == key,
            PropKey::Number(num) => num.to_string() == key,
            _ => false,
          };
          if matches {
            return Some(prop.data.ty);
          }
        }
        if key == "call" && !shape.call_signatures.is_empty() {
          return Some(self.build_call_method_type(shape.call_signatures.clone()));
        }
        let key_prop = if let Some(idx) = parse_canonical_index_str(key) {
          PropKey::Number(idx)
        } else {
          PropKey::String(self.store.intern_name(key))
        };
        let mut matches = Vec::new();
        for idxer in shape.indexers.iter() {
          if crate::type_queries::indexer_accepts_key(&key_prop, idxer.key_type, &self.store) {
            matches.push(idxer.value_type);
          }
        }
        if matches.is_empty() {
          Some(prim.unknown)
        } else if matches.len() == 1 {
          Some(matches[0])
        } else {
          matches.sort_by(|a, b| self.store.type_cmp(*a, *b));
          matches.dedup();
          Some(self.store.union(matches))
        }
      }
      TypeKind::Array { .. } if key == "length" => Some(prim.number),
      TypeKind::Array { ty: elem_ty, .. } => {
        if let Some(iface) = self.array_interface_type(elem_ty) {
          if let Some(looked) = self.object_prop_type(iface, key) {
            return Some(looked);
          }
        }
        // Numeric index names still yield the element type when the lib
        // interface is absent / incomplete.
        if parse_canonical_index_str(key).is_some() {
          Some(elem_ty)
        } else {
          None
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
        let iface = self.primitive_interface_type(obj)?;
        self.object_prop_type(iface, key)
      }
      _ => None,
    }
  }

  pub(crate) fn callable_prop_type(&self, obj: TypeId, key: &str) -> Option<TypeId> {
    // Mirror `member_type` for bare callables: `call` from signatures,
    // `prototype` as `any` (lib `Function.prototype`).
    if key == "prototype" {
      return Some(self.store.primitive_ids().any);
    }
    if key != "call" {
      return None;
    }
    let sigs = callable_signatures(&self.store, obj);
    if sigs.is_empty() {
      return None;
    }
    Some(self.build_call_method_type(sigs))
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

  pub(crate) fn switch_case_falls_through(&self, case: Option<&SwitchCase>) -> bool {
    let Some(case) = case else {
      return false;
    };
    match case.consequent.last() {
      None => true,
      Some(stmt) => match &self.body.stmts[stmt.0 as usize].kind {
        StmtKind::Return(_) | StmtKind::Throw(_) | StmtKind::Break(_) => false,
        _ => true,
      },
    }
  }

  pub(crate) fn apply_switch_narrowing(
    &mut self,
    target: &SwitchDiscriminant,
    test: ExprId,
    env: &mut Env,
  ) -> Option<(TypeId, TypeId)> {
    let (yes, no) = self.switch_case_narrowing_with_type(target, target.ty(), test)?;
    self.apply_switch_result(target, yes, env);
    Some((yes, no))
  }

  pub(crate) fn switch_default_remaining(
    &self,
    target: &SwitchDiscriminant,
    cases: &[SwitchCase],
  ) -> Option<TypeId> {
    let mut remaining = target.ty();
    for case in cases.iter() {
      if let Some(test) = case.test {
        let (_, no) = self.switch_case_narrowing_with_type(target, remaining, test)?;
        remaining = no;
      }
    }
    Some(remaining)
  }

  pub(crate) fn switch_case_narrowing_with_type(
    &self,
    target: &SwitchDiscriminant,
    ty: TypeId,
    test: ExprId,
  ) -> Option<(TypeId, TypeId)> {
    match target {
      SwitchDiscriminant::Ident { .. } => {
        let lit = self.literal_value(test)?;
        Some(narrow_by_literal(ty, &lit, &self.store))
      }
      SwitchDiscriminant::Member {
        path,
        optional_bases,
        ..
      } => {
        let lit = self.literal_value(test)?;
        let (yes, no) = narrow_by_discriminant_path(ty, path, &lit, &self.store, self.ref_expander);
        if optional_bases.is_empty() {
          Some((yes, no))
        } else {
          Some((yes, ty))
        }
      }
      SwitchDiscriminant::Typeof { .. } => match self.literal_value(test) {
        Some(LiteralValue::String(value)) => {
          Some(narrow_by_typeof(ty, &value, &self.store, self.ref_expander))
        }
        _ => None,
      },
    }
  }

  pub(crate) fn switch_discriminant_target(
    &self,
    discriminant: ExprId,
    discriminant_ty: TypeId,
    env: &Env,
  ) -> Option<SwitchDiscriminant> {
    match &self.body.exprs[discriminant.0 as usize].kind {
      ExprKind::Unary {
        op: UnaryOp::Typeof,
        expr,
      } => {
        if let Some(binding) = self.ident_binding(*expr) {
          let operand_ty = env
            .get(binding)
            .unwrap_or_else(|| self.expr_types[expr.0 as usize]);
          return Some(SwitchDiscriminant::Typeof {
            name: binding,
            ty: operand_ty,
          });
        }
        None
      }
      ExprKind::Member(_) => self.switch_member_target(discriminant, env),
      ExprKind::Ident(_) => {
        self
          .ident_binding(discriminant)
          .map(|binding| SwitchDiscriminant::Ident {
            name: binding,
            ty: env.get(binding).unwrap_or(discriminant_ty),
          })
      }
      _ => None,
    }
  }

  pub(crate) fn switch_member_target(&self, expr: ExprId, env: &Env) -> Option<SwitchDiscriminant> {
    let (binding, path, root_expr, optional_bases) = self.discriminant_member(expr)?;
    let obj_ty = env
      .get(binding)
      .unwrap_or_else(|| self.expr_types[root_expr.0 as usize]);
    Some(SwitchDiscriminant::Member {
      name: binding,
      path,
      optional_bases,
      ty: obj_ty,
    })
  }

  pub(crate) fn apply_switch_result(
    &mut self,
    target: &SwitchDiscriminant,
    narrowed: TypeId,
    env: &mut Env,
  ) {
    env.set(target.name(), narrowed);
    let prim = self.store.primitive_ids();
    if let SwitchDiscriminant::Member {
      name,
      optional_bases,
      ..
    } = target
    {
      for base_path in optional_bases.iter() {
        if base_path.is_empty() {
          continue;
        }
        let Some(base_ty) = self.object_prop_type_path(narrowed, base_path) else {
          continue;
        };
        let (non_nullish, _) = narrow_non_nullish(base_ty, &self.store);
        if non_nullish == prim.never {
          continue;
        }
        let mut key = FlowKey::root(*name);
        for seg in base_path.iter() {
          key = key.with_segment(seg.clone());
        }
        env.set_path(key, non_nullish);
      }
    }
  }
}
