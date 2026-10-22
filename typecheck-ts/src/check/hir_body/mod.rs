//! HIR body checking: entrypoints, checker state, and AST indexing.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};
use std::panic::panic_any;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use bumpalo::Bump;
use diagnostics::{Diagnostic, FileId, Span, TextRange};
use hir_js::{
  Body, BodyKind, ExprId, ForHead, ForInit, NameId, NameInterner, PatId, StmtKind, TypeArenasByDef,
  TypeExprId, VarDecl as HirVarDecl,
};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::Expr as AstExpr;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::loc::Loc;
use types_ts_interned::{
  EvaluatorCaches, ExpandedType, NameId as TsNameId, ObjectType, PropKey, RelateCtx, SignatureId,
  TypeDisplay, TypeEvaluator, TypeExpander, TypeId, TypeKind, TypeParamDecl, TypeParamId,
  TypeParamVariance, TypeStore,
};

use super::caches::BodyCaches;
use super::flow_bindings::FlowBindings;
use super::instantiate::{InstantiationCache, Substituter};
use super::type_expr::{TypeLowerer, TypeResolver};
use crate::lib_support::{JsxMode, ScriptTarget};
pub use crate::BodyCheckResult;
use crate::{codes, BodyId, DefId};

#[path = "../ast_index.rs"]
mod ast_index;
pub use ast_index::AstIndex;
pub(crate) use ast_index::{ClassStaticBlockInfo, FunctionInfo, VarInfo};

#[path = "../body/mod.rs"]
mod body;
use body::FlowBodyChecker;
pub use body::{type_id_is_da_exempt, DaAliasBody, DaTypeAliasMap};

#[derive(Default, Clone)]
pub(crate) struct Scope {
  bindings: HashMap<String, Binding>,
}

#[derive(Clone)]
pub(crate) struct Binding {
  /// Current flow type (may narrow after a successful assignment).
  ty: TypeId,
  /// Declared/annotation type used for write checks. Assignments must remain
  /// compatible with this type even after CFA narrows [`Self::ty`].
  declared_ty: TypeId,
  /// Type parameters in scope for the binding (carried for generic value forms).
  #[allow(dead_code)]
  type_params: Vec<TypeParamDecl>,
}

/// Simple resolver that maps single-segment type names to known definitions.
#[derive(Clone)]
pub struct BindingTypeResolver {
  map: HashMap<String, DefId>,
}

impl BindingTypeResolver {
  pub fn new(map: HashMap<String, DefId>) -> Self {
    Self { map }
  }
}

impl TypeResolver for BindingTypeResolver {
  fn resolve_type_name(&self, path: &[String]) -> Option<DefId> {
    match path {
      [name] => self.map.get(name).copied(),
      _ => None,
    }
  }
}

/// Type-check a lowered HIR body, producing per-expression and per-pattern type tables.
pub fn check_body(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  ast_index: &AstIndex<'_>,
  store: Arc<TypeStore>,
  target: ScriptTarget,
  use_define_for_class_fields: bool,
  caches: &BodyCaches,
  bindings: &HashMap<String, TypeId>,
  resolver: Option<Arc<dyn TypeResolver>>,
) -> BodyCheckResult {
  check_body_with_expander(
    body_id,
    body,
    names,
    file,
    ast_index,
    store,
    target,
    use_define_for_class_fields,
    false,
    false,
    caches,
    bindings,
    resolver,
    None,
    None,
    None,
    false,
    None,
    None,
    None,
    None,
    &HashMap::new(),
    &HashMap::new(),
  )
}

/// Collect constructor value types for class expressions in `body`.
///
/// Prefers `value_defs[class_def]` when provided; otherwise scans
/// `def_id_spans` for defs at the expression span whose interned type has
/// construct signatures (the synthetic value-side class def).
pub fn class_expr_value_types_for_body(
  body: &Body,
  interned_def_types: &HashMap<DefId, TypeId>,
  store: &TypeStore,
  value_defs: Option<&HashMap<DefId, DefId>>,
  def_id_spans: Option<&HashMap<DefId, TextRange>>,
) -> HashMap<TextRange, TypeId> {
  let mut out = HashMap::new();
  for expr in body.exprs.iter() {
    let hir_js::ExprKind::ClassExpr { def, .. } = &expr.kind else {
      continue;
    };
    let mut ty = None;
    if let Some(value_defs) = value_defs {
      if let Some(value_def) = value_defs.get(def).copied() {
        if let Some(candidate) = interned_def_types.get(&value_def).copied() {
          if type_has_construct_signature(store, candidate) {
            ty = Some(candidate);
          }
        }
      }
    }
    if ty.is_none() {
      if let Some(def_id_spans) = def_id_spans {
        // value_def and type_def share the class-expression span; pick the
        // interned def at that span that has construct signatures.
        for (other_def, other_span) in def_id_spans.iter() {
          if *other_span != expr.span {
            continue;
          }
          if let Some(candidate) = interned_def_types.get(other_def).copied() {
            if type_has_construct_signature(store, candidate) {
              ty = Some(candidate);
              break;
            }
          }
        }
      }
    }
    if let Some(ty) = ty {
      out.insert(expr.span, store.canon(ty));
    }
  }
  out
}

pub(crate) fn type_has_construct_signature(store: &TypeStore, ty: TypeId) -> bool {
  let ty = store.canon(ty);
  match store.type_kind(ty) {
    TypeKind::Object(obj_id) => !store
      .shape(store.object(obj_id).shape)
      .construct_signatures
      .is_empty(),
    TypeKind::Intersection(members) => members
      .iter()
      .any(|m| type_has_construct_signature(store, *m)),
    _ => false,
  }
}

/// Type-check a lowered HIR body with an optional reference type expander for
/// relation checks. The expander is used to lazily resolve `TypeKind::Ref`
/// nodes during assignability comparisons.
pub fn check_body_with_expander(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  ast_index: &AstIndex<'_>,
  store: Arc<TypeStore>,
  target: ScriptTarget,
  use_define_for_class_fields: bool,
  strict_null_checks: bool,
  strict_property_initialization: bool,
  caches: &BodyCaches,
  bindings: &HashMap<String, TypeId>,
  resolver: Option<Arc<dyn TypeResolver>>,
  relate_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
  type_param_decls: Option<&HashMap<DefId, Arc<[TypeParamDecl]>>>,
  contextual_fn_ty: Option<TypeId>,
  no_implicit_any: bool,
  jsx_mode: Option<JsxMode>,
  cancelled: Option<&Arc<AtomicBool>>,
  // Source text for JSDoc `@type` / `@param` / `@returns` / `@typedef`
  // scanning under checkJs (`.js`/`.jsx`). When `None`, JSDoc type tags are
  // ignored.
  jsdoc_source: Option<&str>,
  // File type arenas for HIR `TypeExprId` annotation lowering (var decls).
  // When `None`, body checking falls back to AstIndex / AST `TypeLowerer`.
  type_arenas: Option<&TypeArenasByDef>,
  // Class-expression span → constructor value type (from HIR decl lowering).
  // Anonymous `const C = class { #m(){} }` must carry privates on the instance
  // so outside access can emit TS18013.
  class_expr_value_tys: &HashMap<TextRange, TypeId>,
  // JS expando members (outer var def → member names) from `Outer.X = …`
  // special assignments; the binding-site assignability check is skipped for
  // these (tsc derives the member type from the RHS).
  expando_members: &HashMap<DefId, HashSet<String>>,
) -> BodyCheckResult {
  if let Some(flag) = cancelled {
    if flag.load(Ordering::Relaxed) {
      panic_any(crate::FatalError::Cancelled);
    }
  }
  let prim = store.primitive_ids();
  let expr_types = vec![prim.unknown; body.exprs.len()];
  let pat_types = vec![prim.unknown; body.pats.len()];
  let expr_spans: Vec<TextRange> = body.exprs.iter().map(|e| e.span).collect();
  let pat_spans: Vec<TextRange> = body.pats.iter().map(|p| p.span).collect();
  let ast = ast_index.ast();

  let expr_map: HashMap<TextRange, ExprId> = body
    .exprs
    .iter()
    .enumerate()
    .map(|(idx, expr)| (expr.span, ExprId(idx as u32)))
    .collect();
  let pat_map: HashMap<TextRange, PatId> = body
    .pats
    .iter()
    .enumerate()
    .map(|(idx, pat)| (pat.span, PatId(idx as u32)))
    .collect();

  let body_range = body_range(body);
  let mut relate_hooks = super::relate_hooks();
  if let Some(expander) = relate_expander {
    relate_hooks.expander = Some(expander);
  }
  if let Some(flag) = cancelled {
    relate_hooks.should_stop = Some(flag.as_ref());
  }
  let relate = RelateCtx::with_hooks_and_cache(
    Arc::clone(&store),
    store.options(),
    relate_hooks,
    caches.relation.clone(),
  );
  let type_resolver = resolver.clone();
  let mut lowerer = match resolver {
    Some(resolver) => TypeLowerer::with_resolver(Arc::clone(&store), resolver),
    None => TypeLowerer::new(Arc::clone(&store)),
  };
  lowerer.set_file(file);
  let synthetic_top_level = matches!(body.kind, BodyKind::TopLevel)
    && body.exprs.is_empty()
    && body.stmts.is_empty()
    && body.pats.is_empty();
  let native_define_class_fields =
    use_define_for_class_fields && matches!(target, ScriptTarget::Es2022 | ScriptTarget::EsNext);
  let types_at_start = store.type_count();
  let jsdoc_typedefs = jsdoc_source
    .map(crate::jsdoc::collect_file_typedefs)
    .unwrap_or_default();
  let hir_var_type_anns = hir_var_type_annotations(body);
  let mut checker = Checker {
    store,
    relate,
    eval_caches: caches.eval.clone(),
    instantiation_cache: caches.instantiation.clone(),
    lowerer,
    type_resolver,
    jsx_mode,
    jsx_element_ty: None,
    jsx_element_class_ty: None,
    jsx_intrinsic_elements_ty: None,
    jsx_intrinsic_attributes_ty: None,
    jsx_intrinsic_class_attributes_def: None,
    jsx_element_attributes_prop_name: None,
    jsx_library_managed_attributes_def: None,
    jsx_children_prop_name: None,
    jsx_namespace_missing_reported: false,
    expr_types,
    pat_types,
    expr_spans,
    pat_spans,
    expr_map,
    pat_map,
    diagnostics: Vec::new(),
    implicit_any_reported: HashSet::new(),
    assertion_overlap_reported: HashSet::new(),
    established_var_bindings: HashSet::new(),
    destructuring_assignment: false,
    return_types: Vec::new(),
    yield_types: Vec::new(),
    index: ast_index,
    scopes: vec![Scope::default()],
    type_param_scopes: Vec::new(),
    namespace_scopes: HashMap::new(),
    namespace_established_vars: HashMap::new(),
    expected_return: None,
    expected_return_defer_type_params: false,
    body_kind: body.kind,
    in_async_function: false,
    check_var_assignments: !synthetic_top_level,
    widen_object_literals: true,
    no_implicit_any,
    use_define_for_class_fields,
    strict_null_checks,
    strict_property_initialization,
    native_define_class_fields,
    target,
    current_class_field_param_props: None,
    class_field_initializer: None,
    field_init_type_stack: Vec::new(),
    constructor_class_index: None,
    enclosing_class_index: None,
    spi_ctor: None,
    file,
    jsdoc_source,
    jsdoc_typedefs,
    ref_expander: relate_expander,
    def_type_param_decls: type_param_decls,
    contextual_fn_ty,
    contextual_this_ty: None,
    contextual_this_is_static: None,
    cancelled,
    engine_budget_diagnostic_emitted: false,
    eval_budget_exceeded: Cell::new(false),
    expr_steps: Cell::new(0),
    expr_step_limit: Checker::DEFAULT_EXPR_STEP_LIMIT,
    types_at_start,
    max_type_growth: Checker::DEFAULT_MAX_TYPE_GROWTH,
    body,
    type_arenas,
    hir_var_type_anns,
    class_expr_value_tys,
    expando_members,
    names,
    _bump: Bump::new(),
  };

  checker.seed_builtins();
  for (name, ty) in bindings {
    checker.insert_binding(name.clone(), *ty, Vec::new());
  }

  match body.kind {
    BodyKind::TopLevel => {
      checker.check_class_field_overwrites_base_properties();
      checker.check_class_private_name_grammar();
      checker.check_class_private_name_uniqueness();
      checker.check_class_duplicate_function_implementations();
      checker.check_class_subsequent_property_types();
      checker.check_abstract_property_initializers();
      checker.check_strict_property_initialization();
      checker.check_stmt_list(&ast.stx.body);
    }
    BodyKind::Function => {
      // Overload signatures / `declare function` now carry HIR `FunctionData`
      // with `has_body: false` (no AST implementation). There is nothing to
      // type-check in the body; skip the AstIndex function lookup.
      let signature_only = body.function.as_ref().is_some_and(|func| !func.has_body);
      if !signature_only {
        let found = checker.check_enclosing_function(body_range);
        if !found {
          checker.diagnostics.push(codes::MISSING_BODY.error(
            "missing function body for checker",
            Span::new(file, body_range),
          ));
        }
      }
    }
    BodyKind::Initializer => {
      let found = checker.check_matching_initializer(body_range);
      if !found {
        checker.diagnostics.push(codes::MISSING_BODY.error(
          "missing initializer body for checker",
          Span::new(file, body_range),
        ));
      }
    }
    BodyKind::Class => {
      let found = checker.check_enclosing_class(body_range);
      if !found {
        checker.diagnostics.push(codes::MISSING_BODY.error(
          "missing class body for checker",
          Span::new(file, body_range),
        ));
      }
    }
    BodyKind::Unknown => {
      checker
        .diagnostics
        .push(codes::MISSING_BODY.error("missing body for checker", Span::new(file, body_range)));
    }
  }

  checker
    .diagnostics
    .extend(checker.lowerer.take_diagnostics());
  checker.observe_engine_budget(Span::new(file, body_range));
  codes::normalize_diagnostics(&mut checker.diagnostics);
  BodyCheckResult {
    body: body_id,
    expr_types: checker.expr_types,
    expr_spans: checker.expr_spans,
    pat_types: checker.pat_types,
    pat_spans: checker.pat_spans,
    diagnostics: checker.diagnostics,
    return_types: checker.return_types,
    yield_types: checker.yield_types,
  }
}

#[derive(Clone, Debug)]
pub(crate) enum ArrayLiteralContext {
  Tuple(Vec<types_ts_interned::TupleElem>),
  Array(TypeId),
}

#[derive(Debug)]
pub(crate) struct JsxActualProps {
  pub(crate) ty: TypeId,
  pub(crate) props: HashSet<String>,
  pub(crate) has_spread: bool,
}

#[derive(Clone, Debug)]
pub(crate) struct ClassFieldInitializerContext {
  pub(crate) class_index: usize,
  pub(crate) member_index: usize,
  pub(crate) is_static: bool,
}

/// Constructor-local state for `strictPropertyInitialization` use-before-assign
/// (TS2565). TS2564 (missing definite assignment) is analyzed separately at
/// top-level from the class AST.
#[derive(Clone, Debug)]
pub(crate) struct SpiCtorState {
  /// Instance props that must be assigned before use (non-undefined types).
  pub(crate) required: HashSet<String>,
  /// Props assigned on the current control-flow path.
  pub(crate) assigned: HashSet<String>,
}

pub(crate) struct Checker<'a> {
  pub(crate) store: Arc<TypeStore>,
  pub(crate) relate: RelateCtx<'a>,
  pub(crate) eval_caches: EvaluatorCaches,
  pub(crate) instantiation_cache: InstantiationCache,
  pub(crate) lowerer: TypeLowerer,
  pub(crate) type_resolver: Option<Arc<dyn TypeResolver>>,
  pub(crate) jsx_mode: Option<JsxMode>,
  pub(crate) jsx_element_ty: Option<TypeId>,
  pub(crate) jsx_element_class_ty: Option<TypeId>,
  pub(crate) jsx_intrinsic_elements_ty: Option<TypeId>,
  pub(crate) jsx_intrinsic_attributes_ty: Option<TypeId>,
  pub(crate) jsx_intrinsic_class_attributes_def: Option<Option<DefId>>,
  pub(crate) jsx_element_attributes_prop_name: Option<Option<TsNameId>>,
  pub(crate) jsx_library_managed_attributes_def: Option<Option<DefId>>,
  pub(crate) jsx_children_prop_name: Option<TsNameId>,
  pub(crate) jsx_namespace_missing_reported: bool,
  pub(crate) expr_types: Vec<TypeId>,
  pub(crate) pat_types: Vec<TypeId>,
  pub(crate) expr_spans: Vec<TextRange>,
  pub(crate) pat_spans: Vec<TextRange>,
  pub(crate) expr_map: HashMap<TextRange, ExprId>,
  pub(crate) pat_map: HashMap<TextRange, PatId>,
  pub(crate) diagnostics: Vec<Diagnostic>,
  pub(crate) implicit_any_reported: HashSet<TextRange>,
  /// Spans already reported for TS2352 type-assertion overlap (check_expr may
  /// visit the same assertion more than once).
  pub(crate) assertion_overlap_reported: HashSet<TextRange>,
  /// `var` names whose type was established by a prior declarator in this body
  /// check. Used so TS2403 ignores binder/pre-seed types and only fires on true
  /// subsequent `var` merges.
  pub(crate) established_var_bindings: HashSet<String>,
  /// True while binding a *destructuring assignment* pattern (not a
  /// declaration): existing bindings are checked against their declared type
  /// and flow-narrowed, never rebound with a fresh `declared_ty`
  /// (`assignmentTypeNarrowing.ts`).
  pub(crate) destructuring_assignment: bool,
  pub(crate) return_types: Vec<TypeId>,
  /// Operand types of `yield` / `yield*` expressions in the current function
  /// body, for generator return-type inference (tsc aggregates the yield
  /// union into `Generator<Y, R, N>` and checks it against the contextual
  /// return type instead of adopting it blindly).
  pub(crate) yield_types: Vec<TypeId>,
  pub(crate) index: &'a AstIndex<'a>,
  pub(crate) scopes: Vec<Scope>,
  pub(crate) type_param_scopes: Vec<Vec<TypeParamDecl>>,
  pub(crate) namespace_scopes: HashMap<String, Scope>,
  /// Per-namespace `established_var_bindings` so sibling nested namespaces do
  /// not false-TS2403 on the same `var` name (`…CallSignatures4` `a2`/`b2`).
  pub(crate) namespace_established_vars: HashMap<String, HashSet<String>>,
  pub(crate) expected_return: Option<TypeId>,
  /// True when `expected_return` comes from a *contextual* generic signature
  /// (a lambda checked against an uninstantiated call parameter) and mentions a
  /// type parameter. Hard return-assignability diagnostics are deferred in that
  /// case: tsc validates such returns after inference instantiates the
  /// signature, and free type params are nominal targets (`number` ↛ `U`).
  pub(crate) expected_return_defer_type_params: bool,
  pub(crate) body_kind: BodyKind,
  pub(crate) in_async_function: bool,
  pub(crate) check_var_assignments: bool,
  pub(crate) widen_object_literals: bool,
  pub(crate) no_implicit_any: bool,
  pub(crate) use_define_for_class_fields: bool,
  pub(crate) strict_null_checks: bool,
  pub(crate) strict_property_initialization: bool,
  pub(crate) native_define_class_fields: bool,
  /// Script target for grammar checks that depend on language version
  /// (e.g. TS18028 private identifiers require ES2015+).
  pub(crate) target: ScriptTarget,
  pub(crate) current_class_field_param_props: Option<&'a [String]>,
  pub(crate) class_field_initializer: Option<ClassFieldInitializerContext>,
  /// Stack of `(class_index, prop_name)` while resolving field initializer
  /// types (detects TS7022 circularity for self / mutual `this.#x` refs).
  pub(crate) field_init_type_stack: Vec<(usize, String)>,
  /// Set while type-checking a constructor body (TS2715 class-init flow).
  pub(crate) constructor_class_index: Option<usize>,
  /// Lexically enclosing class while checking a class member body / field
  /// initializer / static block (for private-name diagnostics such as TS2806).
  pub(crate) enclosing_class_index: Option<usize>,
  /// Path-sensitive SPI tracking while checking a constructor (TS2565).
  pub(crate) spi_ctor: Option<SpiCtorState>,
  pub(crate) file: FileId,
  /// File source for leading JSDoc `@type` / `@param` / `@returns` /
  /// `@typedef` / `@template` extraction (checkJs / `.js` files).
  pub(crate) jsdoc_source: Option<&'a str>,
  /// File-scope `@typedef` map collected from [`Self::jsdoc_source`].
  pub(crate) jsdoc_typedefs: HashMap<String, crate::jsdoc::OwnedJsdocTypedef>,
  pub(crate) ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
  pub(crate) def_type_param_decls: Option<&'a HashMap<DefId, Arc<[TypeParamDecl]>>>,
  pub(crate) contextual_fn_ty: Option<TypeId>,
  /// Contextual `this` type: class member bodies (ctor / methods / field
  /// initializers / static blocks), or a JSDoc/`this:` signature while refining
  /// a function expression against an expected callable.
  pub(crate) contextual_this_ty: Option<TypeId>,
  /// Whether the current member body is static (seeded alongside
  /// `contextual_this_ty`) — used by `super` member resolution to pick the
  /// base constructor vs the base instance.
  pub(crate) contextual_this_is_static: Option<bool>,
  pub(crate) cancelled: Option<&'a Arc<AtomicBool>>,
  /// Latched once when a relation/eval/instantiation budget trips so we emit a
  /// single [`codes::ENGINE_BUDGET_EXCEEDED`] diagnostic per body.
  pub(crate) engine_budget_diagnostic_emitted: bool,
  /// True when an evaluator (outside RelateCtx) hit its step/stop budget.
  pub(crate) eval_budget_exceeded: Cell<bool>,
  /// Per-body expression visits; bounds work that never enters the relation
  /// engine (the `parserRealSource12` pathology was mostly here).
  pub(crate) expr_steps: Cell<usize>,
  pub(crate) expr_step_limit: usize,
  /// TypeStore size at body-check start; growth beyond [`Self::max_type_growth`]
  /// trips the engine budget (shared store can otherwise grow without bound
  /// across many relate/eval steps that individually stay under step limits).
  pub(crate) types_at_start: usize,
  pub(crate) max_type_growth: usize,
  /// HIR body being checked (annotations via [`TypeExprId`], not AstIndex).
  pub(crate) body: &'a Body,
  /// File type arenas; when set, var annotations lower from HIR first.
  pub(crate) type_arenas: Option<&'a TypeArenasByDef>,
  /// Pat span → HIR type annotation for var declarators in [`Self::body`].
  pub(crate) hir_var_type_anns: HashMap<TextRange, TypeExprId>,
  /// Class-expression span → constructor value type (includes private members).
  pub(crate) class_expr_value_tys: &'a HashMap<TextRange, TypeId>,
  /// JS expando members (outer var def → member names) from `Outer.X = …`
  /// special assignments; the binding-site assignability check is skipped.
  pub(crate) expando_members: &'a HashMap<DefId, HashSet<String>>,
  pub(crate) names: &'a NameInterner,
  pub(crate) _bump: Bump,
}

impl<'a> Checker<'a> {
  /// Generous per-body expression visit budget.
  ///
  /// Far above typical bodies in the 401-case shard sample; low enough that the
  /// `parserRealSource12` / unresolved-index-assign pathology fails fast.
  pub(crate) const DEFAULT_EXPR_STEP_LIMIT: usize = 100_000;
  /// Max new interned types a single body may add to the shared store.
  pub(crate) const DEFAULT_MAX_TYPE_GROWTH: usize = 5_000;

  pub(crate) fn type_param_constraint(&self, param: TypeParamId) -> Option<TypeId> {
    for scope in self.type_param_scopes.iter().rev() {
      if let Some(decl) = scope.iter().find(|decl| decl.id == param) {
        return decl.constraint;
      }
    }
    None
  }

  fn expand_callable_type(&self, ty: TypeId) -> TypeId {
    let mut current = self.expand_ref(ty);
    let mut seen = HashSet::new();
    while seen.insert(current) {
      match self.store.type_kind(current) {
        TypeKind::TypeParam(param) => {
          let Some(constraint) = self.type_param_constraint(param) else {
            break;
          };
          current = self.expand_ref(constraint);
        }
        // Expand alias/interface members then re-intersect so conflicting
        // discriminants collapse to `never` (tsc getIntersectionType).
        TypeKind::Intersection(members) => {
          let expanded: Vec<TypeId> = members.iter().map(|m| self.expand_ref(*m)).collect();
          let next = self.store.intersection(expanded);
          if next == current {
            break;
          }
          current = next;
        }
        _ => break,
      }
    }
    current
  }

  fn apply_explicit_type_args(&mut self, base: TypeId, type_args: &[TypeId], span: Span) -> TypeId {
    if type_args.is_empty() {
      return base;
    }
    let mut reported_arity = false;
    let mut reported_constraint = false;

    fn instantiate_signature(
      checker: &mut Checker<'_>,
      sig_id: SignatureId,
      type_args: &[TypeId],
      span: Span,
      reported_arity: &mut bool,
      reported_constraint: &mut bool,
    ) -> Option<SignatureId> {
      let sig = checker.store.signature(sig_id);

      // tsc: when explicit type arguments are provided, signatures without
      // type parameters are silently excluded from candidacy (lib
      // `ArrayConstructor` has a non-generic `new (arrayLength?): any[]`
      // overload; `new Array<number>()` must not TS2558 on it).
      if sig.type_params.is_empty() && !type_args.is_empty() {
        return None;
      }

      let declared = sig.type_params.len();
      if type_args.len() > declared && !*reported_arity {
        checker
          .diagnostics
          .push(codes::WRONG_TYPE_ARGUMENT_COUNT.error(
            format!(
              "Expected {declared} type arguments, but got {}.",
              type_args.len()
            ),
            span,
          ));
        *reported_arity = true;
      }

      let mut subst = HashMap::new();
      let mut prefix_subst: HashMap<TypeParamId, TypeId> = HashMap::new();
      for (idx, decl) in sig.type_params.iter().enumerate() {
        let Some(arg) = type_args.get(idx).copied() else {
          break;
        };

        if let Some(constraint) = decl.constraint {
          let instantiated_constraint = if prefix_subst.is_empty() {
            constraint
          } else {
            let mut substituter =
              Substituter::new(Arc::clone(&checker.store), prefix_subst.clone());
            substituter.substitute_type(constraint)
          };

          if !checker.relate.is_assignable(arg, instantiated_constraint) && !*reported_constraint {
            checker
              .diagnostics
              .push(codes::TYPE_ARGUMENT_CONSTRAINT_VIOLATION.error(
                format!(
                  "Type '{}' does not satisfy the constraint '{}'.",
                  TypeDisplay::new(checker.store.as_ref(), arg),
                  TypeDisplay::new(checker.store.as_ref(), instantiated_constraint)
                ),
                span,
              ));
            *reported_constraint = true;
          }
        }

        subst.insert(decl.id, arg);
        prefix_subst.insert(decl.id, arg);
      }

      Some(
        checker
          .instantiation_cache
          .instantiate_signature(&checker.store, sig_id, &sig, &subst),
      )
    }

    fn inner(
      checker: &mut Checker<'_>,
      ty: TypeId,
      type_args: &[TypeId],
      span: Span,
      reported_arity: &mut bool,
      reported_constraint: &mut bool,
    ) -> TypeId {
      let ty = checker.expand_callable_type(ty);
      match checker.store.type_kind(ty) {
        TypeKind::Any | TypeKind::Unknown | TypeKind::Never => ty,
        TypeKind::Callable { overloads } => {
          let mut instantiated: Vec<_> = overloads
            .iter()
            .copied()
            .filter_map(|sig_id| {
              instantiate_signature(
                checker,
                sig_id,
                type_args,
                span,
                reported_arity,
                reported_constraint,
              )
            })
            .collect();
          // All signatures were non-generic and explicit type args were
          // provided: tsc reports TS2558 once but continues with the
          // signatures (e.g. `f<number>()` on a non-generic `f`).
          if instantiated.is_empty() && !overloads.is_empty() {
            if !*reported_arity {
              checker
                .diagnostics
                .push(codes::WRONG_TYPE_ARGUMENT_COUNT.error(
                  format!("Expected 0 type arguments, but got {}.", type_args.len()),
                  span,
                ));
              *reported_arity = true;
            }
            instantiated = overloads.clone();
          }
          instantiated.sort();
          instantiated.dedup();
          checker.store.intern_type(TypeKind::Callable {
            overloads: instantiated,
          })
        }
        TypeKind::Object(obj_id) => {
          let obj = checker.store.object(obj_id);
          let mut shape = checker.store.shape(obj.shape);
          let mut changed = false;

          if !shape.call_signatures.is_empty() {
            let mut call_sigs = Vec::new();
            let mut seen = HashSet::new();
            for sig_id in shape.call_signatures.iter().copied() {
              if let Some(inst) = instantiate_signature(
                checker,
                sig_id,
                type_args,
                span,
                reported_arity,
                reported_constraint,
              ) {
                if seen.insert(inst) {
                  call_sigs.push(inst);
                }
              }
            }
            if call_sigs.is_empty() && !type_args.is_empty() {
              // All signatures were non-generic and explicit type args were
              // provided: tsc reports TS2558 once but continues.
              if !*reported_arity {
                checker
                  .diagnostics
                  .push(codes::WRONG_TYPE_ARGUMENT_COUNT.error(
                    format!("Expected 0 type arguments, but got {}.", type_args.len()),
                    span,
                  ));
                *reported_arity = true;
              }
              call_sigs = shape.call_signatures.clone();
            }
            if call_sigs != shape.call_signatures {
              shape.call_signatures = call_sigs;
              changed = true;
            }
          }

          if !shape.construct_signatures.is_empty() {
            let mut construct_sigs = Vec::new();
            let mut seen = HashSet::new();
            for sig_id in shape.construct_signatures.iter().copied() {
              if let Some(inst) = instantiate_signature(
                checker,
                sig_id,
                type_args,
                span,
                reported_arity,
                reported_constraint,
              ) {
                if seen.insert(inst) {
                  construct_sigs.push(inst);
                }
              }
            }
            if construct_sigs.is_empty() && !type_args.is_empty() {
              // All signatures were non-generic and explicit type args were
              // provided: tsc reports TS2558 once but continues.
              if !*reported_arity {
                checker
                  .diagnostics
                  .push(codes::WRONG_TYPE_ARGUMENT_COUNT.error(
                    format!("Expected 0 type arguments, but got {}.", type_args.len()),
                    span,
                  ));
                *reported_arity = true;
              }
              construct_sigs = shape.construct_signatures.clone();
            }
            if construct_sigs != shape.construct_signatures {
              shape.construct_signatures = construct_sigs;
              changed = true;
            }
          }

          if !changed {
            return ty;
          }

          let shape_id = checker.store.intern_shape(shape);
          let obj_id = checker.store.intern_object(ObjectType { shape: shape_id });
          checker.store.intern_type(TypeKind::Object(obj_id))
        }
        TypeKind::Union(members) => {
          let mapped: Vec<_> = members
            .iter()
            .copied()
            .map(|member| {
              inner(
                checker,
                member,
                type_args,
                span,
                reported_arity,
                reported_constraint,
              )
            })
            .collect();
          checker.store.union(mapped)
        }
        TypeKind::Intersection(members) => {
          let mapped: Vec<_> = members
            .iter()
            .copied()
            .map(|member| {
              inner(
                checker,
                member,
                type_args,
                span,
                reported_arity,
                reported_constraint,
              )
            })
            .collect();
          checker.store.intersection(mapped)
        }
        _ => {
          if !*reported_arity {
            checker
              .diagnostics
              .push(codes::WRONG_TYPE_ARGUMENT_COUNT.error(
                format!("Expected 0 type arguments, but got {}.", type_args.len()),
                span,
              ));
            *reported_arity = true;
          }
          checker.store.primitive_ids().unknown
        }
      }
    }

    inner(
      self,
      base,
      type_args,
      span,
      &mut reported_arity,
      &mut reported_constraint,
    )
  }

  fn expand_ref(&self, ty: TypeId) -> TypeId {
    let mut current = self.store.canon(ty);
    let Some(expander) = self.ref_expander else {
      return current;
    };
    let mut seen = HashSet::new();
    while seen.insert(current) {
      match self.store.type_kind(current) {
        TypeKind::Ref { def, args } => {
          if let Some(expanded) = expander.expand_ref(self.store.as_ref(), def, &args) {
            current = self.store.canon(expanded);
            continue;
          }
        }
        _ => {}
      }
      break;
    }
    current
  }

  fn expand_for_props(&self, ty: TypeId) -> TypeId {
    let Some(expander) = self.ref_expander else {
      return ty;
    };
    match self.store.type_kind(ty) {
      TypeKind::Ref { .. } | TypeKind::IndexedAccess { .. } => {}
      _ => return ty,
    }
    struct Adapter<'a> {
      hook: &'a dyn types_ts_interned::RelateTypeExpander,
    }

    impl<'a> TypeExpander for Adapter<'a> {
      fn expand(
        &self,
        store: &TypeStore,
        def: types_ts_interned::DefId,
        args: &[TypeId],
      ) -> Option<ExpandedType> {
        self
          .hook
          .expand_ref(store, def, args)
          .map(|ty| ExpandedType {
            params: Vec::new(),
            ty,
          })
      }
    }

    let adapter = Adapter { hook: expander };
    let mut evaluator =
      TypeEvaluator::with_caches(Arc::clone(&self.store), &adapter, self.eval_caches.clone());
    if let Some(flag) = self.cancelled {
      evaluator = evaluator.with_should_stop(flag.as_ref());
    }
    let result = evaluator.evaluate(ty);
    if evaluator.budget_exceeded() {
      self.eval_budget_exceeded.set(true);
    }
    result
  }

  fn has_excess_properties(
    &self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    target: TypeId,
  ) -> bool {
    self.first_excess_property(obj, target).is_some()
  }

  /// First excess property on a fresh object literal, in source order.
  ///
  /// Prefers a property rejected on its own (tsc `isKnownProperty`-style). When
  /// the full set is rejected but every name is known on some constituent
  /// (stricter union cases), falls back to the first property key.
  fn first_excess_property(
    &self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    target: TypeId,
  ) -> Option<(String, Loc)> {
    let mut props: Vec<(String, Loc)> = Vec::new();
    for member in obj.stx.members.iter() {
      match &member.stx.typ {
        ObjMemberType::Valued { key, .. } => {
          if let ClassOrObjKey::Direct(direct) = key {
            props.push((direct.stx.key.clone(), direct.loc));
          }
        }
        ObjMemberType::Shorthand { id } => {
          props.push((id.stx.name.clone(), id.loc));
        }
        ObjMemberType::Rest { .. } => return None,
      }
    }
    let all: HashSet<String> = props.iter().map(|(name, _)| name.clone()).collect();
    if self.type_accepts_props(target, &all) {
      return None;
    }
    let mut single = HashSet::with_capacity(1);
    for (name, loc) in &props {
      single.clear();
      single.insert(name.clone());
      if !self.type_accepts_props(target, &single) {
        return Some((name.clone(), *loc));
      }
    }
    props.first().map(|(name, loc)| (name.clone(), *loc))
  }

  /// Emit [`codes::EXCESS_PROPERTY`] (TS2353) for a fresh object literal when it
  /// has an excess property relative to `target`. Primary span is the property
  /// key (tsc-aligned).
  fn report_excess_property(
    &mut self,
    obj: &Node<parse_js::ast::expr::lit::LitObjExpr>,
    target: TypeId,
  ) -> bool {
    let Some((name, key_loc)) = self.first_excess_property(obj, target) else {
      return false;
    };
    // Use the tsc-shaped "does not exist" message only when the name is rejected
    // on its own. When the full set fails but every name is known on some
    // constituent (stricter union cases), avoid a misleading claim.
    let mut single = HashSet::with_capacity(1);
    single.insert(name.clone());
    let message = if !self.type_accepts_props(target, &single) {
      let target_disp = TypeDisplay::new(self.store.as_ref(), self.store.canon(target)).to_string();
      codes::excess_property_message(&name, &target_disp)
    } else {
      "Object literal may only specify known properties.".to_string()
    };
    self.diagnostics.push(codes::EXCESS_PROPERTY.error(
      message,
      Span {
        file: self.file,
        range: loc_to_range(self.file, key_loc),
      },
    ));
    true
  }

  fn has_contextual_excess_properties(&mut self, expr: &Node<AstExpr>, expected: TypeId) -> bool {
    fn inner(
      checker: &mut Checker<'_>,
      expr: &Node<AstExpr>,
      expected: TypeId,
      depth: usize,
    ) -> bool {
      if depth > 32 {
        return false;
      }
      let prim = checker.store.primitive_ids();
      let expected = checker.store.canon(expected);
      if expected == prim.unknown {
        return false;
      }
      match expr.stx.as_ref() {
        AstExpr::LitObj(obj) => {
          if checker.has_excess_properties(obj, expected) {
            return true;
          }
          for member in obj.stx.members.iter() {
            let (name, value) = match &member.stx.typ {
              ObjMemberType::Valued {
                key: ClassOrObjKey::Direct(key),
                val: ClassOrObjVal::Prop(Some(expr)),
              } => (Some(key.stx.key.as_str()), Some(expr)),
              _ => (None, None),
            };
            let (Some(name), Some(value)) = (name, value) else {
              continue;
            };
            let expected_prop = checker.member_type(expected, name);
            if expected_prop == prim.unknown {
              continue;
            }
            if inner(checker, value, expected_prop, depth + 1) {
              return true;
            }
          }
          false
        }
        AstExpr::LitArr(arr) => {
          use parse_js::ast::expr::lit::LitArrElem;

          if arr
            .stx
            .elements
            .iter()
            .any(|e| !matches!(e, LitArrElem::Single(_)))
          {
            return false;
          }

          let elems: Vec<_> = arr
            .stx
            .elements
            .iter()
            .filter_map(|e| match e {
              LitArrElem::Single(v) => Some(v),
              _ => None,
            })
            .collect();
          let arity = elems.len();
          let contexts = checker.array_literal_context_candidates(expected, arity);
          if contexts.is_empty() {
            return false;
          }

          for context in contexts.into_iter() {
            let passes = match context {
              ArrayLiteralContext::Tuple(expected_elems) => {
                elems.iter().enumerate().all(|(idx, expr)| {
                  let expected_elem = expected_elems
                    .get(idx)
                    .map(|e| e.ty)
                    .unwrap_or(prim.unknown);
                  !inner(checker, expr, expected_elem, depth + 1)
                })
              }
              ArrayLiteralContext::Array(expected_elem) => elems
                .iter()
                .all(|expr| !inner(checker, expr, expected_elem, depth + 1)),
            };
            if passes {
              return false;
            }
          }

          true
        }
        _ => false,
      }
    }

    inner(self, expr, expected, 0)
  }

  fn type_accepts_props(&self, target: TypeId, props: &HashSet<String>) -> bool {
    let target = self.expand_ref(target);
    let expanded = self.expand_for_props(target);
    if expanded != target {
      return self.type_accepts_props(expanded, props);
    }
    match self.store.type_kind(target) {
      TypeKind::Union(members) => {
        let mut saw_object = false;
        for member in members {
          let member = self.expand_ref(self.expand_for_props(member));
          match self.store.type_kind(member) {
            TypeKind::Object(_)
            | TypeKind::Union(_)
            | TypeKind::Intersection(_)
            | TypeKind::Mapped(_) => {
              saw_object = true;
              if self.type_accepts_props(member, props) {
                return true;
              }
            }
            _ => {}
          }
        }
        !saw_object
      }
      TypeKind::Intersection(members) => {
        // Excess property checking on intersection targets behaves like checking
        // against the merged property set of all intersected object types. In
        // particular, `{ a } & { b }` should accept `{ a, b }` without treating
        // either `a` or `b` as excess.
        //
        // To keep union semantics correct, distribute unions inside the
        // intersection into a top-level union before applying the merged-props
        // check. This avoids incorrectly accepting `{ a, b }` for targets like
        // `({ a } | { b }) & { key }`.
        let expanded_members: Vec<TypeId> = members
          .iter()
          .copied()
          .map(|member| self.expand_ref(self.expand_for_props(member)))
          .collect();
        for (idx, member) in expanded_members.iter().enumerate() {
          if let TypeKind::Union(options) = self.store.type_kind(*member) {
            let mut distributed = Vec::with_capacity(options.len());
            for option in options {
              let mut parts = Vec::with_capacity(expanded_members.len());
              for (j, other) in expanded_members.iter().enumerate() {
                if j == idx {
                  continue;
                }
                parts.push(*other);
              }
              parts.push(option);
              distributed.push(self.store.intersection(parts));
            }
            return self.type_accepts_props(self.store.union(distributed), props);
          }
        }

        let mut object_members: Vec<TypeId> = Vec::new();
        for member in expanded_members.iter().copied() {
          match self.store.type_kind(member) {
            TypeKind::Object(_)
            | TypeKind::Union(_)
            | TypeKind::Intersection(_)
            | TypeKind::Mapped(_) => {
              object_members.push(member);
            }
            _ => {}
          }
        }

        if object_members.is_empty() {
          return true;
        }

        let mut single = HashSet::with_capacity(1);
        for prop in props {
          single.clear();
          single.insert(prop.clone());
          if !object_members
            .iter()
            .copied()
            .any(|member| self.type_accepts_props(member, &single))
          {
            return false;
          }
        }
        true
      }
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        if !shape.indexers.is_empty() {
          return true;
        }
        let mut allowed: HashSet<String> = HashSet::new();
        for prop in shape.properties.iter() {
          match prop.key {
            PropKey::String(name) | PropKey::Symbol(name) => {
              allowed.insert(self.store.name(name));
            }
            PropKey::Number(num) => {
              allowed.insert(num.to_string());
            }
          }
        }
        props.iter().all(|p| allowed.contains(p))
      }
      TypeKind::Mapped(_) => true,
      TypeKind::Ref { .. } => true,
      _ => true,
    }
  }

  pub(crate) fn expr_budget_exceeded(&self) -> bool {
    self.expr_steps.get() >= self.expr_step_limit
  }

  pub(crate) fn type_growth_exceeded(&self) -> bool {
    self.store.type_count().saturating_sub(self.types_at_start) > self.max_type_growth
  }

  pub(crate) fn observe_engine_budget(&mut self, span: Span) {
    self.check_cancelled();
    if self.type_growth_exceeded() {
      self.eval_budget_exceeded.set(true);
    }
    let hit = self.relate.budget_exceeded()
      || self.eval_budget_exceeded.get()
      || self.expr_budget_exceeded()
      || self.type_growth_exceeded();
    if hit && !self.engine_budget_diagnostic_emitted {
      self.engine_budget_diagnostic_emitted = true;
      self
        .diagnostics
        .push(codes::ENGINE_BUDGET_EXCEEDED.error("engine budget exceeded", span));
    }
  }

  /// Span for assignability / argument diagnostics (tsc `getErrorSpanForNode`).
  ///
  /// Named class/function expressions report on the binding name (`C` in
  /// `class C {…}`), not the whole expression body.
  pub(crate) fn error_range_for_expr(&self, expr: &Node<AstExpr>) -> TextRange {
    match expr.stx.as_ref() {
      AstExpr::Class(class_expr) => {
        if let Some(name) = class_expr.stx.name.as_ref() {
          return loc_to_range(self.file, name.loc);
        }
      }
      AstExpr::Func(func_expr) => {
        if let Some(name) = func_expr.stx.name.as_ref() {
          return loc_to_range(self.file, name.loc);
        }
      }
      _ => {}
    }
    loc_to_range(self.file, expr.loc)
  }

  fn check_assignable(
    &mut self,
    expr: &Node<AstExpr>,
    src: TypeId,
    dst: TypeId,
    range_override: Option<TextRange>,
  ) {
    self.check_assignable_with_code(expr, src, dst, range_override, &codes::TYPE_MISMATCH);
  }

  fn check_assignable_with_code(
    &mut self,
    expr: &Node<AstExpr>,
    src: TypeId,
    dst: TypeId,
    range_override: Option<TextRange>,
    base_code: &'static codes::Code,
  ) {
    self.check_cancelled();
    let prim = self.store.primitive_ids();
    // Note: void *return* positions skip this helper in `check_stmt` /
    // `check_function_body` (contextual `() => void` callbacks may return
    // values). Annotated `void` bindings still use normal assignability
    // (`nullAssignableToEveryType.ts`: `var g: void = null`).
    if matches!(self.store.type_kind(src), TypeKind::Any | TypeKind::Unknown)
      || matches!(self.store.type_kind(dst), TypeKind::Any | TypeKind::Unknown)
    {
      return;
    }
    if let TypeKind::Array { ty, .. } = self.store.type_kind(src) {
      if matches!(self.store.type_kind(ty), TypeKind::Unknown) {
        return;
      }
    }
    if matches!(self.store.type_kind(src), TypeKind::Conditional { .. })
      || matches!(self.store.type_kind(dst), TypeKind::Conditional { .. })
    {
      return;
    }
    // Mapped destinations are checked after expansion via relate / missing-prop
    // selection (`assignmentCompatWithEnumIndexer.ts`: `Record<E, any> = {}`).
    // Previously skipped entirely, which hid TS2741 for mapped Record targets.
    if let AstExpr::LitObj(obj) = expr.stx.as_ref() {
      if self.report_excess_property(obj, dst) {
        return;
      }
    }
    let assignable =
      self.is_assignable_for_check(src, dst) && self.variance_allows_assignability(src, dst);
    let span = Span {
      file: self.file,
      range: range_override.unwrap_or_else(|| self.error_range_for_expr(expr)),
    };
    self.observe_engine_budget(span);
    if assignable {
      return;
    }
    if std::env::var("DEBUG_TYPE_MISMATCH").is_ok() {
      eprintln!(
        "DEBUG_TYPE_MISMATCH src={} {:?} dst={} {:?}",
        TypeDisplay::new(self.store.as_ref(), src),
        self.store.type_kind(src),
        TypeDisplay::new(self.store.as_ref(), dst),
        self.store.type_kind(dst)
      );
    }
    let base_range = range_override.unwrap_or_else(|| self.error_range_for_expr(expr));
    if let AstExpr::LitObj(obj) = expr.stx.as_ref() {
      let mut mismatched_props = Vec::new();
      for member in obj.stx.members.iter() {
        let (prop, key_loc) = match &member.stx.typ {
          ObjMemberType::Valued {
            key: ClassOrObjKey::Direct(key),
            ..
          } => (key.stx.key.clone(), Some(key.loc)),
          ObjMemberType::Shorthand { id } => (id.stx.name.clone(), Some(id.loc)),
          _ => continue,
        };
        let prop_src = self.member_type(src, &prop);
        let prop_dst = self.member_type(dst, &prop);
        if prop_src == prim.unknown || prop_dst == prim.unknown {
          continue;
        }
        if !self.relate.is_assignable(prop_src, prop_dst) {
          mismatched_props.push((prop, key_loc));
        }
      }

      if !mismatched_props.is_empty() {
        for (prop, key_loc) in mismatched_props {
          let range = key_loc
            .map(|loc| loc_to_range(self.file, loc))
            .unwrap_or(base_range);
          let range = TextRange::new(range.start, range.start.saturating_add(prop.len() as u32));
          self.diagnostics.push(codes::TYPE_MISMATCH.error(
            "type mismatch",
            Span {
              file: self.file,
              range,
            },
          ));
        }
        return;
      }
    }

    if let AstExpr::LitArr(arr) = expr.stx.as_ref() {
      if arr
        .stx
        .elements
        .iter()
        .all(|elem| matches!(elem, parse_js::ast::expr::lit::LitArrElem::Single(_)))
      {
        let elems: Vec<_> = arr
          .stx
          .elements
          .iter()
          .filter_map(|elem| match elem {
            parse_js::ast::expr::lit::LitArrElem::Single(expr) => Some(expr),
            _ => None,
          })
          .collect();
        let contexts = self.array_literal_context_candidates(dst, elems.len());
        if let Some(context) = contexts.into_iter().next() {
          let mut mismatched_elems: Vec<&Node<AstExpr>> = Vec::new();
          match context {
            ArrayLiteralContext::Tuple(expected_elems) => {
              for (idx, elem) in elems.iter().enumerate() {
                let expected_elem = expected_elems
                  .get(idx)
                  .map(|e| e.ty)
                  .unwrap_or(prim.unknown);
                if expected_elem == prim.unknown {
                  continue;
                }
                let elem_ty = self.recorded_expr_type(elem.loc).unwrap_or(prim.unknown);
                if elem_ty != prim.unknown && !self.relate.is_assignable(elem_ty, expected_elem) {
                  mismatched_elems.push(elem);
                }
              }
            }
            ArrayLiteralContext::Array(expected_elem) => {
              if expected_elem != prim.unknown {
                for elem in elems.iter() {
                  let elem_ty = self.recorded_expr_type(elem.loc).unwrap_or(prim.unknown);
                  if elem_ty != prim.unknown && !self.relate.is_assignable(elem_ty, expected_elem) {
                    mismatched_elems.push(elem);
                  }
                }
              }
            }
          }

          if !mismatched_elems.is_empty() {
            for elem in mismatched_elems {
              self.diagnostics.push(codes::TYPE_MISMATCH.error(
                "type mismatch",
                Span {
                  file: self.file,
                  range: loc_to_range(self.file, elem.loc),
                },
              ));
            }
            return;
          }
        }
      }
    }

    let code = self.assignability_mismatch_code(src, dst, base_code);
    self.diagnostics.push(code.error(
      "type mismatch",
      Span {
        file: self.file,
        range: base_range,
      },
    ));
  }

  /// Prefer tsc-aligned TS2741 / TS2739 over generic TS2322 when the only
  /// assignability failure is missing required properties on the target.
  ///
  /// Mirrors `reportUnmatchedProperty`: one unmatched → TS2741; several →
  /// TS2739. Cross-class private brands that share a `#name` are *present* on
  /// both shapes (and fail via private compatibility), so they stay TS2322.
  fn assignability_mismatch_code(
    &self,
    src: TypeId,
    dst: TypeId,
    base_code: &'static codes::Code,
  ) -> &'static codes::Code {
    if base_code.as_str() != codes::TYPE_MISMATCH.as_str() {
      return base_code;
    }
    match self.unmatched_required_property_count(src, dst) {
      Some(1) => &codes::MISSING_REQUIRED_PROPERTY,
      Some(n) if n > 1 => &codes::MISSING_PROPERTIES,
      Some(_) => base_code,
      None => {
        // Shape walk inconclusive (unions / non-objects). Fall back to the
        // relation reason tree's "missing property" note.
        if self.explain_is_missing_property_failure(src, dst) {
          &codes::MISSING_REQUIRED_PROPERTY
        } else {
          base_code
        }
      }
    }
  }

  fn explain_is_missing_property_failure(&self, src: TypeId, dst: TypeId) -> bool {
    let explained = self.relate.explain_assignable(src, dst);
    if explained.result {
      return false;
    }
    fn note_is_absent_property(node: &types_ts_interned::ReasonNode) -> bool {
      // Only fully absent props ("missing property"). Optional-vs-required is
      // "missing required property" in relate and maps to tsc TS2327, not 2741.
      match node.note.as_deref() {
        Some("missing property") => true,
        _ => node.children.iter().any(note_is_absent_property),
      }
    }
    explained
      .reason
      .as_ref()
      .is_some_and(note_is_absent_property)
  }

  /// Count required target properties absent from `src` (tsc
  /// `getUnmatchedProperties` for assignability).
  ///
  /// Returns `None` when either side is not object-like after expansion
  /// (unions, primitives, etc.) so callers can fall back.
  fn unmatched_required_property_count(&self, src: TypeId, dst: TypeId) -> Option<usize> {
    let src = self.expand_for_props(self.expand_ref(src));
    let dst = self.expand_for_props(self.expand_ref(dst));
    let dst_props = self.object_like_properties(dst)?;
    let src_keys = self.object_like_property_keys(src)?;
    let src_has_catchall_indexer = self.object_like_has_indexer(src);
    // Match relate / tsc: static private-identifier fields on constructable
    // types are not unmatched properties (`typeof A = class {}`).
    let skip_private_idents = self.object_like_has_construct_sig(dst);
    let mut missing = 0usize;
    for (key, optional) in dst_props {
      if optional {
        continue;
      }
      if skip_private_idents && key.starts_with('#') {
        continue;
      }
      if src_keys.contains(&key) {
        continue;
      }
      // Approximate indexer coverage: any indexer on `src` can satisfy a
      // missing string/number prop (matches relate's indexer_for_prop fall
      // through for common cases). Without this, indexed types spuriously
      // report every absent named prop as unmatched.
      if src_has_catchall_indexer {
        continue;
      }
      missing += 1;
    }
    Some(missing)
  }

  fn object_like_has_construct_sig(&self, ty: TypeId) -> bool {
    let ty = self.store.canon(ty);
    match self.store.type_kind(ty) {
      TypeKind::Object(obj_id) => !self
        .store
        .shape(self.store.object(obj_id).shape)
        .construct_signatures
        .is_empty(),
      TypeKind::Intersection(members) => members
        .iter()
        .copied()
        .any(|m| self.object_like_has_construct_sig(self.expand_for_props(self.expand_ref(m)))),
      TypeKind::Ref { .. } => {
        let expanded = self.expand_ref(ty);
        expanded != ty && self.object_like_has_construct_sig(expanded)
      }
      _ => false,
    }
  }

  fn object_like_properties(&self, ty: TypeId) -> Option<Vec<(String, bool)>> {
    let ty = self.store.canon(ty);
    match self.store.type_kind(ty) {
      TypeKind::Object(obj_id) => {
        let shape = self.store.shape(self.store.object(obj_id).shape);
        let mut out = Vec::with_capacity(shape.properties.len());
        for prop in shape.properties.iter() {
          let key = match &prop.key {
            PropKey::String(name) | PropKey::Symbol(name) => self.store.name(*name),
            PropKey::Number(n) => n.to_string(),
          };
          out.push((key, prop.data.optional));
        }
        Some(out)
      }
      TypeKind::Intersection(members) => {
        let mut out = Vec::new();
        let mut seen = HashSet::new();
        for member in members.iter().copied() {
          let member = self.expand_for_props(self.expand_ref(member));
          let Some(props) = self.object_like_properties(member) else {
            continue;
          };
          for (key, optional) in props {
            if seen.insert(key.clone()) {
              out.push((key, optional));
            }
          }
        }
        if out.is_empty() && !self.object_like_has_indexer(ty) {
          // Intersection of non-objects — not analyzable as a shape.
          return None;
        }
        Some(out)
      }
      TypeKind::Ref { .. } => {
        let expanded = self.expand_ref(ty);
        if expanded == ty {
          None
        } else {
          self.object_like_properties(expanded)
        }
      }
      // The empty object type has no own properties — an analyzable (empty)
      // shape, so missing-property counting still works
      // (`let foo: Record<"a", any> = {}` → TS2741, not TS2322).
      TypeKind::EmptyObject => Some(Vec::new()),
      _ => None,
    }
  }

  fn object_like_property_keys(&self, ty: TypeId) -> Option<HashSet<String>> {
    let props = self.object_like_properties(ty)?;
    Some(props.into_iter().map(|(k, _)| k).collect())
  }

  fn object_like_has_indexer(&self, ty: TypeId) -> bool {
    let ty = self.store.canon(ty);
    match self.store.type_kind(ty) {
      TypeKind::Object(obj_id) => !self
        .store
        .shape(self.store.object(obj_id).shape)
        .indexers
        .is_empty(),
      TypeKind::Intersection(members) => members
        .iter()
        .copied()
        .any(|m| self.object_like_has_indexer(self.expand_for_props(self.expand_ref(m)))),
      TypeKind::Ref { .. } => {
        let expanded = self.expand_ref(ty);
        expanded != ty && self.object_like_has_indexer(expanded)
      }
      _ => false,
    }
  }

  fn variance_allows_assignability(&self, src: TypeId, dst: TypeId) -> bool {
    let Some(type_param_decls) = self.def_type_param_decls else {
      return true;
    };
    let src = self.store.canon(src);
    let dst = self.store.canon(dst);
    let (def, src_args, dst_args) = match (self.store.type_kind(src), self.store.type_kind(dst)) {
      (
        TypeKind::Ref {
          def: src_def,
          args: src_args,
        },
        TypeKind::Ref {
          def: dst_def,
          args: dst_args,
        },
      ) if src_def == dst_def => (src_def, src_args, dst_args),
      _ => return true,
    };
    let Some(decls) = type_param_decls.get(&def) else {
      return true;
    };
    if !decls.iter().any(|decl| decl.variance.is_some()) {
      return true;
    }
    for (idx, decl) in decls.iter().enumerate() {
      let Some(variance) = decl.variance else {
        continue;
      };
      let Some(src_arg) = src_args.get(idx).copied() else {
        continue;
      };
      let Some(dst_arg) = dst_args.get(idx).copied() else {
        continue;
      };
      match variance {
        TypeParamVariance::Out => {
          if !self.relate.is_assignable(src_arg, dst_arg) {
            return false;
          }
        }
        TypeParamVariance::In => {
          if !self.relate.is_assignable(dst_arg, src_arg) {
            return false;
          }
        }
        TypeParamVariance::InOut => {
          if !self.relate.is_assignable(src_arg, dst_arg)
            || !self.relate.is_assignable(dst_arg, src_arg)
          {
            return false;
          }
        }
      }
    }
    true
  }
}

/// Collect pat-span → HIR type annotation for every var declarator in `body`
/// (including `for` / `for-in` / `for-of` heads).
fn hir_var_type_annotations(body: &Body) -> HashMap<TextRange, TypeExprId> {
  let mut map = HashMap::new();
  let mut insert_decl = |decl: &HirVarDecl| {
    for declarator in decl.declarators.iter() {
      let Some(ann) = declarator.type_annotation else {
        continue;
      };
      let Some(pat) = body.pats.get(declarator.pat.0 as usize) else {
        continue;
      };
      map.insert(pat.span, ann);
    }
  };
  for stmt in body.stmts.iter() {
    match &stmt.kind {
      StmtKind::Var(decl) => insert_decl(decl),
      StmtKind::For {
        init: Some(ForInit::Var(decl)),
        ..
      } => insert_decl(decl),
      StmtKind::ForIn {
        left: ForHead::Var(decl),
        ..
      } => insert_decl(decl),
      _ => {}
    }
  }
  map
}

pub(crate) fn contains_range(outer: TextRange, inner: TextRange) -> bool {
  inner.start >= outer.start && inner.end <= outer.end
}

pub(crate) fn ranges_overlap(a: TextRange, b: TextRange) -> bool {
  a.start < b.end && b.start < a.end
}

pub(crate) fn is_empty_jsx_expr_placeholder(expr: &Node<AstExpr>) -> bool {
  expr.loc.is_empty() && matches!(expr.stx.as_ref(), AstExpr::Id(id) if id.stx.name.is_empty())
}

pub(crate) fn span_for_stmt_list(stmts: &[Node<Stmt>], file: FileId) -> Option<TextRange> {
  let mut start: Option<u32> = None;
  let mut end: Option<u32> = None;
  for stmt in stmts {
    let range = loc_to_range(file, stmt.loc);
    start = Some(start.map_or(range.start, |s| s.min(range.start)));
    end = Some(end.map_or(range.end, |e| e.max(range.end)));
  }
  start.zip(end).map(|(s, e)| TextRange::new(s, e))
}

pub(crate) fn body_range(body: &Body) -> TextRange {
  let mut start = u32::MAX;
  let mut end = 0u32;
  for stmt in body.stmts.iter() {
    start = start.min(stmt.span.start);
    end = end.max(stmt.span.end);
  }
  for expr in body.exprs.iter() {
    start = start.min(expr.span.start);
    end = end.max(expr.span.end);
  }
  for pat in body.pats.iter() {
    start = start.min(pat.span.start);
    end = end.max(pat.span.end);
  }
  if start == u32::MAX {
    match body.kind {
      BodyKind::Class => TextRange::new(0, 0),
      _ => body.span,
    }
  } else {
    TextRange::new(start, end)
  }
}

pub(crate) fn loc_to_range(_file: FileId, loc: Loc) -> TextRange {
  let (range, _) = loc.to_diagnostics_range_with_note();
  TextRange::new(range.start, range.end)
}

pub(crate) fn parse_canonical_index_str(s: &str) -> Option<i64> {
  if s == "0" {
    return Some(0);
  }
  let bytes = s.as_bytes();
  let first = *bytes.first()?;
  if first == b'0' {
    return None;
  }
  if bytes.iter().all(|c| c.is_ascii_digit()) {
    s.parse().ok()
  } else {
    None
  }
}

pub(crate) fn fixed_spread_len(
  store: &TypeStore,
  ty: TypeId,
  expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
  seen: &mut HashSet<TypeId>,
) -> Option<usize> {
  if !seen.insert(ty) {
    return None;
  }
  match store.type_kind(ty) {
    TypeKind::Tuple(elems) => {
      if elems.iter().any(|elem| elem.optional || elem.rest) {
        None
      } else {
        Some(elems.len())
      }
    }
    TypeKind::Ref { def, args } => expander
      .and_then(|expander| expander.expand_ref(store, def, &args))
      .and_then(|expanded| fixed_spread_len(store, expanded, expander, seen)),
    _ => None,
  }
}

pub(crate) fn awaited_type(
  store: &TypeStore,
  ty: TypeId,
  ref_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> TypeId {
  struct AwaitedTypeCalc<'a> {
    store: &'a TypeStore,
    ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
    awaited_stack: HashSet<TypeId>,
    thenable_stack: HashSet<TypeId>,
    then_name: types_ts_interned::NameId,
  }

  impl<'a> AwaitedTypeCalc<'a> {
    const MAX_DEPTH: usize = 32;

    fn awaited(&mut self, ty: TypeId, depth: usize) -> TypeId {
      let ty = self.store.canon(ty);
      if depth > Self::MAX_DEPTH {
        return ty;
      }
      if !self.awaited_stack.insert(ty) {
        return ty;
      }
      let prim = self.store.primitive_ids();
      let out = match self.store.type_kind(ty) {
        TypeKind::Any | TypeKind::Unknown | TypeKind::Never => ty,
        TypeKind::Union(members) => {
          let mapped: Vec<_> = members
            .iter()
            .copied()
            .map(|member| self.awaited(member, depth + 1))
            .collect();
          self.store.union(mapped)
        }
        _ => match self.thenable_resolved(ty, depth + 1) {
          Some(resolved) => self.awaited(resolved, depth + 1),
          None => ty,
        },
      };
      self.awaited_stack.remove(&ty);
      if out == prim.never {
        prim.never
      } else {
        out
      }
    }

    fn thenable_resolved(&mut self, ty: TypeId, depth: usize) -> Option<TypeId> {
      let ty = self.store.canon(ty);
      if depth > Self::MAX_DEPTH {
        return None;
      }
      if !self.thenable_stack.insert(ty) {
        return None;
      }
      let out = match self.store.type_kind(ty) {
        TypeKind::Ref { def, args } => self
          .ref_expander
          .and_then(|expander| expander.expand_ref(self.store, def, &args))
          .and_then(|expanded| self.thenable_resolved(expanded, depth + 1)),
        TypeKind::Object(obj) => self.thenable_from_object(obj, depth + 1),
        TypeKind::Intersection(members) => {
          let mut resolved = Vec::new();
          for member in members.iter().copied() {
            if let Some(inner) = self.thenable_resolved(member, depth + 1) {
              resolved.push(inner);
            }
          }
          match resolved.len() {
            0 => None,
            1 => resolved.into_iter().next(),
            _ => Some(self.store.intersection(resolved)),
          }
        }
        _ => None,
      };
      self.thenable_stack.remove(&ty);
      out
    }

    fn thenable_from_object(
      &mut self,
      obj: types_ts_interned::ObjectId,
      depth: usize,
    ) -> Option<TypeId> {
      let shape = self.store.shape(self.store.object(obj).shape);
      let then_prop = shape.properties.iter().find(|prop| match prop.key {
        PropKey::String(name) => name == self.then_name,
        _ => false,
      })?;
      let then_ty = then_prop.data.ty;
      let mut then_sigs = Vec::new();
      self.collect_call_signatures(then_ty, &mut then_sigs, &mut HashSet::new(), depth + 1);
      if then_sigs.is_empty() {
        return None;
      }
      then_sigs.sort();
      then_sigs.dedup();

      let prim = self.store.primitive_ids();
      let mut resolved = Vec::new();
      for sig_id in then_sigs {
        let sig = self.store.signature(sig_id);
        let Some(onfulfilled) = sig.params.first() else {
          continue;
        };
        let mut cb_sigs = Vec::new();
        self.collect_call_signatures(onfulfilled.ty, &mut cb_sigs, &mut HashSet::new(), depth + 1);
        if cb_sigs.is_empty() {
          continue;
        }
        cb_sigs.sort();
        cb_sigs.dedup();
        let mut cb_values = Vec::new();
        for cb_sig_id in cb_sigs {
          let cb_sig = self.store.signature(cb_sig_id);
          if let Some(value) = cb_sig.params.first() {
            cb_values.push(value.ty);
          }
        }
        let value_ty = match cb_values.len() {
          0 => prim.unknown,
          1 => cb_values[0],
          _ => self.store.union(cb_values),
        };
        resolved.push(value_ty);
      }
      match resolved.len() {
        0 => None,
        1 => resolved.into_iter().next(),
        _ => Some(self.store.union(resolved)),
      }
    }

    fn collect_call_signatures(
      &self,
      ty: TypeId,
      out: &mut Vec<types_ts_interned::SignatureId>,
      seen: &mut HashSet<TypeId>,
      depth: usize,
    ) {
      let ty = self.store.canon(ty);
      if depth > Self::MAX_DEPTH {
        return;
      }
      if !seen.insert(ty) {
        return;
      }
      match self.store.type_kind(ty) {
        TypeKind::Callable { overloads } => {
          out.extend(overloads.iter().copied());
        }
        TypeKind::Object(obj) => {
          let shape = self.store.shape(self.store.object(obj).shape);
          out.extend(shape.call_signatures.iter().copied());
        }
        TypeKind::Union(members) | TypeKind::Intersection(members) => {
          for member in members.iter().copied() {
            self.collect_call_signatures(member, out, seen, depth + 1);
          }
        }
        TypeKind::Ref { def, args } => {
          if let Some(expander) = self.ref_expander {
            if let Some(expanded) = expander.expand_ref(self.store, def, &args) {
              self.collect_call_signatures(expanded, out, seen, depth + 1);
            }
          }
        }
        _ => {}
      }
    }
  }

  let then_name = store.intern_name("then");
  let mut calc = AwaitedTypeCalc {
    store,
    ref_expander,
    awaited_stack: HashSet::new(),
    thenable_stack: HashSet::new(),
    then_name,
  };
  calc.awaited(ty, 0)
}

/// Flow-sensitive body checker built directly on `hir-js` bodies. This is a
/// lightweight, statement-level analysis that uses a CFG plus a simple lattice
/// of variable environments to drive narrowing.
/// Build `#priv` → class-type map for `#priv in x` CFA (tsc
/// `narrowTypeByPrivateIdentifierInInExpression`).
///
/// `resolve_class_types(class_index) -> (instance, static/ctor)`.
pub fn build_private_in_targets(
  ast_index: &AstIndex<'_>,
  body_span: TextRange,
  mut resolve_class_types: impl FnMut(usize) -> Option<(TypeId, TypeId)>,
) -> HashMap<String, TypeId> {
  let enclosing = enclosing_class_index_for_span(ast_index, body_span);
  let Some(start) = enclosing else {
    return HashMap::new();
  };
  let mut targets = HashMap::new();
  // Walk lexical chain so nested classes see outer privates (and own ones win).
  let mut current = Some(start);
  let mut visited = HashSet::new();
  while let Some(idx) = current.take() {
    if !visited.insert(idx) {
      break;
    }
    let Some((instance_ty, static_ty)) = resolve_class_types(idx) else {
      current = ast_index
        .classes
        .get(idx)
        .and_then(|c| c.parent_class_index);
      continue;
    };
    for prop in ast_index.class_private_names(idx) {
      // Inner declarations shadow outer same-spelling privates.
      if targets.contains_key(&prop) {
        continue;
      }
      let ty = if ast_index.class_private_is_static(idx, &prop) {
        static_ty
      } else {
        instance_ty
      };
      targets.insert(prop, ty);
    }
    current = ast_index
      .classes
      .get(idx)
      .and_then(|c| c.parent_class_index);
  }
  targets
}

fn enclosing_class_index_for_span(ast_index: &AstIndex<'_>, body_span: TextRange) -> Option<usize> {
  let mut best: Option<(u32, usize)> = None;
  let consider = |best: &mut Option<(u32, usize)>, span: TextRange, idx: usize| {
    if !(span.start <= body_span.start && span.end >= body_span.end) {
      return;
    }
    let len = span.end.saturating_sub(span.start);
    let replace = match *best {
      Some((existing_len, _)) => len < existing_len,
      None => true,
    };
    if replace {
      *best = Some((len, idx));
    }
  };
  for (span, info) in ast_index.class_member_func_by_span.iter() {
    consider(&mut best, *span, info.class_index);
  }
  for (span, info) in ast_index.class_field_initializers.iter() {
    consider(&mut best, *span, info.class_index);
  }
  for block in ast_index.class_static_blocks.iter() {
    consider(&mut best, block.span, block.class_index);
  }
  // Class expression / declaration spans as a last resort.
  for (idx, class) in ast_index.classes.iter().enumerate() {
    consider(&mut best, class.span, idx);
  }
  best.map(|(_, idx)| idx)
}

pub fn check_body_with_env(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  _source: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
  relate: RelateCtx,
  ref_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
) -> BodyCheckResult {
  check_body_with_env_with_bindings(
    body_id,
    body,
    names,
    file,
    _source,
    store,
    initial,
    None,
    relate,
    ref_expander,
    None,
    None,
    HashMap::new(),
    None,
    false,
  )
}

pub fn check_body_with_env_with_bindings(
  body_id: BodyId,
  body: &Body,
  names: &NameInterner,
  file: FileId,
  _source: &str,
  store: Arc<TypeStore>,
  initial: &HashMap<NameId, TypeId>,
  flow_bindings: Option<&FlowBindings>,
  relate: RelateCtx,
  ref_expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
  type_arenas: Option<&hir_js::TypeArenas>,
  type_aliases: Option<&DaTypeAliasMap<'_>>,
  private_in_targets: HashMap<String, TypeId>,
  type_resolver: Option<Arc<dyn TypeResolver>>,
  no_implicit_any: bool,
) -> BodyCheckResult {
  let mut checker = FlowBodyChecker::new(
    body_id,
    body,
    names,
    Arc::clone(&store),
    file,
    initial,
    flow_bindings,
    relate,
    ref_expander,
    type_arenas,
    type_aliases,
    private_in_targets,
    type_resolver,
    no_implicit_any,
  );
  checker.run();
  codes::normalize_diagnostics(&mut checker.diagnostics);
  checker.into_result()
}
