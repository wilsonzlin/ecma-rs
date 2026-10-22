use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use diagnostics::{Diagnostic, FileId, TextRange};
use hir_js::{
  ArrayElement, Body, DefKind, DefTypeInfo, ExprId, ExprKind, ForHead, ForInit, LocalKind,
  LowerResult, NameId, NameInterner, ObjectKey, ObjectProperty, PatId, PatKind, StmtId, StmtKind,
  TypeArenas, TypeExprId, TypeParamId, VarDecl as HirVarDecl,
};
use semantic_js::ts::SymbolId;
use types_ts_interned::{Indexer, PropKey, RelateCtx, Shape, TypeId, TypeKind, TypeStore};

use super::super::super::flow::{BindingKey, PathSegment};
use super::super::super::flow_bindings::{FlowBindingId, FlowBindings};
use super::super::super::instantiate::InstantiationCache;
use crate::BodyId;

/// Body of a file-level `type` alias, used to expand `TypeRef` annotations for
/// TS2454 DA exemptions (tsc resolves the declared type, not just the AST shape).
///
/// Supports generic aliases (`type Id<T> = T`) via [`type_params`] and cross-file
/// imports (local [`NameId`] → foreign arenas) via [`DaTypeAliasMap::link_import`].
#[derive(Clone, Copy)]
pub struct DaAliasBody<'a> {
  pub file: FileId,
  pub arenas: &'a TypeArenas,
  pub type_expr: TypeExprId,
  pub type_params: &'a [TypeParamId],
  pub names: &'a NameInterner,
}

/// Type-argument / default substitution target while expanding a generic alias
/// for DA exemption.
#[derive(Clone, Copy)]
pub(crate) struct DaSubstTarget<'a> {
  pub arenas: &'a TypeArenas,
  pub expr: TypeExprId,
  pub file: FileId,
  pub names: &'a NameInterner,
}

/// Name → alias-body map for DA exemption expansion.
///
/// - [`by_name`]: annotation-site local [`NameId`] (including import locals)
/// - [`by_qualified`]: defining-file aliases keyed by `(file, name)` for nested
///   expansion inside alias bodies (`type V<T> = U<T>`)
/// - [`nullary_exempt`]: local [`NameId`] → whether a *nullary* `TypeRef` to that
///   name is DA-exempt (used for re-exports that expose a resolved `type_id`
///   but no local `TypeAlias` def body)
#[derive(Default, Clone)]
pub struct DaTypeAliasMap<'a> {
  pub by_name: HashMap<NameId, DaAliasBody<'a>>,
  pub by_qualified: HashMap<(u32, String), DaAliasBody<'a>>,
  pub nullary_exempt: HashMap<NameId, bool>,
}

impl<'a> DaTypeAliasMap<'a> {
  pub fn from_lowered(lowered: &'a LowerResult) -> Self {
    let mut map = Self::default();
    map.register_file_aliases(lowered);
    // Local aliases are also addressable by their defining-file NameId.
    for def in lowered.defs.iter() {
      if def.path.kind != DefKind::TypeAlias {
        continue;
      }
      let Some(name) = lowered.names.resolve(def.name) else {
        continue;
      };
      if let Some(body) = map
        .by_qualified
        .get(&(lowered.hir.file.0, name.to_string()))
        .copied()
      {
        map.by_name.insert(def.name, body);
      }
    }
    map
  }

  /// Register every `type` alias in `lowered` under `(file, name)` for nested
  /// expansion. Does not add local [`by_name`] entries (callers link imports /
  /// locals explicitly via [`from_lowered`] / [`link_import`]).
  pub fn register_file_aliases(&mut self, lowered: &'a LowerResult) {
    let file = lowered.hir.file;
    for def in lowered.defs.iter() {
      if def.path.kind != DefKind::TypeAlias {
        continue;
      }
      let Some(DefTypeInfo::TypeAlias {
        type_expr,
        type_params,
      }) = def.type_info.as_ref()
      else {
        continue;
      };
      let Some(arenas) = lowered.type_arenas(def.id) else {
        continue;
      };
      let Some(name) = lowered.names.resolve(def.name) else {
        continue;
      };
      let body = DaAliasBody {
        file,
        arenas,
        type_expr: *type_expr,
        type_params: type_params.as_slice(),
        names: &lowered.names,
      };
      self.by_qualified.insert((file.0, name.to_string()), body);
    }
  }

  /// Map a local import binding name to a type alias exported (by `export_name`)
  /// from `foreign`.
  pub fn link_import(
    &mut self,
    local: NameId,
    export_name: &str,
    foreign: &'a LowerResult,
  ) -> bool {
    self.register_file_aliases(foreign);
    let Some(body) = self
      .by_qualified
      .get(&(foreign.hir.file.0, export_name.to_string()))
      .copied()
    else {
      return false;
    };
    self.link_alias_body(local, body);
    true
  }

  /// Bind a local [`NameId`] (import or alias) to an already-resolved alias body.
  pub fn link_alias_body(&mut self, local: NameId, body: DaAliasBody<'a>) {
    self.by_name.insert(local, body);
  }

  /// Record whether a nullary `TypeRef` to `local` is DA-exempt (re-export
  /// `type_id` fallback when no alias body is available).
  pub fn link_nullary_exempt(&mut self, local: NameId, exempt: bool) {
    self.nullary_exempt.insert(local, exempt);
  }
}

/// Whether an interned type is DA-exempt per tsc `assumeInitialized` /
/// `containsUndefinedType` (any / unknown / void, or a union including
/// `undefined`). Does not expand `Ref`s — callers should pass resolved types.
pub fn type_id_is_da_exempt(store: &TypeStore, ty: TypeId) -> bool {
  fn inner(store: &TypeStore, ty: TypeId, seen: &mut HashSet<TypeId>) -> bool {
    let ty = store.canon(ty);
    if !seen.insert(ty) {
      return false;
    }
    match store.type_kind(ty) {
      types_ts_interned::TypeKind::Any
      | types_ts_interned::TypeKind::Unknown
      | types_ts_interned::TypeKind::Void
      | types_ts_interned::TypeKind::Undefined => true,
      types_ts_interned::TypeKind::Union(members) => members.iter().any(|m| inner(store, *m, seen)),
      _ => false,
    }
  }
  let mut seen = HashSet::new();
  inner(store, ty, &mut seen)
}

pub(crate) enum Reference {
  Ident {
    name: FlowBindingId,
    ty: TypeId,
  },
  Member {
    base: FlowBindingId,
    prop: String,
    base_ty: TypeId,
    prop_ty: TypeId,
  },
}

impl Reference {
  pub(crate) fn target(&self) -> FlowBindingId {
    match self {
      Reference::Ident { name, .. } => *name,
      Reference::Member { base, .. } => *base,
    }
  }

  pub(crate) fn target_ty(&self) -> TypeId {
    match self {
      Reference::Ident { ty, .. } => *ty,
      Reference::Member { base_ty, .. } => *base_ty,
    }
  }

  pub(crate) fn value_ty(&self) -> TypeId {
    match self {
      Reference::Ident { ty, .. } => *ty,
      Reference::Member { prop_ty, .. } => *prop_ty,
    }
  }
}

pub(crate) struct FlowBodyChecker<'a> {
  pub(crate) body_id: BodyId,
  pub(crate) body: &'a Body,
  pub(crate) names: &'a NameInterner,
  pub(crate) store: Arc<TypeStore>,
  pub(crate) file: FileId,
  pub(crate) relate: RelateCtx<'a>,
  pub(crate) instantiation_cache: InstantiationCache,
  pub(crate) expr_types: Vec<TypeId>,
  pub(crate) optional_chain_exec_types: Vec<Option<TypeId>>,
  pub(crate) pat_types: Vec<TypeId>,
  pub(crate) expr_spans: Vec<TextRange>,
  pub(crate) pat_spans: Vec<TextRange>,
  pub(crate) diagnostics: Vec<Diagnostic>,
  pub(crate) reported_unassigned: HashSet<ExprId>,
  /// Bindings whose declared type is DA-exempt (`any` / `unknown` / `void` /
  /// includes `undefined`), matching tsc's `assumeInitialized` /
  /// `containsUndefinedType` gates for TS2454.
  pub(crate) da_exempt_bindings: HashSet<BindingKey>,
  /// Type arenas for `body.owner` (var/param annotations). Optional so unit
  /// tests that don't care about DA exemptions can omit them.
  pub(crate) type_arenas: Option<&'a TypeArenas>,
  /// File-level type aliases for expanding `TypeRef` DA exemptions.
  pub(crate) type_aliases: Option<&'a DaTypeAliasMap<'a>>,
  pub(crate) return_types: Vec<TypeId>,
  pub(crate) return_indices: HashMap<StmtId, usize>,
  pub(crate) widen_object_literals: bool,
  pub(crate) ref_expander: Option<&'a dyn types_ts_interned::RelateTypeExpander>,
  /// Resolves global interfaces (`String`, `Number`, …) for primitive property
  /// access. Optional so unit tests can omit libs.
  pub(crate) type_resolver: Option<Arc<dyn crate::check::type_expr::TypeResolver>>,
  pub(crate) initial: HashMap<FlowBindingId, TypeId>,
  pub(crate) param_bindings: HashSet<BindingKey>,
  pub(crate) bindings: BindingTable,
  /// Worklist iterations consumed by [`FlowBodyChecker::run`].
  pub(crate) flow_steps: usize,
  /// Cap on worklist iterations (pathology: non-stabilizing merges).
  pub(crate) flow_step_limit: usize,
  pub(crate) budget_diagnostic_emitted: bool,
  pub(crate) types_at_start: usize,
  pub(crate) max_type_growth: usize,
  /// Lexically visible `#priv` → class type for `#priv in x` CFA
  /// (instance type, or constructor type for static privates).
  pub(crate) private_in_targets: HashMap<String, TypeId>,
  /// `--noImplicitAny`: empty `[]` bindings use `any[]` (tsc autoArrayType).
  pub(crate) no_implicit_any: bool,
}

impl FlowBodyChecker<'_> {
  /// Generous CFA worklist / expression-visit budget; above normal bodies,
  /// below the `parserRealSource12` non-stabilizing-merge pathology.
  pub(crate) const DEFAULT_FLOW_STEP_LIMIT: usize = 25_000;
  /// Max new interned types a single flow pass may add (shared store growth).
  pub(crate) const DEFAULT_MAX_TYPE_GROWTH: usize = 5_000;
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(crate) enum BindingMode {
  Declare,
  Assign,
}

pub(crate) enum SwitchDiscriminant {
  Ident {
    name: FlowBindingId,
    ty: TypeId,
  },
  Member {
    name: FlowBindingId,
    path: Vec<PathSegment>,
    optional_bases: Vec<Vec<PathSegment>>,
    ty: TypeId,
  },
  Typeof {
    name: FlowBindingId,
    ty: TypeId,
  },
}

impl SwitchDiscriminant {
  pub(crate) fn ty(&self) -> TypeId {
    match self {
      SwitchDiscriminant::Ident { ty, .. }
      | SwitchDiscriminant::Member { ty, .. }
      | SwitchDiscriminant::Typeof { ty, .. } => *ty,
    }
  }

  pub(crate) fn name(&self) -> FlowBindingId {
    match self {
      SwitchDiscriminant::Ident { name, .. }
      | SwitchDiscriminant::Member { name, .. }
      | SwitchDiscriminant::Typeof { name, .. } => *name,
    }
  }
}

#[derive(Default)]
pub(crate) struct BindingTable {
  pub(crate) expr_bindings: HashMap<ExprId, BindingKey>,
  pub(crate) pat_bindings: HashMap<PatId, BindingKey>,
  pub(crate) param_bindings: HashSet<BindingKey>,
  pub(crate) flow_ids: HashMap<BindingKey, FlowBindingId>,
  pub(crate) flow_to_binding: HashMap<FlowBindingId, BindingKey>,
  /// Body-root-scope bindings by name (deterministic: one slot per name).
  /// Used to seed caller-provided declared types onto the *local* flow
  /// binding of the top-level body (module-level `declare const` is a local
  /// of that body, not an external) without ever matching a shadowed
  /// block-scoped local of the same name.
  pub(crate) root_bindings: HashMap<NameId, BindingKey>,
  pub(crate) next_flow_id: u64,
  /// Ident exprs that reference a block-scoped binding in its TDZ
  /// (own initializer or for-in/of RHS) — emit TS2448.
  pub(crate) used_before_declaration: HashSet<ExprId>,
  /// Subset of [`used_before_declaration`] on for-in/of RHS: tsc reports
  /// TS2448 only there (not also TS2454), matching `for-of55.ts`.
  pub(crate) suppress_use_before_assignment: HashSet<ExprId>,
}

impl BindingTable {
  pub(crate) fn binding_key_for_expr(&self, expr: ExprId) -> Option<BindingKey> {
    self.expr_bindings.get(&expr).copied()
  }

  pub(crate) fn binding_key_for_pat(&self, pat: PatId) -> Option<BindingKey> {
    self.pat_bindings.get(&pat).copied()
  }

  pub(crate) fn binding_for_expr(&self, expr: ExprId) -> Option<FlowBindingId> {
    self.flow_binding_for_expr(expr)
  }

  pub(crate) fn binding_for_pat(&self, pat: PatId) -> Option<FlowBindingId> {
    self.flow_binding_for_pat(pat)
  }

  pub(crate) fn set_flow_binding(
    &mut self,
    binding: BindingKey,
    id: FlowBindingId,
  ) -> FlowBindingId {
    if let Some(existing) = self.flow_ids.get(&binding) {
      if *existing == id {
        return id;
      }
      self.flow_to_binding.remove(existing);
    }
    if let Some(previous_binding) = self.flow_to_binding.insert(id, binding) {
      if previous_binding != binding {
        self.flow_ids.remove(&previous_binding);
      }
    }
    self.flow_ids.insert(binding, id);
    id
  }

  pub(crate) fn ensure_flow_binding(&mut self, binding: BindingKey) -> FlowBindingId {
    if let Some(existing) = self.flow_ids.get(&binding) {
      return *existing;
    }
    let mut id = SymbolId(self.next_flow_id);
    self.next_flow_id += 1;
    while self.flow_to_binding.contains_key(&id) {
      id = SymbolId(self.next_flow_id);
      self.next_flow_id += 1;
    }
    self.set_flow_binding(binding, id)
  }

  pub(crate) fn flow_binding_for_key(&self, binding: BindingKey) -> Option<FlowBindingId> {
    self.flow_ids.get(&binding).copied()
  }

  pub(crate) fn flow_binding_for_expr(&self, expr: ExprId) -> Option<FlowBindingId> {
    self
      .expr_bindings
      .get(&expr)
      .and_then(|b| self.flow_ids.get(b))
      .copied()
  }

  pub(crate) fn flow_binding_for_pat(&self, pat: PatId) -> Option<FlowBindingId> {
    self
      .pat_bindings
      .get(&pat)
      .and_then(|b| self.flow_ids.get(b))
      .copied()
  }

  pub(crate) fn binding_for_flow(&self, id: FlowBindingId) -> Option<BindingKey> {
    self.flow_to_binding.get(&id).copied()
  }

  pub(crate) fn flow_binding_for_external(&mut self, name: NameId) -> FlowBindingId {
    self.ensure_flow_binding(BindingKey::External(name))
  }
}

pub(crate) struct BindingCollector<'a> {
  pub(crate) body: &'a Body,
  pub(crate) scopes: Vec<HashMap<NameId, BindingKey>>,
  pub(crate) table: BindingTable,
  pub(crate) visited_stmts: HashSet<StmtId>,
  pub(crate) flow_bindings: Option<&'a FlowBindings>,
  /// Pats of the active for-in/of head while visiting its RHS.
  pub(crate) for_head_pats: HashSet<PatId>,
  /// Pats of the active var declarator while visiting its initializer.
  pub(crate) init_pats: HashSet<PatId>,
  /// >0 while visiting a computed key of a *method* member: tsc does not run
  /// definite-assignment analysis on method name expressions (`{ [s]() {} }`,
  /// `class C { [s]() {} }`), only on plain-property keys (`{ [s]: 1 }`).
  pub(crate) method_key_depth: u32,
}

impl<'a> BindingCollector<'a> {
  pub(crate) fn collect(body: &'a Body, flow_bindings: Option<&'a FlowBindings>) -> BindingTable {
    let mut collector = BindingCollector {
      body,
      scopes: vec![HashMap::new()],
      table: BindingTable::default(),
      visited_stmts: HashSet::new(),
      flow_bindings,
      for_head_pats: HashSet::new(),
      init_pats: HashSet::new(),
      method_key_depth: 0,
    };
    collector.collect_params();
    let roots = if !body.root_stmts.is_empty() {
      body.root_stmts.clone()
    } else {
      (0..body.stmts.len() as u32).map(StmtId).collect()
    };
    for stmt in roots {
      collector.visit_stmt(stmt);
    }
    // Snapshot the body-root scope for deterministic name → binding lookup.
    if let Some(root) = collector.scopes.first() {
      collector.table.root_bindings = root.clone();
    }
    collector.table
  }

  fn collect_pat_ids(&self, pat_id: PatId, out: &mut HashSet<PatId>) {
    out.insert(pat_id);
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(_) | PatKind::AssignTarget(_) => {}
      PatKind::Assign { target, .. } => self.collect_pat_ids(*target, out),
      PatKind::Rest(inner) => self.collect_pat_ids(**inner, out),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.collect_pat_ids(elem.pat, out);
        }
        if let Some(rest) = arr.rest {
          self.collect_pat_ids(rest, out);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.collect_pat_ids(prop.value, out);
        }
        if let Some(rest) = obj.rest {
          self.collect_pat_ids(rest, out);
        }
      }
    }
  }

  fn note_tdz_use(&mut self, expr_id: ExprId, binding: BindingKey, for_head_rhs: bool) {
    let BindingKey::Local { pat, .. } = binding else {
      return;
    };
    let in_tdz = if for_head_rhs {
      self.for_head_pats.contains(&pat)
    } else {
      self.init_pats.contains(&pat)
    };
    if !in_tdz {
      return;
    }
    self.table.used_before_declaration.insert(expr_id);
    if for_head_rhs {
      self.table.suppress_use_before_assignment.insert(expr_id);
    }
  }

  pub(crate) fn collect_params(&mut self) {
    // Prefer Body.locals / LocalId as the source of truth for param bindings.
    for (_local_id, local) in self.body.locals_with_kind(LocalKind::Param) {
      let Some(pat_id) = local.pat else {
        continue;
      };
      self.insert_binding(
        local.name,
        pat_id,
        true,
        false,
        self
          .flow_bindings
          .and_then(|bindings| bindings.binding_for_pat(pat_id)),
      );
    }
    // Walk param patterns for nested default/computed exprs; Ident bindings
    // reuse the LocalId-seeded entries above.
    if let Some(function) = self.body.function.as_ref() {
      for param in function.params.iter() {
        self.declare_pat(param.pat, true, false);
        if let Some(default) = param.default {
          self.visit_expr(default);
        }
      }
    }
  }

  pub(crate) fn insert_binding(
    &mut self,
    name: NameId,
    pat: PatId,
    is_param: bool,
    hoist: bool,
    flow_binding: Option<FlowBindingId>,
  ) {
    let target_scope = if hoist {
      self
        .scopes
        .first_mut()
        .expect("binding collector always has a root scope")
    } else {
      self
        .scopes
        .last_mut()
        .expect("binding collector always has a scope")
    };
    // Hoisted `var` declarations share the function-scoped binding with
    // parameters and other `var`s. Reuse the existing binding if present so
    // flow facts accumulate on the same symbol.
    if let Some(existing) = target_scope.get(&name).copied() {
      self.table.pat_bindings.insert(pat, existing);
      if is_param {
        self.table.param_bindings.insert(existing);
      }
      if let Some(id) = flow_binding {
        self.table.set_flow_binding(existing, id);
      } else {
        self.table.ensure_flow_binding(existing);
      }
      return;
    }

    let key = BindingKey::Local { pat, name };
    self.table.pat_bindings.insert(pat, key);
    if is_param {
      self.table.param_bindings.insert(key);
    }
    if let Some(id) = flow_binding {
      self.table.set_flow_binding(key, id);
    } else {
      self.table.ensure_flow_binding(key);
    }
    target_scope.insert(name, key);
  }

  pub(crate) fn declare_pat(&mut self, pat_id: PatId, is_param: bool, hoist: bool) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => self.insert_binding(
        *name,
        pat_id,
        is_param,
        hoist,
        self
          .flow_bindings
          .and_then(|bindings| bindings.binding_for_pat(pat_id)),
      ),
      PatKind::Assign {
        target,
        default_value,
      } => {
        self.declare_pat(*target, is_param, hoist);
        self.visit_expr(*default_value);
      }
      PatKind::Rest(inner) => self.declare_pat(**inner, is_param, hoist),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.declare_pat(elem.pat, is_param, hoist);
          if let Some(default) = elem.default_value {
            self.visit_expr(default);
          }
          // Destructuring assigns left-to-right: once an element completes,
          // its names leave the TDZ for later siblings (`[a1, a2 = a1]` is
          // legal; `[a2 = a1, a1]` is not).
          let mut done = HashSet::new();
          self.collect_pat_ids(elem.pat, &mut done);
          for id in done {
            self.init_pats.remove(&id);
          }
        }
        if let Some(rest) = arr.rest {
          self.declare_pat(rest, is_param, hoist);
          let mut done = HashSet::new();
          self.collect_pat_ids(rest, &mut done);
          for id in done {
            self.init_pats.remove(&id);
          }
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.declare_pat(prop.value, is_param, hoist);
          if let Some(default) = prop.default_value {
            self.visit_expr(default);
          }
          if let ObjectKey::Computed(expr) = &prop.key {
            self.visit_expr(*expr);
          }
          let mut done = HashSet::new();
          self.collect_pat_ids(prop.value, &mut done);
          for id in done {
            self.init_pats.remove(&id);
          }
        }
        if let Some(rest) = obj.rest {
          self.declare_pat(rest, is_param, hoist);
          let mut done = HashSet::new();
          self.collect_pat_ids(rest, &mut done);
          for id in done {
            self.init_pats.remove(&id);
          }
        }
      }
      PatKind::AssignTarget(expr) => self.visit_expr(*expr),
    }
  }

  pub(crate) fn resolve_binding(&mut self, name: NameId) -> BindingKey {
    for scope in self.scopes.iter().rev() {
      if let Some(binding) = scope.get(&name) {
        let binding = *binding;
        self.table.ensure_flow_binding(binding);
        return binding;
      }
    }
    let binding = BindingKey::External(name);
    self.table.ensure_flow_binding(binding);
    binding
  }

  pub(crate) fn visit_stmt(&mut self, stmt_id: StmtId) {
    if !self.visited_stmts.insert(stmt_id) {
      return;
    }
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    match &stmt.kind {
      StmtKind::Expr(expr) => self.visit_expr(*expr),
      StmtKind::Decl(_) => {}
      StmtKind::Return(expr) => {
        if let Some(expr) = expr {
          self.visit_expr(*expr);
        }
      }
      StmtKind::Block(stmts) => {
        self.push_scope();
        for stmt in stmts.iter() {
          self.visit_stmt(*stmt);
        }
        self.pop_scope();
      }
      StmtKind::If {
        test,
        consequent,
        alternate,
      } => {
        self.visit_expr(*test);
        self.push_scope();
        self.visit_stmt(*consequent);
        self.pop_scope();
        if let Some(alt) = alternate {
          self.push_scope();
          self.visit_stmt(*alt);
          self.pop_scope();
        }
      }
      StmtKind::While { test, body } => {
        self.visit_expr(*test);
        self.push_scope();
        self.visit_stmt(*body);
        self.pop_scope();
      }
      StmtKind::DoWhile { test, body } => {
        self.push_scope();
        self.visit_stmt(*body);
        self.pop_scope();
        self.visit_expr(*test);
      }
      StmtKind::For {
        init,
        test,
        update,
        body,
      } => {
        self.push_scope();
        if let Some(init) = init {
          match init {
            ForInit::Expr(expr) => self.visit_expr(*expr),
            ForInit::Var(var) => self.visit_var_decl(var),
          }
        }
        if let Some(test) = test {
          self.visit_expr(*test);
        }
        if let Some(update) = update {
          self.visit_expr(*update);
        }
        self.visit_stmt(*body);
        self.pop_scope();
      }
      StmtKind::ForIn {
        left, right, body, ..
      } => {
        self.push_scope();
        // Declare the head first so the RHS resolves to the inner binding
        // (TDZ), matching tsc / ES — then mark those uses as TS2448.
        let saved_head = std::mem::take(&mut self.for_head_pats);
        let mut head_pats = HashSet::new();
        match left {
          ForHead::Pat(pat) => {
            self.declare_pat(*pat, false, false);
            self.collect_pat_ids(*pat, &mut head_pats);
          }
          ForHead::Var(var) => {
            // Declare without walking inits (for-in/of heads have none); collect
            // pats for TDZ, then visit RHS under for_head_pats.
            let hoist = matches!(var.kind, hir_js::VarDeclKind::Var);
            for declarator in var.declarators.iter() {
              self.declare_pat(declarator.pat, false, hoist);
              self.collect_pat_ids(declarator.pat, &mut head_pats);
            }
          }
        }
        self.for_head_pats = head_pats;
        self.visit_expr(*right);
        self.for_head_pats = saved_head;
        self.visit_stmt(*body);
        self.pop_scope();
      }
      StmtKind::Switch {
        discriminant,
        cases,
        ..
      } => {
        self.visit_expr(*discriminant);
        self.push_scope();
        for case in cases.iter() {
          if let Some(test) = case.test {
            self.visit_expr(test);
          }
          for stmt in case.consequent.iter() {
            self.visit_stmt(*stmt);
          }
        }
        self.pop_scope();
      }
      StmtKind::Try {
        block,
        catch,
        finally_block,
      } => {
        self.push_scope();
        self.visit_stmt(*block);
        self.pop_scope();
        if let Some(catch) = catch {
          self.push_scope();
          if let Some(param) = catch.param {
            self.declare_pat(param, false, false);
          }
          self.visit_stmt(catch.body);
          self.pop_scope();
        }
        if let Some(finally_block) = finally_block {
          self.push_scope();
          self.visit_stmt(*finally_block);
          self.pop_scope();
        }
      }
      StmtKind::Throw(expr) => self.visit_expr(*expr),
      StmtKind::Break(_) | StmtKind::Continue(_) | StmtKind::Debugger | StmtKind::Empty => {}
      StmtKind::Var(decl) => self.visit_var_decl(decl),
      StmtKind::Labeled { body, .. } => self.visit_stmt(*body),
      StmtKind::With { object, body } => {
        self.visit_expr(*object);
        self.push_scope();
        self.visit_stmt(*body);
        self.pop_scope();
      }
    }
  }

  pub(crate) fn visit_var_decl(&mut self, decl: &HirVarDecl) {
    let hoist = matches!(decl.kind, hir_js::VarDeclKind::Var);
    for declarator in decl.declarators.iter() {
      // TDZ tracking for one declarator. Pattern defaults evaluate
      // left-to-right as destructuring proceeds, so a default may reference
      // earlier siblings (`{ a1, a2 = a1 }`) but not itself or later ones
      // (`{ a2 = a1, a1 }`, `{ a: x = x }`): `init_pats` starts as the full
      // declarator set and `declare_pat` shrinks it as sub-patterns complete.
      // The outer initializer evaluates before any binding, so it always sees
      // the full set (`const { a } = a` is a TDZ use).
      let saved = std::mem::take(&mut self.init_pats);
      let mut pats = HashSet::new();
      self.collect_pat_ids(declarator.pat, &mut pats);
      self.init_pats = pats.clone();
      self.declare_pat(declarator.pat, false, hoist);
      if let Some(init) = declarator.init {
        self.init_pats = pats;
        self.visit_expr(init);
      }
      self.init_pats = saved;
    }
  }

  pub(crate) fn visit_expr(&mut self, expr_id: ExprId) {
    let expr = &self.body.exprs[expr_id.0 as usize];
    match &expr.kind {
      ExprKind::Ident(name) => {
        let binding = self.resolve_binding(*name);
        self.table.expr_bindings.insert(expr_id, binding);
        if self.method_key_depth > 0 {
          self.table.suppress_use_before_assignment.insert(expr_id);
        }
        if !self.for_head_pats.is_empty() {
          self.note_tdz_use(expr_id, binding, true);
        } else if !self.init_pats.is_empty() {
          self.note_tdz_use(expr_id, binding, false);
        }
        if let Some(id) = self
          .flow_bindings
          .and_then(|bindings| bindings.binding_for_expr(expr_id))
        {
          self.table.set_flow_binding(binding, id);
        }
      }
      ExprKind::Unary { expr, .. } => self.visit_expr(*expr),
      ExprKind::Update { expr, .. } => self.visit_expr(*expr),
      ExprKind::Binary { left, right, .. } => {
        self.visit_expr(*left);
        self.visit_expr(*right);
      }
      ExprKind::Assignment { target, value, .. } => {
        self.visit_pat(*target);
        self.visit_expr(*value);
      }
      ExprKind::Call(call) => {
        self.visit_expr(call.callee);
        for arg in call.args.iter() {
          self.visit_expr(arg.expr);
        }
      }
      ExprKind::Member(mem) => {
        self.visit_expr(mem.object);
        if let ObjectKey::Computed(expr) = &mem.property {
          self.visit_expr(*expr);
        }
      }
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        self.visit_expr(*test);
        self.visit_expr(*consequent);
        self.visit_expr(*alternate);
      }
      ExprKind::Array(arr) => {
        for elem in arr.elements.iter() {
          match elem {
            ArrayElement::Expr(expr) | ArrayElement::Spread(expr) => self.visit_expr(*expr),
            ArrayElement::Empty => {}
          }
        }
      }
      ExprKind::Object(obj) => {
        for prop in obj.properties.iter() {
          match prop {
            ObjectProperty::KeyValue { key, value, .. } => {
              self.visit_expr(*value);
              if let ObjectKey::Computed(expr) = key {
                // tsc: definite-assignment analysis does not apply to
                // computed keys of *method* members, only plain properties
                // (`computedPropertyNames10_ES6.ts`).
                let is_method = matches!(
                  self.body.exprs[value.0 as usize].kind,
                  ExprKind::FunctionExpr { .. }
                );
                if is_method {
                  self.method_key_depth += 1;
                }
                self.visit_expr(*expr);
                if is_method {
                  self.method_key_depth -= 1;
                }
              }
            }
            ObjectProperty::Getter { body, key } | ObjectProperty::Setter { body, key } => {
              if let ObjectKey::Computed(expr) = key {
                // Accessors are methods for DA purposes (tsc).
                self.method_key_depth += 1;
                self.visit_expr(*expr);
                self.method_key_depth -= 1;
              }
              self.visit_body(*body);
            }
            ObjectProperty::Spread(expr) => self.visit_expr(*expr),
          }
        }
      }
      ExprKind::Template(template) => {
        for span in template.spans.iter() {
          self.visit_expr(span.expr);
        }
      }
      ExprKind::TaggedTemplate { tag, template } => {
        self.visit_expr(*tag);
        for span in template.spans.iter() {
          self.visit_expr(span.expr);
        }
      }
      ExprKind::Await { expr } => self.visit_expr(*expr),
      ExprKind::Yield { expr, .. } => {
        if let Some(expr) = expr {
          self.visit_expr(*expr);
        }
      }
      ExprKind::TypeAssertion { expr, .. }
      | ExprKind::NonNull { expr, .. }
      | ExprKind::Satisfies { expr, .. }
      | ExprKind::Instantiation { expr, .. } => self.visit_expr(*expr),
      ExprKind::ImportCall {
        argument,
        attributes,
      } => {
        self.visit_expr(*argument);
        if let Some(attrs) = attributes {
          self.visit_expr(*attrs);
        }
      }
      ExprKind::Jsx(elem) => {
        for attr in elem.attributes.iter() {
          match attr {
            hir_js::JsxAttr::Named { value, .. } => {
              if let Some(value) = value {
                match value {
                  hir_js::JsxAttrValue::Expression(container) => {
                    if let Some(expr) = container.expr {
                      self.visit_expr(expr);
                    }
                  }
                  hir_js::JsxAttrValue::Element(expr) => {
                    self.visit_expr(*expr);
                  }
                  hir_js::JsxAttrValue::Text(_) => {}
                }
              }
            }
            hir_js::JsxAttr::Spread { expr } => self.visit_expr(*expr),
          }
        }
        for child in elem.children.iter() {
          match child {
            hir_js::JsxChild::Text(_) => {}
            hir_js::JsxChild::Expr(container) => {
              if let Some(expr) = container.expr {
                self.visit_expr(expr);
              }
            }
            hir_js::JsxChild::Element(expr) => self.visit_expr(*expr),
          }
        }
      }
      ExprKind::Literal(_)
      | ExprKind::Missing
      | ExprKind::This
      | ExprKind::Super
      | ExprKind::FunctionExpr { .. }
      | ExprKind::ClassExpr { .. }
      | ExprKind::ImportMeta
      | ExprKind::NewTarget => {}
    }
  }

  pub(crate) fn visit_body(&mut self, _body_id: BodyId) {
    // Nested bodies are checked separately; nothing to do here.
  }

  pub(crate) fn visit_pat(&mut self, pat_id: PatId) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => {
        let binding = self.resolve_binding(*name);
        self.table.pat_bindings.entry(pat_id).or_insert(binding);
      }
      PatKind::Assign {
        target,
        default_value,
      } => {
        self.visit_pat(*target);
        self.visit_expr(*default_value);
      }
      PatKind::Rest(inner) => self.visit_pat(**inner),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.visit_pat(elem.pat);
          if let Some(default) = elem.default_value {
            self.visit_expr(default);
          }
        }
        if let Some(rest) = arr.rest {
          self.visit_pat(rest);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.visit_pat(prop.value);
          if let Some(default) = prop.default_value {
            self.visit_expr(default);
          }
          if let ObjectKey::Computed(expr) = &prop.key {
            self.visit_expr(*expr);
          }
        }
        if let Some(rest) = obj.rest {
          self.visit_pat(rest);
        }
      }
      PatKind::AssignTarget(expr) => self.visit_expr(*expr),
    }
  }

  pub(crate) fn push_scope(&mut self) {
    self.scopes.push(HashMap::new());
  }

  pub(crate) fn pop_scope(&mut self) {
    self.scopes.pop();
  }
}

// ---------------------------------------------------------------------------
// Computed object-literal keys (tsc `checkComputedPropertyName` +
// `getIndexInfosOfIndexSymbol` / `getObjectLiteralIndexInfo`)
// ---------------------------------------------------------------------------

/// Classification of an evaluated computed object-literal key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ComputedObjKey {
  /// String/number literal key — a *named* property (tsc late-binds these).
  Named(PropKey),
  /// Non-literal key assignable to `string`/`number`/`symbol` — contributes
  /// to an index signature keyed by the given primitive (tsc
  /// `getIndexInfosOfIndexSymbol`; `any` and numeric-enum keys take the
  /// numeric branch, mixed `string | number` unions the string branch).
  Index(TypeId),
  /// Not usable as a property key (`unknown`, `never`, unions containing
  /// non-key types, unique symbols we cannot name, …) — the member is
  /// checked for side effects but contributes nothing. We do not yet emit
  /// tsc's TS1166 ("computed property name must be of type …").
  Skip,
}

/// Classify the *type* of a computed object-literal key expression.
pub(crate) fn classify_computed_obj_key(store: &TypeStore, key_ty: TypeId) -> ComputedObjKey {
  let prim = store.primitive_ids();
  match store.type_kind(key_ty) {
    TypeKind::StringLiteral(id) => return ComputedObjKey::Named(PropKey::String(id)),
    TypeKind::NumberLiteral(v) => {
      let n = v.0;
      if n.fract() == 0.0 && n >= i64::MIN as f64 && n <= i64::MAX as f64 {
        return ComputedObjKey::Named(PropKey::Number(n as i64));
      }
      return ComputedObjKey::Named(PropKey::String(store.intern_name(n.to_string())));
    }
    _ => {}
  }
  let canon = store.canon(key_ty);
  match store.type_kind(canon) {
    TypeKind::Number => ComputedObjKey::Index(prim.number),
    TypeKind::String => ComputedObjKey::Index(prim.string),
    TypeKind::Symbol => ComputedObjKey::Index(prim.symbol),
    // tsc: `any` is assignable to `number` first, so it takes the numeric branch.
    TypeKind::Any => ComputedObjKey::Index(prim.number),
    TypeKind::Union(members) => {
      let mut all_number = true;
      let mut all_string = true;
      let mut all_symbol = true;
      for member in members {
        match store.type_kind(store.canon(member)) {
          TypeKind::Number | TypeKind::NumberLiteral(_) => {
            all_string = false;
            all_symbol = false;
          }
          TypeKind::String | TypeKind::StringLiteral(_) => {
            all_number = false;
            all_symbol = false;
          }
          TypeKind::Symbol => {
            all_number = false;
            all_string = false;
          }
          _ => return ComputedObjKey::Skip,
        }
      }
      if all_number {
        ComputedObjKey::Index(prim.number)
      } else if all_string {
        ComputedObjKey::Index(prim.string)
      } else if all_symbol {
        ComputedObjKey::Index(prim.symbol)
      } else {
        // Mixed key unions (e.g. `string | number`) are not assignable to
        // `number`/`symbol`, so tsc routes them to the string branch.
        ComputedObjKey::Index(prim.string)
      }
    }
    _ => ComputedObjKey::Skip,
  }
}

/// Synthesize index signatures from computed-key contributions
/// (`(key_kind, value_type)` pairs), following tsc
/// `getObjectLiteralIndexInfo`: the string index also unions in *all* named
/// sibling properties (numeric names are string-keyed at runtime; symbol
/// names are excluded), the number index unions numeric-named siblings, and
/// the symbol index unions symbol-named siblings. Only kinds with at least
/// one computed contribution gain an indexer. Values use plain unions (tsc
/// applies subtype reduction; the canonicalizer already dedups).
pub(crate) fn synthesize_computed_indexers(
  store: &TypeStore,
  shape: &mut Shape,
  contribs: &[(TypeId, TypeId)],
) {
  if contribs.is_empty() {
    return;
  }
  let prim = store.primitive_ids();
  for kind in [prim.string, prim.number, prim.symbol] {
    let mut values: Vec<TypeId> = contribs
      .iter()
      .filter(|(k, _)| *k == kind)
      .map(|(_, v)| *v)
      .collect();
    if values.is_empty() {
      continue;
    }
    for prop in shape.properties.iter() {
      let include = match &prop.key {
        PropKey::Number(_) => kind == prim.string || kind == prim.number,
        PropKey::String(_) => kind == prim.string,
        PropKey::Symbol(_) => kind == prim.symbol,
      };
      if include {
        values.push(prop.data.ty);
      }
    }
    let value = store.union(values);
    shape.indexers.push(Indexer {
      key_type: kind,
      value_type: value,
      readonly: false,
    });
  }
}
