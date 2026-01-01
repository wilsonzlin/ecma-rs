use std::collections::HashMap;

use hir_js::{
  ids::{ExprId, PatId},
  ArrayElement, Body, ExprKind, ForHead, ForInit, MemberExpr, ObjectKey, PatKind, StmtId, StmtKind,
  VarDeclKind,
};
use semantic_js::ts::{locals::TsLocalSemantics, SymbolId};
use std::collections::HashSet;

pub type FlowBindingId = SymbolId;

/// Per-body side table mapping identifiers in expressions and patterns back to
/// their resolved bindings.
#[derive(Debug, Clone)]
pub struct FlowBindings {
  expr_bindings: Vec<Option<FlowBindingId>>,
  pat_bindings: Vec<Option<FlowBindingId>>,
  entry_bindings: HashMap<hir_js::NameId, FlowBindingId>,
}

impl FlowBindings {
  /// Precompute bindings for all identifier expressions and patterns in a body
  /// using the locals binder so lookups during flow analysis are O(1).
  pub fn new(body: &Body, sem: &TsLocalSemantics) -> Self {
    let expr_bindings = body
      .exprs
      .iter()
      .enumerate()
      .map(|(idx, expr)| {
        matches!(expr.kind, ExprKind::Ident(_))
          .then(|| ExprId(idx as u32))
          .and_then(|id| {
            let span = expr.span;
            sem
              .resolve_expr(body, id)
              .or_else(|| sem.resolve_expr_span(span))
              .or_else(|| sem.resolve_expr_at_offset(span.start).map(|(_, id)| id))
              .or_else(|| {
                if span.end > span.start {
                  sem.resolve_expr_at_offset(span.end - 1).map(|(_, id)| id)
                } else {
                  None
                }
              })
          })
      })
      .collect();

    let pat_bindings = body
      .pats
      .iter()
      .map(|pat| {
        matches!(pat.kind, PatKind::Ident(_))
          .then(|| pat.span)
          .and_then(|span| {
            sem
              .resolve_expr_span(span)
              .or_else(|| sem.resolve_expr_at_offset(span.start).map(|(_, id)| id))
              .or_else(|| {
                if span.end > span.start {
                  sem.resolve_expr_at_offset(span.end - 1).map(|(_, id)| id)
                } else {
                  None
                }
              })
          })
      })
      .collect();

    let mut bindings = FlowBindings {
      expr_bindings,
      pat_bindings,
      entry_bindings: HashMap::new(),
    };
    bindings.populate_entry_bindings(body);
    bindings
  }

  /// Fallback constructor that infers bindings lexically when locals semantics
  /// are unavailable.
  pub fn from_body(body: &Body) -> Self {
    FlowBindingsBuilder::new(body).build()
  }

  /// Binding identifier for an expression, if it was an identifier expression
  /// and could be resolved.
  pub fn binding_for_expr(&self, expr_id: ExprId) -> Option<FlowBindingId> {
    self
      .expr_bindings
      .get(expr_id.0 as usize)
      .copied()
      .flatten()
  }

  /// Binding identifier for a pattern, if it was an identifier pattern and
  /// could be resolved.
  pub fn binding_for_pat(&self, pat_id: PatId) -> Option<FlowBindingId> {
    self.pat_bindings.get(pat_id.0 as usize).copied().flatten()
  }

  /// Resolve a binding by name visible at the entry of this body (parameters,
  /// var-scoped declarations, root-level lexicals, or outer bindings referenced
  /// from expressions).
  pub fn binding_for_name(&self, name: hir_js::NameId) -> Option<FlowBindingId> {
    self.entry_bindings.get(&name).copied()
  }

  fn populate_entry_bindings(&mut self, body: &Body) {
    for (idx, expr) in body.exprs.iter().enumerate() {
      if let ExprKind::Ident(name) = expr.kind {
        if let Some(binding) = self.expr_bindings.get(idx).and_then(|b| *b) {
          self.entry_bindings.entry(name).or_insert(binding);
        }
      }
    }
    for (idx, pat) in body.pats.iter().enumerate() {
      if let PatKind::Ident(name) = pat.kind {
        if let Some(binding) = self.pat_bindings.get(idx).and_then(|b| *b) {
          self.entry_bindings.entry(name).or_insert(binding);
        }
      }
    }
  }
}

struct FlowBindingsBuilder<'a> {
  body: &'a Body,
  bindings: FlowBindings,
  next_binding: u64,
  var_scope: HashMap<hir_js::NameId, FlowBindingId>,
  free_bindings: HashMap<hir_js::NameId, FlowBindingId>,
  root_scope: HashMap<hir_js::NameId, FlowBindingId>,
}

impl<'a> FlowBindingsBuilder<'a> {
  fn new(body: &'a Body) -> Self {
    FlowBindingsBuilder {
      body,
      bindings: FlowBindings {
        expr_bindings: vec![None; body.exprs.len()],
        pat_bindings: vec![None; body.pats.len()],
        entry_bindings: HashMap::new(),
      },
      next_binding: 0,
      var_scope: HashMap::new(),
      free_bindings: HashMap::new(),
      root_scope: HashMap::new(),
    }
  }

  fn build(mut self) -> FlowBindings {
    let roots = self.root_stmts();
    self.collect_var_scope(&roots);

    let mut lexical_scopes: Vec<HashMap<_, _>> = Vec::new();
    self.process_block(&roots, &mut lexical_scopes);

    let mut entry = self.var_scope.clone();
    for (name, binding) in self.root_scope {
      entry.insert(name, binding);
    }
    for (name, binding) in self.free_bindings {
      entry.entry(name).or_insert(binding);
    }
    self.bindings.entry_bindings = entry;
    self.bindings
  }

  fn root_stmts(&self) -> Vec<StmtId> {
    if !self.body.root_stmts.is_empty() {
      return self.body.root_stmts.clone();
    }
    let mut referenced: HashSet<StmtId> = HashSet::new();
    for stmt in self.body.stmts.iter() {
      referenced.extend(child_stmt_ids(stmt));
    }
    let mut roots: Vec<StmtId> = (0..self.body.stmts.len() as u32)
      .map(StmtId)
      .filter(|id| !referenced.contains(id))
      .collect();
    roots.sort_by_key(|id| id.0);
    roots
  }

  fn collect_var_scope(&mut self, roots: &[StmtId]) {
    if let Some(func) = &self.body.function {
      for param in func.params.iter() {
        self.declare_var_pat(param.pat);
      }
    }
    for stmt in roots.iter() {
      self.collect_var_stmt(*stmt);
    }
  }

  fn collect_var_stmt(&mut self, stmt_id: StmtId) {
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    match &stmt.kind {
      StmtKind::Var(decl) if decl.kind == VarDeclKind::Var => {
        for declarator in decl.declarators.iter() {
          self.declare_var_pat(declarator.pat);
        }
      }
      StmtKind::For {
        init,
        test: _,
        update: _,
        body,
      } => {
        if let Some(init) = init {
          if let ForInit::Var(decl) = init {
            if decl.kind == VarDeclKind::Var {
              for declarator in decl.declarators.iter() {
                self.declare_var_pat(declarator.pat);
              }
            }
          }
        }
        self.collect_var_stmt(*body);
      }
      StmtKind::ForIn { left, body, .. } => {
        if let ForHead::Var(decl) = left {
          if decl.kind == VarDeclKind::Var {
            for declarator in decl.declarators.iter() {
              self.declare_var_pat(declarator.pat);
            }
          }
        }
        self.collect_var_stmt(*body);
      }
      StmtKind::If {
        test: _,
        consequent,
        alternate,
      } => {
        self.collect_var_stmt(*consequent);
        if let Some(alt) = alternate {
          self.collect_var_stmt(*alt);
        }
      }
      StmtKind::While { test: _, body } | StmtKind::DoWhile { test: _, body } => {
        self.collect_var_stmt(*body);
      }
      StmtKind::Switch {
        discriminant: _,
        cases,
      } => {
        for case in cases.iter() {
          for stmt in case.consequent.iter() {
            self.collect_var_stmt(*stmt);
          }
        }
      }
      StmtKind::Try {
        block,
        catch,
        finally_block,
      } => {
        self.collect_var_stmt(*block);
        if let Some(c) = catch {
          self.collect_var_stmt(c.body);
        }
        if let Some(finally_stmt) = finally_block {
          self.collect_var_stmt(*finally_stmt);
        }
      }
      StmtKind::Block(stmts) => {
        for stmt in stmts.iter() {
          self.collect_var_stmt(*stmt);
        }
      }
      StmtKind::With { object: _, body } => self.collect_var_stmt(*body),
      StmtKind::Labeled { label: _, body } => self.collect_var_stmt(*body),
      _ => {}
    }
  }

  fn process_block(
    &mut self,
    stmts: &[StmtId],
    lexical_scopes: &mut Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) {
    let scope = self.collect_block_scope(stmts);
    if lexical_scopes.is_empty() {
      self.root_scope = scope.clone();
    }
    lexical_scopes.push(scope);
    for stmt in stmts.iter() {
      self.process_stmt(*stmt, lexical_scopes);
    }
    lexical_scopes.pop();
  }

  fn collect_block_scope(&mut self, stmts: &[StmtId]) -> HashMap<hir_js::NameId, FlowBindingId> {
    let mut scope = HashMap::new();
    for stmt in stmts.iter() {
      let stmt = &self.body.stmts[stmt.0 as usize];
      if let StmtKind::Var(decl) = &stmt.kind {
        if decl.kind != VarDeclKind::Var {
          for declarator in decl.declarators.iter() {
            self.declare_lexical_pat(declarator.pat, &mut scope);
          }
        }
      }
    }
    scope
  }

  fn process_stmt(
    &mut self,
    stmt_id: StmtId,
    lexical_scopes: &mut Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) {
    let stmt = &self.body.stmts[stmt_id.0 as usize];
    match &stmt.kind {
      StmtKind::Expr(expr) => self.process_expr(*expr, lexical_scopes),
      StmtKind::Return(expr) => {
        if let Some(expr) = expr {
          self.process_expr(*expr, lexical_scopes);
        }
      }
      StmtKind::Throw(expr) => self.process_expr(*expr, lexical_scopes),
      StmtKind::If {
        test,
        consequent,
        alternate,
      } => {
        self.process_expr(*test, lexical_scopes);
        self.process_stmt(*consequent, lexical_scopes);
        if let Some(alt) = alternate {
          self.process_stmt(*alt, lexical_scopes);
        }
      }
      StmtKind::While { test, body } | StmtKind::DoWhile { test, body } => {
        self.process_expr(*test, lexical_scopes);
        self.process_stmt(*body, lexical_scopes);
      }
      StmtKind::For {
        init,
        test,
        update,
        body,
      } => {
        let mut loop_scope = None;
        if let Some(ForInit::Var(decl)) = init {
          if decl.kind != VarDeclKind::Var {
            let mut scope = HashMap::new();
            for declarator in decl.declarators.iter() {
              self.declare_lexical_pat(declarator.pat, &mut scope);
            }
            loop_scope = Some(scope);
          }
        }

        if let Some(scope) = loop_scope.take() {
          lexical_scopes.push(scope);
        }

        if let Some(init) = init {
          match init {
            ForInit::Expr(expr) => self.process_expr(*expr, lexical_scopes),
            ForInit::Var(decl) => self.process_var_decl(decl, lexical_scopes),
          }
        }
        if let Some(test) = test {
          self.process_expr(*test, lexical_scopes);
        }
        if let Some(update) = update {
          self.process_expr(*update, lexical_scopes);
        }
        self.process_stmt(*body, lexical_scopes);

        if let Some(ForInit::Var(decl)) = init {
          if decl.kind != VarDeclKind::Var {
            lexical_scopes.pop();
          }
        }
      }
      StmtKind::ForIn {
        left, right, body, ..
      } => {
        let mut loop_scope = None;
        if let ForHead::Var(decl) = left {
          if decl.kind != VarDeclKind::Var {
            let mut scope = HashMap::new();
            for declarator in decl.declarators.iter() {
              self.declare_lexical_pat(declarator.pat, &mut scope);
            }
            loop_scope = Some(scope);
          }
        }

        if let Some(scope) = loop_scope.take() {
          lexical_scopes.push(scope);
        }

        match left {
          ForHead::Pat(pat) => self.bind_existing_pat(*pat, lexical_scopes),
          ForHead::Var(decl) => self.process_var_decl(decl, lexical_scopes),
        }
        self.process_expr(*right, lexical_scopes);
        self.process_stmt(*body, lexical_scopes);

        if let ForHead::Var(decl) = left {
          if decl.kind != VarDeclKind::Var {
            lexical_scopes.pop();
          }
        }
      }
      StmtKind::Switch {
        discriminant,
        cases,
      } => {
        self.process_expr(*discriminant, lexical_scopes);
        let switch_scope = self.collect_switch_scope(cases);
        lexical_scopes.push(switch_scope);
        for case in cases.iter() {
          if let Some(test) = case.test {
            self.process_expr(test, lexical_scopes);
          }
          for stmt in case.consequent.iter() {
            self.process_stmt(*stmt, lexical_scopes);
          }
        }
        lexical_scopes.pop();
      }
      StmtKind::Try {
        block,
        catch,
        finally_block,
      } => {
        self.process_stmt(*block, lexical_scopes);
        if let Some(catch) = catch {
          let mut catch_scope = HashMap::new();
          if let Some(param) = catch.param {
            self.declare_lexical_pat(param, &mut catch_scope);
          }
          lexical_scopes.push(catch_scope);
          self.process_stmt(catch.body, lexical_scopes);
          lexical_scopes.pop();
        }
        if let Some(finally_stmt) = finally_block {
          self.process_stmt(*finally_stmt, lexical_scopes);
        }
      }
      StmtKind::Block(stmts) => self.process_block(stmts, lexical_scopes),
      StmtKind::Var(decl) => self.process_var_decl(decl, lexical_scopes),
      StmtKind::With { object, body } => {
        self.process_expr(*object, lexical_scopes);
        self.process_stmt(*body, lexical_scopes);
      }
      StmtKind::Labeled { label: _, body } => self.process_stmt(*body, lexical_scopes),
      _ => {}
    }
  }

  fn collect_switch_scope(
    &mut self,
    cases: &[hir_js::hir::SwitchCase],
  ) -> HashMap<hir_js::NameId, FlowBindingId> {
    let mut scope = HashMap::new();
    for case in cases.iter() {
      for stmt in case.consequent.iter() {
        let stmt = &self.body.stmts[stmt.0 as usize];
        if let StmtKind::Var(decl) = &stmt.kind {
          if decl.kind != VarDeclKind::Var {
            for declarator in decl.declarators.iter() {
              self.declare_lexical_pat(declarator.pat, &mut scope);
            }
          }
        }
      }
    }
    scope
  }

  fn process_var_decl(
    &mut self,
    decl: &hir_js::VarDecl,
    lexical_scopes: &mut Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) {
    for declarator in decl.declarators.iter() {
      self.bind_existing_pat(declarator.pat, lexical_scopes);
      if let Some(init) = declarator.init {
        self.process_expr(init, lexical_scopes);
      }
    }
  }

  fn process_expr(
    &mut self,
    expr_id: ExprId,
    lexical_scopes: &mut Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) {
    let expr = &self.body.exprs[expr_id.0 as usize];
    match &expr.kind {
      ExprKind::Ident(name) => {
        let binding = self.resolve_binding(*name, lexical_scopes);
        self.bindings.expr_bindings[expr_id.0 as usize] = Some(binding);
      }
      ExprKind::Unary { expr, .. }
      | ExprKind::Update { expr, .. }
      | ExprKind::TypeAssertion { expr, .. } => {
        self.process_expr(*expr, lexical_scopes);
      }
      ExprKind::Binary { left, right, .. } => {
        self.process_expr(*left, lexical_scopes);
        self.process_expr(*right, lexical_scopes);
      }
      ExprKind::Assignment { target, value, .. } => {
        self.bind_existing_pat(*target, lexical_scopes);
        self.process_expr(*value, lexical_scopes);
      }
      ExprKind::Call(call) => {
        self.process_expr(call.callee, lexical_scopes);
        for arg in call.args.iter() {
          self.process_expr(arg.expr, lexical_scopes);
        }
      }
      ExprKind::Member(mem) => self.process_member(mem, lexical_scopes),
      ExprKind::Conditional {
        test,
        consequent,
        alternate,
      } => {
        self.process_expr(*test, lexical_scopes);
        self.process_expr(*consequent, lexical_scopes);
        self.process_expr(*alternate, lexical_scopes);
      }
      ExprKind::Array(arr) => {
        for elem in arr.elements.iter() {
          match elem {
            ArrayElement::Expr(id) | ArrayElement::Spread(id) => {
              self.process_expr(*id, lexical_scopes);
            }
            ArrayElement::Empty => {}
          }
        }
      }
      ExprKind::Object(obj) => {
        for prop in obj.properties.iter() {
          match prop {
            hir_js::ObjectProperty::KeyValue { value, .. } => {
              self.process_expr(*value, lexical_scopes);
            }
            hir_js::ObjectProperty::Getter { .. } | hir_js::ObjectProperty::Setter { .. } => {}
            hir_js::ObjectProperty::Spread(expr) => self.process_expr(*expr, lexical_scopes),
          }
        }
      }
      ExprKind::FunctionExpr { .. } | ExprKind::ClassExpr { .. } => {}
      ExprKind::Template(lit) => {
        for span in lit.spans.iter() {
          self.process_expr(span.expr, lexical_scopes);
        }
      }
      ExprKind::TaggedTemplate { tag, template } => {
        self.process_expr(*tag, lexical_scopes);
        for span in template.spans.iter() {
          self.process_expr(span.expr, lexical_scopes);
        }
      }
      ExprKind::Await { expr } | ExprKind::NonNull { expr } | ExprKind::Satisfies { expr, .. } => {
        self.process_expr(*expr, lexical_scopes);
      }
      ExprKind::Yield { expr, .. } => {
        if let Some(expr) = expr {
          self.process_expr(*expr, lexical_scopes);
        }
      }
      ExprKind::ImportCall {
        argument,
        attributes,
      } => {
        self.process_expr(*argument, lexical_scopes);
        if let Some(attrs) = attributes {
          self.process_expr(*attrs, lexical_scopes);
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
                      self.process_expr(expr, lexical_scopes);
                    }
                  }
                  hir_js::JsxAttrValue::Element(expr) => {
                    self.process_expr(*expr, lexical_scopes);
                  }
                  hir_js::JsxAttrValue::Text(_) => {}
                }
              }
            }
            hir_js::JsxAttr::Spread { expr } => self.process_expr(*expr, lexical_scopes),
          }
        }
        for child in elem.children.iter() {
          match child {
            hir_js::JsxChild::Text(_) => {}
            hir_js::JsxChild::Expr(container) => {
              if let Some(expr) = container.expr {
                self.process_expr(expr, lexical_scopes);
              }
            }
            hir_js::JsxChild::Element(expr) => self.process_expr(*expr, lexical_scopes),
          }
        }
      }
      ExprKind::This
      | ExprKind::Super
      | ExprKind::Literal(_)
      | ExprKind::Missing
      | ExprKind::NewTarget
      | ExprKind::ImportMeta => {}
    }
  }

  fn process_member(
    &mut self,
    mem: &MemberExpr,
    lexical_scopes: &mut Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) {
    self.process_expr(mem.object, lexical_scopes);
    if let ObjectKey::Computed(expr) = mem.property {
      self.process_expr(expr, lexical_scopes);
    }
  }

  fn bind_existing_pat(
    &mut self,
    pat_id: PatId,
    lexical_scopes: &mut Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => {
        let binding = self.resolve_binding(*name, lexical_scopes);
        self.bindings.pat_bindings[pat_id.0 as usize] = Some(binding);
      }
      PatKind::Assign {
        target,
        default_value,
      } => {
        self.bind_existing_pat(*target, lexical_scopes);
        self.process_expr(*default_value, lexical_scopes);
      }
      PatKind::Rest(inner) => self.bind_existing_pat(**inner, lexical_scopes),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.bind_existing_pat(elem.pat, lexical_scopes);
          if let Some(default) = elem.default_value {
            self.process_expr(default, lexical_scopes);
          }
        }
        if let Some(rest) = arr.rest {
          self.bind_existing_pat(rest, lexical_scopes);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.bind_existing_pat(prop.value, lexical_scopes);
          if let Some(default) = prop.default_value {
            self.process_expr(default, lexical_scopes);
          }
        }
        if let Some(rest) = obj.rest {
          self.bind_existing_pat(rest, lexical_scopes);
        }
      }
      PatKind::AssignTarget(expr) => self.process_expr(*expr, lexical_scopes),
    }
  }

  fn declare_var_pat(&mut self, pat_id: PatId) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => {
        let binding = self.declare_var_name(*name);
        self.bindings.pat_bindings[pat_id.0 as usize] = Some(binding);
      }
      PatKind::Assign { target, .. } => self.declare_var_pat(*target),
      PatKind::Rest(inner) => self.declare_var_pat(**inner),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.declare_var_pat(elem.pat);
        }
        if let Some(rest) = arr.rest {
          self.declare_var_pat(rest);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.declare_var_pat(prop.value);
        }
        if let Some(rest) = obj.rest {
          self.declare_var_pat(rest);
        }
      }
      PatKind::AssignTarget(expr) => self.process_expr(*expr, &mut Vec::new()),
    }
  }

  fn declare_var_name(&mut self, name: hir_js::NameId) -> FlowBindingId {
    if let Some(existing) = self.var_scope.get(&name) {
      *existing
    } else {
      let next = self.next_binding();
      self.var_scope.insert(name, next);
      next
    }
  }

  fn declare_lexical_pat(
    &mut self,
    pat_id: PatId,
    scope: &mut HashMap<hir_js::NameId, FlowBindingId>,
  ) {
    let pat = &self.body.pats[pat_id.0 as usize];
    match &pat.kind {
      PatKind::Ident(name) => {
        let binding = *scope.entry(*name).or_insert_with(|| self.next_binding());
        self.bindings.pat_bindings[pat_id.0 as usize] = Some(binding);
      }
      PatKind::Assign { target, .. } => self.declare_lexical_pat(*target, scope),
      PatKind::Rest(inner) => self.declare_lexical_pat(**inner, scope),
      PatKind::Array(arr) => {
        for elem in arr.elements.iter().flatten() {
          self.declare_lexical_pat(elem.pat, scope);
        }
        if let Some(rest) = arr.rest {
          self.declare_lexical_pat(rest, scope);
        }
      }
      PatKind::Object(obj) => {
        for prop in obj.props.iter() {
          self.declare_lexical_pat(prop.value, scope);
        }
        if let Some(rest) = obj.rest {
          self.declare_lexical_pat(rest, scope);
        }
      }
      PatKind::AssignTarget(_) => {}
    }
  }

  fn resolve_binding(
    &mut self,
    name: hir_js::NameId,
    lexical_scopes: &Vec<HashMap<hir_js::NameId, FlowBindingId>>,
  ) -> FlowBindingId {
    for scope in lexical_scopes.iter().rev() {
      if let Some(binding) = scope.get(&name) {
        return *binding;
      }
    }
    if let Some(binding) = self.var_scope.get(&name) {
      return *binding;
    }
    if let Some(binding) = self.free_bindings.get(&name) {
      return *binding;
    }
    let next = self.next_binding();
    self.free_bindings.insert(name, next);
    next
  }

  fn next_binding(&mut self) -> FlowBindingId {
    let next = SymbolId(self.next_binding);
    self.next_binding += 1;
    next
  }
}

fn child_stmt_ids(stmt: &hir_js::Stmt) -> Vec<StmtId> {
  match &stmt.kind {
    StmtKind::Block(stmts) => stmts.clone(),
    StmtKind::If {
      consequent,
      alternate,
      ..
    } => alternate
      .iter()
      .copied()
      .chain(std::iter::once(*consequent))
      .collect(),
    StmtKind::While { body, .. } | StmtKind::DoWhile { body, .. } => vec![*body],
    StmtKind::For { body, .. } => vec![*body],
    StmtKind::ForIn { body, .. } => vec![*body],
    StmtKind::Switch { cases, .. } => cases
      .iter()
      .flat_map(|c| c.consequent.iter().copied())
      .collect(),
    StmtKind::Try {
      block,
      catch,
      finally_block,
    } => catch
      .iter()
      .map(|c| c.body)
      .chain(finally_block.iter().copied())
      .chain(std::iter::once(*block))
      .collect(),
    StmtKind::Labeled { body, .. } => vec![*body],
    StmtKind::With { body, .. } => vec![*body],
    _ => Vec::new(),
  }
}
