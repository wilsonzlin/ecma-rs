use crate::{Heap, RootId, Scope, Value, Vm, VmError};
use diagnostics::FileId;
use parse_js::ast::expr::lit::{LitBoolExpr, LitNumExpr, LitStrExpr};
use parse_js::ast::expr::{BinaryExpr, Expr, IdExpr};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::node::{literal_string_code_units, Node};
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  BlockStmt, CatchBlock, DoWhileStmt, ExprStmt, ForBody, ForTripleStmt, IfStmt, ReturnStmt, Stmt,
  ThrowStmt, TryStmt, WhileStmt,
};
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::collections::{HashMap, HashSet};

/// An ECMAScript completion record (ECMA-262).
///
/// We model the "empty" completion value explicitly as `None` so statement-list evaluation can
/// implement `UpdateEmpty` correctly (e.g. `1; if (true) {}` should evaluate to `1`).
#[derive(Clone, Debug, PartialEq)]
pub enum Completion {
  Normal(Option<Value>),
  Throw(Value),
  Return(Value),
  Break(Option<String>, Option<Value>),
  Continue(Option<String>, Option<Value>),
}

impl Completion {
  pub fn empty() -> Self {
    Completion::Normal(None)
  }

  pub fn normal(value: Value) -> Self {
    Completion::Normal(Some(value))
  }

  pub fn value(&self) -> Option<Value> {
    match self {
      Completion::Normal(v) => *v,
      Completion::Throw(v) => Some(*v),
      Completion::Return(v) => Some(*v),
      Completion::Break(_, v) => *v,
      Completion::Continue(_, v) => *v,
    }
  }

  pub fn is_abrupt(&self) -> bool {
    !matches!(self, Completion::Normal(_))
  }

  /// Implements `UpdateEmpty(completion, value)` from ECMA-262.
  pub fn update_empty(self, value: Option<Value>) -> Self {
    match self {
      Completion::Normal(None) => Completion::Normal(value),
      Completion::Break(target, None) => Completion::Break(target, value),
      Completion::Continue(target, None) => Completion::Continue(target, value),
      other => other,
    }
  }
}

#[derive(Clone, Copy, Debug)]
struct Binding {
  root: RootId,
  mutable: bool,
}

#[derive(Debug, Default)]
struct Env {
  var: HashMap<String, Binding>,
  lexical: Vec<HashMap<String, Binding>>,
}

impl Env {
  fn new() -> Self {
    // Start with the global lexical environment frame.
    Self {
      var: HashMap::new(),
      lexical: vec![HashMap::new()],
    }
  }

  fn push_lexical(&mut self) {
    self.lexical.push(HashMap::new());
  }

  fn pop_lexical(&mut self, heap: &mut Heap) {
    debug_assert!(
      self.lexical.len() > 1,
      "attempted to pop global lexical environment"
    );
    if self.lexical.len() <= 1 {
      return;
    }

    if let Some(frame) = self.lexical.pop() {
      for binding in frame.values() {
        heap.remove_root(binding.root);
      }
    }
  }

  fn declare_var(&mut self, heap: &mut Heap, name: &str) {
    if self.var.contains_key(name) {
      return;
    }
    let root = heap.add_root(Value::Undefined);
    self.var.insert(
      name.to_string(),
      Binding {
        root,
        mutable: true,
      },
    );
  }

  fn declare_lexical(
    &mut self,
    heap: &mut Heap,
    name: &str,
    mutable: bool,
    value: Value,
  ) -> Result<(), VmError> {
    let Some(frame) = self.lexical.last_mut() else {
      return Err(VmError::Unimplemented("lexical env stack underflow"));
    };
    if frame.contains_key(name) {
      // TODO: Should be a syntax error (early error).
      return Err(VmError::Unimplemented("duplicate lexical declaration"));
    }
    let root = heap.add_root(value);
    frame.insert(name.to_string(), Binding { root, mutable });
    Ok(())
  }

  fn get(&self, heap: &Heap, name: &str) -> Option<Value> {
    for frame in self.lexical.iter().rev() {
      if let Some(binding) = frame.get(name) {
        return heap.get_root(binding.root);
      }
    }
    self.var.get(name).and_then(|binding| heap.get_root(binding.root))
  }

  fn set(&mut self, heap: &mut Heap, name: &str, value: Value) -> Result<(), VmError> {
    for frame in self.lexical.iter_mut().rev() {
      if let Some(binding) = frame.get(name).copied() {
        if !binding.mutable {
          // TODO: Should throw a TypeError.
          return Err(VmError::Unimplemented("assignment to const"));
        }
        heap.set_root(binding.root, value);
        return Ok(());
      }
    }

    if let Some(binding) = self.var.get(name).copied() {
      heap.set_root(binding.root, value);
      return Ok(());
    }

    // Sloppy-mode fallback: create a global `var` binding.
    self.declare_var(heap, name);
    let binding = self.var.get(name).copied().unwrap();
    heap.set_root(binding.root, value);
    Ok(())
  }

  fn set_var(&mut self, heap: &mut Heap, name: &str, value: Value) -> Result<(), VmError> {
    self.declare_var(heap, name);
    let binding = self.var.get(name).copied().unwrap();
    heap.set_root(binding.root, value);
    Ok(())
  }
}

/// An (early, incomplete) AST-interpreting execution engine for `parse-js` syntax trees.
pub struct JsRuntime {
  pub vm: Vm,
  pub heap: Heap,
  env: Env,
}

impl JsRuntime {
  pub fn new(vm: Vm, heap: Heap) -> Self {
    Self {
      vm,
      heap,
      env: Env::new(),
    }
  }

  pub fn heap(&self) -> &Heap {
    &self.heap
  }

  pub fn heap_mut(&mut self) -> &mut Heap {
    &mut self.heap
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`).
  pub fn exec_script(&mut self, source: &str) -> Result<Value, VmError> {
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };
    let top = parse_with_options(source, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;

    let heap = &mut self.heap;
    let mut evaluator = Evaluator {
      vm: &mut self.vm,
      env: &mut self.env,
    };
    evaluator.hoist_var_decls(heap, &top.stx.body)?;

    let mut scope = heap.scope();
    let completion = evaluator.eval_stmt_list(&mut scope, &top.stx.body)?;
    match completion {
      Completion::Normal(v) => Ok(v.unwrap_or(Value::Undefined)),
      Completion::Throw(v) => Err(VmError::Throw(v)),
      Completion::Return(_) => Err(VmError::Unimplemented("return outside of function")),
      Completion::Break(..) => Err(VmError::Unimplemented("break outside of loop")),
      Completion::Continue(..) => Err(VmError::Unimplemented("continue outside of loop")),
    }
  }

}

struct Evaluator<'a> {
  vm: &'a mut Vm,
  env: &'a mut Env,
}

impl<'a> Evaluator<'a> {
  /// Runs one VM "tick".
  ///
  /// ## Tick policy (AST evaluator)
  ///
  /// This interpreter charges **one tick** at the start of every statement evaluation
  /// ([`Evaluator::eval_stmt`]) and every expression evaluation ([`Evaluator::eval_expr`]).
  ///
  /// Some constructs (e.g. `for(;;){}` with an empty body and no condition/update expressions) may
  /// otherwise loop without evaluating any statements/expressions per iteration; those paths tick
  /// explicitly as well.
  #[inline]
  fn tick(&mut self) -> Result<(), VmError> {
    self.vm.tick()
  }

  fn hoist_var_decls(&mut self, heap: &mut Heap, stmts: &[Node<Stmt>]) -> Result<(), VmError> {
    let mut names = HashSet::<String>::new();
    for stmt in stmts {
      self.collect_var_names(&stmt.stx, &mut names)?;
    }
    for name in names {
      self.env.declare_var(heap, &name);
    }
    Ok(())
  }

  fn collect_var_names(&self, stmt: &Stmt, out: &mut HashSet<String>) -> Result<(), VmError> {
    match stmt {
      Stmt::VarDecl(var) => {
        if var.stx.mode != VarDeclMode::Var {
          return Ok(());
        }
        for decl in &var.stx.declarators {
          self.collect_var_names_from_pat_decl(&decl.pattern.stx, out)?;
        }
      }
      Stmt::Block(block) => {
        for stmt in &block.stx.body {
          self.collect_var_names(&stmt.stx, out)?;
        }
      }
      Stmt::If(stmt) => {
        self.collect_var_names(&stmt.stx.consequent.stx, out)?;
        if let Some(alt) = &stmt.stx.alternate {
          self.collect_var_names(&alt.stx, out)?;
        }
      }
      Stmt::Try(stmt) => {
        for s in &stmt.stx.wrapped.stx.body {
          self.collect_var_names(&s.stx, out)?;
        }
        if let Some(catch) = &stmt.stx.catch {
          for s in &catch.stx.body {
            self.collect_var_names(&s.stx, out)?;
          }
        }
        if let Some(finally) = &stmt.stx.finally {
          for s in &finally.stx.body {
            self.collect_var_names(&s.stx, out)?;
          }
        }
      }
      Stmt::While(stmt) => {
        self.collect_var_names(&stmt.stx.body.stx, out)?;
      }
      Stmt::DoWhile(stmt) => {
        self.collect_var_names(&stmt.stx.body.stx, out)?;
      }
      Stmt::ForTriple(stmt) => {
        if let parse_js::ast::stmt::ForTripleStmtInit::Decl(decl) = &stmt.stx.init {
          if decl.stx.mode == VarDeclMode::Var {
            for d in &decl.stx.declarators {
              self.collect_var_names_from_pat_decl(&d.pattern.stx, out)?;
            }
          }
        }
        for s in &stmt.stx.body.stx.body {
          self.collect_var_names(&s.stx, out)?;
        }
      }
      // Skip nested function declarations: their `var` bindings are not hoisted into the current
      // scope.
      Stmt::FunctionDecl(_) => {}

      // TODO: other statement types.
      _ => {}
    }
    Ok(())
  }

  fn collect_var_names_from_pat_decl(
    &self,
    pat_decl: &PatDecl,
    out: &mut HashSet<String>,
  ) -> Result<(), VmError> {
    match &*pat_decl.pat.stx {
      Pat::Id(id) => {
        out.insert(id.stx.name.clone());
        Ok(())
      }
      _ => Err(VmError::Unimplemented("var destructuring patterns")),
    }
  }

  fn eval_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<Completion, VmError> {
    // Root the running completion value so it cannot be collected while evaluating subsequent
    // statements (which may allocate and trigger GC).
    let last_root = scope.heap_mut().add_root(Value::Undefined);
    let mut last_value: Option<Value> = None;

    for stmt in stmts {
      let completion = self.eval_stmt(scope, stmt)?;
      let completion = completion.update_empty(last_value);

      match completion {
        Completion::Normal(v) => {
          if let Some(v) = v {
            last_value = Some(v);
            scope.heap_mut().set_root(last_root, v);
          }
        }
        abrupt => {
          scope.heap_mut().remove_root(last_root);
          return Ok(abrupt);
        }
      }
    }

    scope.heap_mut().remove_root(last_root);
    Ok(Completion::Normal(last_value))
  }

  fn eval_block_stmt(
    &mut self,
    scope: &mut Scope<'_>,
    block: &BlockStmt,
  ) -> Result<Completion, VmError> {
    self.env.push_lexical();
    let result = self.eval_stmt_list(scope, &block.body);
    self.env.pop_lexical(scope.heap_mut());
    result
  }

  fn eval_stmt(&mut self, scope: &mut Scope<'_>, stmt: &Node<Stmt>) -> Result<Completion, VmError> {
    // One tick per statement.
    self.tick()?;

    match &*stmt.stx {
      Stmt::Empty(_) => Ok(Completion::empty()),
      Stmt::Expr(expr_stmt) => self.eval_expr_stmt(scope, &expr_stmt.stx),
      Stmt::VarDecl(var_decl) => self.eval_var_decl(scope, &var_decl.stx),
      Stmt::Block(block) => self.eval_block_stmt(scope, &block.stx),
      Stmt::If(stmt) => self.eval_if(scope, &stmt.stx),
      Stmt::Throw(stmt) => self.eval_throw(scope, &stmt.stx),
      Stmt::Try(stmt) => self.eval_try(scope, &stmt.stx),
      Stmt::Return(stmt) => self.eval_return(scope, &stmt.stx),
      Stmt::While(stmt) => self.eval_while(scope, &stmt.stx),
      Stmt::DoWhile(stmt) => self.eval_do_while(scope, &stmt.stx),
      Stmt::ForTriple(stmt) => self.eval_for_triple(scope, &stmt.stx),
      Stmt::Break(stmt) => {
        if stmt.stx.label.is_some() {
          return Err(VmError::Unimplemented("labelled break"));
        }
        Ok(Completion::Break(None, None))
      }
      Stmt::Continue(stmt) => {
        if stmt.stx.label.is_some() {
          return Err(VmError::Unimplemented("labelled continue"));
        }
        Ok(Completion::Continue(None, None))
      }

      _ => Err(VmError::Unimplemented("statement type")),
    }
  }

  fn eval_expr_stmt(&mut self, scope: &mut Scope<'_>, stmt: &ExprStmt) -> Result<Completion, VmError> {
    let value = self.eval_expr(scope, &stmt.expr)?;
    Ok(Completion::normal(value))
  }

  fn eval_var_decl(&mut self, scope: &mut Scope<'_>, decl: &VarDecl) -> Result<Completion, VmError> {
    match decl.mode {
      VarDeclMode::Var => {
        // `var` bindings are hoisted to `undefined` at function/script entry.
        for declarator in &decl.declarators {
          let Some(init) = &declarator.initializer else {
            continue;
          };
          let name = expect_simple_binding_identifier(&declarator.pattern.stx)?;
          let value = self.eval_expr(scope, init)?;
          self.env.set_var(scope.heap_mut(), name, value)?;
        }
        Ok(Completion::empty())
      }
      VarDeclMode::Let => {
        for declarator in &decl.declarators {
          let name = expect_simple_binding_identifier(&declarator.pattern.stx)?;
          let value = match &declarator.initializer {
            Some(init) => self.eval_expr(scope, init)?,
            None => Value::Undefined,
          };
          self
            .env
            .declare_lexical(scope.heap_mut(), name, true, value)?;
        }
        Ok(Completion::empty())
      }
      VarDeclMode::Const => {
        for declarator in &decl.declarators {
          let name = expect_simple_binding_identifier(&declarator.pattern.stx)?;
          let Some(init) = &declarator.initializer else {
            // TODO: should be a syntax error (early error).
            return Err(VmError::Unimplemented("const without initializer"));
          };
          let value = self.eval_expr(scope, init)?;
          self
            .env
            .declare_lexical(scope.heap_mut(), name, false, value)?;
        }
        Ok(Completion::empty())
      }

      _ => Err(VmError::Unimplemented("var declaration kind")),
    }
  }

  fn eval_if(&mut self, scope: &mut Scope<'_>, stmt: &IfStmt) -> Result<Completion, VmError> {
    let test = self.eval_expr(scope, &stmt.test)?;
    if to_boolean(scope.heap(), test)? {
      self.eval_stmt(scope, &stmt.consequent)
    } else if let Some(alt) = &stmt.alternate {
      self.eval_stmt(scope, alt)
    } else {
      Ok(Completion::empty())
    }
  }

  fn eval_throw(&mut self, scope: &mut Scope<'_>, stmt: &ThrowStmt) -> Result<Completion, VmError> {
    let value = self.eval_expr(scope, &stmt.value)?;
    Ok(Completion::Throw(value))
  }

  fn eval_try(&mut self, scope: &mut Scope<'_>, stmt: &TryStmt) -> Result<Completion, VmError> {
    let mut result = self.eval_block_stmt(scope, &stmt.wrapped.stx)?;

    if matches!(result, Completion::Throw(_)) {
      if let Some(catch) = &stmt.catch {
        let thrown = match result {
          Completion::Throw(v) => v,
          _ => unreachable!(),
        };
        result = self.eval_catch(scope, &catch.stx, thrown)?;
      }
    }

    if let Some(finally) = &stmt.finally {
      // Root the pending completion's value (if any) while evaluating `finally`, which may
      // allocate and trigger GC.
      let pending_root = result.value().map(|v| scope.heap_mut().add_root(v));
      let finally_result = self.eval_block_stmt(scope, &finally.stx)?;
      if let Some(root) = pending_root {
        scope.heap_mut().remove_root(root);
      }

      if finally_result.is_abrupt() {
        return Ok(finally_result);
      }

      result = result.update_empty(finally_result.value());
    }

    Ok(result)
  }

  fn eval_catch(
    &mut self,
    scope: &mut Scope<'_>,
    catch: &CatchBlock,
    thrown: Value,
  ) -> Result<Completion, VmError> {
    self.env.push_lexical();
    if let Some(param) = &catch.parameter {
      self.bind_catch_param(scope.heap_mut(), &param.stx, thrown)?;
    }
    let result = self.eval_stmt_list(scope, &catch.body);
    self.env.pop_lexical(scope.heap_mut());
    result
  }

  fn bind_catch_param(
    &mut self,
    heap: &mut Heap,
    param: &PatDecl,
    thrown: Value,
  ) -> Result<(), VmError> {
    match &*param.pat.stx {
      Pat::Id(id) => self
        .env
        .declare_lexical(heap, &id.stx.name, true, thrown),
      _ => Err(VmError::Unimplemented("destructuring catch parameter")),
    }
  }

  fn eval_return(&mut self, scope: &mut Scope<'_>, stmt: &ReturnStmt) -> Result<Completion, VmError> {
    let value = match &stmt.value {
      Some(expr) => self.eval_expr(scope, expr)?,
      None => Value::Undefined,
    };
    Ok(Completion::Return(value))
  }

  fn eval_while(&mut self, scope: &mut Scope<'_>, stmt: &WhileStmt) -> Result<Completion, VmError> {
    loop {
      let test = self.eval_expr(scope, &stmt.condition)?;
      if !to_boolean(scope.heap(), test)? {
        break;
      }

      match self.eval_stmt(scope, &stmt.body)? {
        Completion::Normal(_) => {}
        Completion::Continue(None, _) => continue,
        Completion::Break(None, _) => break,
        other => return Ok(other),
      }
    }
    Ok(Completion::empty())
  }

  fn eval_do_while(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &DoWhileStmt,
  ) -> Result<Completion, VmError> {
    loop {
      match self.eval_stmt(scope, &stmt.body)? {
        Completion::Normal(_) => {}
        Completion::Continue(None, _) => {}
        Completion::Break(None, _) => break,
        other => return Ok(other),
      }

      let test = self.eval_expr(scope, &stmt.condition)?;
      if !to_boolean(scope.heap(), test)? {
        break;
      }
    }
    Ok(Completion::empty())
  }

  fn eval_for_triple(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForTripleStmt,
  ) -> Result<Completion, VmError> {
    // Note: this is intentionally minimal and does not implement per-iteration lexical
    // environments for `let`/`const`.
    match &stmt.init {
      parse_js::ast::stmt::ForTripleStmtInit::None => {}
      parse_js::ast::stmt::ForTripleStmtInit::Expr(expr) => {
        let _ = self.eval_expr(scope, expr)?;
      }
      parse_js::ast::stmt::ForTripleStmtInit::Decl(decl) => {
        let _ = self.eval_var_decl(scope, &decl.stx)?;
      }
    }

    // Most `for` loop iterations are naturally budgeted by ticks in:
    // - condition/update expression evaluation (if present), and/or
    // - evaluating at least one statement in the loop body.
    //
    // However, `for(;;){}` executes no statements/expressions per iteration. Tick explicitly to
    // ensure budgets/interrupts are still observed.
    let needs_explicit_iter_tick =
      stmt.cond.is_none() && stmt.post.is_none() && stmt.body.stx.body.is_empty();

    loop {
      if needs_explicit_iter_tick {
        self.tick()?;
      }

      if let Some(cond) = &stmt.cond {
        let test = self.eval_expr(scope, cond)?;
        if !to_boolean(scope.heap(), test)? {
          break;
        }
      }

      match self.eval_for_body(scope, &stmt.body.stx)? {
        Completion::Normal(_) => {}
        Completion::Continue(None, _) => {}
        Completion::Break(None, _) => break,
        other => return Ok(other),
      }

      if let Some(post) = &stmt.post {
        let _ = self.eval_expr(scope, post)?;
      }
    }

    Ok(Completion::empty())
  }

  fn eval_for_body(&mut self, scope: &mut Scope<'_>, body: &ForBody) -> Result<Completion, VmError> {
    self.eval_stmt_list(scope, &body.body)
  }

  fn eval_expr(&mut self, scope: &mut Scope<'_>, expr: &Node<Expr>) -> Result<Value, VmError> {
    // One tick per expression.
    self.tick()?;

    match &*expr.stx {
      Expr::LitStr(node) => self.eval_lit_str(scope, node),
      Expr::LitNum(node) => self.eval_lit_num(&node.stx),
      Expr::LitBool(node) => self.eval_lit_bool(&node.stx),
      Expr::LitNull(_) => Ok(Value::Null),
      Expr::Id(node) => self.eval_id(scope, &node.stx),
      Expr::Binary(node) => self.eval_binary(scope, &node.stx),

      // Patterns sometimes show up in expression position (e.g. assignment targets). We only
      // support simple identifier patterns for now.
      Expr::IdPat(node) => self.eval_id_pat(scope, &node.stx),

      _ => Err(VmError::Unimplemented("expression type")),
    }
  }

  fn eval_lit_str(&mut self, scope: &mut Scope<'_>, node: &Node<LitStrExpr>) -> Result<Value, VmError> {
    let s = match literal_string_code_units(&node.assoc) {
      Some(units) => scope.alloc_string_from_code_units(units)?,
      None => scope.alloc_string_from_utf8(&node.stx.value)?,
    };
    Ok(Value::String(s))
  }

  fn eval_lit_num(&self, expr: &LitNumExpr) -> Result<Value, VmError> {
    Ok(Value::Number(expr.value.0))
  }

  fn eval_lit_bool(&self, expr: &LitBoolExpr) -> Result<Value, VmError> {
    Ok(Value::Bool(expr.value))
  }

  fn eval_id(&self, scope: &mut Scope<'_>, expr: &IdExpr) -> Result<Value, VmError> {
    self
      .env
      .get(scope.heap(), &expr.name)
      .ok_or(VmError::Unimplemented("unbound identifier"))
  }

  fn eval_id_pat(&self, scope: &mut Scope<'_>, expr: &IdPat) -> Result<Value, VmError> {
    self
      .env
      .get(scope.heap(), &expr.name)
      .ok_or(VmError::Unimplemented("unbound identifier"))
  }

  fn eval_binary(&mut self, scope: &mut Scope<'_>, expr: &BinaryExpr) -> Result<Value, VmError> {
    match expr.operator {
      OperatorName::StrictEquality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(strict_equal(rhs_scope.heap(), left, right)?))
      }
      OperatorName::Assignment => {
        // `=` assignment expression.
        let name = match &*expr.left.stx {
          Expr::Id(id) => id.stx.name.as_str(),
          Expr::IdPat(id) => id.stx.name.as_str(),
          _ => return Err(VmError::Unimplemented("assignment target")),
        };
        let value = self.eval_expr(scope, &expr.right)?;
        self.env.set(scope.heap_mut(), name, value)?;
        Ok(value)
      }
      _ => Err(VmError::Unimplemented("binary operator")),
    }
  }
}

fn expect_simple_binding_identifier<'a>(pat_decl: &'a PatDecl) -> Result<&'a str, VmError> {
  match &*pat_decl.pat.stx {
    Pat::Id(id) => Ok(&id.stx.name),
    _ => Err(VmError::Unimplemented("destructuring patterns")),
  }
}

fn to_boolean(heap: &Heap, value: Value) -> Result<bool, VmError> {
  Ok(match value {
    Value::Undefined | Value::Null => false,
    Value::Bool(b) => b,
    Value::Number(n) => n != 0.0 && !n.is_nan(),
    Value::String(s) => !heap.get_string(s)?.as_code_units().is_empty(),
    Value::Symbol(_) | Value::Object(_) => true,
  })
}

fn strict_equal(heap: &Heap, a: Value, b: Value) -> Result<bool, VmError> {
  Ok(match (a, b) {
    (Value::Undefined, Value::Undefined) => true,
    (Value::Null, Value::Null) => true,
    (Value::Bool(x), Value::Bool(y)) => x == y,
    (Value::Number(x), Value::Number(y)) => x == y,
    (Value::String(x), Value::String(y)) => heap.get_string(x)? == heap.get_string(y)?,
    (Value::Symbol(x), Value::Symbol(y)) => x == y,
    (Value::Object(x), Value::Object(y)) => x == y,
    _ => false,
  })
}
