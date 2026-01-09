use crate::ops::{add_operator, abstract_equality, to_number};
use crate::{
  EnvRootId, GcEnv, GcObject, GcString, Heap, PropertyDescriptor, PropertyKey, PropertyKind, Realm,
  RootId, Scope, Value, Vm, VmError, VmJobContext,
};
use diagnostics::FileId;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::lit::{
  LitArrElem, LitArrExpr, LitBoolExpr, LitNumExpr, LitObjExpr, LitStrExpr,
};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{BinaryExpr, CondExpr, Expr, IdExpr, UnaryExpr};
use parse_js::ast::node::{literal_string_code_units, Node};
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  BlockStmt, CatchBlock, DoWhileStmt, ExprStmt, ForBody, ForTripleStmt, IfStmt, LabelStmt,
  ReturnStmt, Stmt, SwitchStmt, ThrowStmt, TryStmt, WhileStmt,
};
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::collections::HashSet;

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

fn global_var_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: true,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

#[derive(Debug)]
struct RuntimeEnv {
  global_object: GcObject,
  lexical_env: GcEnv,
  lexical_root: EnvRootId,
}

impl RuntimeEnv {
  fn new(heap: &mut Heap, global_object: GcObject) -> Result<Self, VmError> {
    // Root the global object across env allocation in case it triggers GC.
    let mut scope = heap.scope();
    scope.push_root(Value::Object(global_object));

    let lexical_env = scope.env_create(None)?;
    let lexical_root = scope.heap_mut().add_env_root(lexical_env);

    Ok(Self {
      global_object,
      lexical_env,
      lexical_root,
    })
  }

  fn teardown(&mut self, heap: &mut Heap) {
    heap.remove_env_root(self.lexical_root);
  }

  fn set_lexical_env(&mut self, heap: &mut Heap, env: GcEnv) {
    self.lexical_env = env;
    heap.set_env_root(self.lexical_root, env);
  }

  fn resolve_lexical_binding(&self, heap: &Heap, name: &str) -> Result<Option<GcEnv>, VmError> {
    let mut current = Some(self.lexical_env);
    while let Some(env) = current {
      if heap.env_has_binding(env, name)? {
        return Ok(Some(env));
      }
      current = heap.env_outer(env)?;
    }
    Ok(None)
  }

  fn declare_var(&mut self, scope: &mut Scope<'_>, name: &str) -> Result<(), VmError> {
    let global_object = self.global_object;

    // Root the global object across property-key allocation in case it triggers GC.
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(global_object));

    let key = PropertyKey::from_string(key_scope.alloc_string(name)?);
    if key_scope
      .heap()
      .object_get_own_property(global_object, &key)?
      .is_some()
    {
      return Ok(());
    }

    key_scope.define_property(global_object, key, global_var_desc(Value::Undefined))?;
    Ok(())
  }

  fn get(&self, vm: &mut Vm, scope: &mut Scope<'_>, name: &str) -> Result<Option<Value>, VmError> {
    if let Some(env) = self.resolve_lexical_binding(scope.heap(), name)? {
      return Ok(Some(
        scope.heap().env_get_binding_value(env, name, false)?,
      ));
    }

    // Fall back to global object property lookup.
    let global_object = self.global_object;
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(global_object));
    let key_s = key_scope.alloc_string(name)?;
    key_scope.push_root(Value::String(key_s));
    let key = PropertyKey::from_string(key_s);

    // Distinguish between a missing property (unbound identifier) and a present property whose
    // value is actually `undefined`.
    if !key_scope.ordinary_has_property(global_object, key)? {
      return Ok(None);
    }

    let receiver = Value::Object(global_object);
    Ok(Some(key_scope.ordinary_get(vm, global_object, key, receiver)?))
  }

  fn set(
    &mut self,
    scope: &mut Scope<'_>,
    name: &str,
    value: Value,
    strict: bool,
  ) -> Result<(), VmError> {
    if let Some(env) = self.resolve_lexical_binding(scope.heap(), name)? {
      return scope
        .heap_mut()
        .env_set_mutable_binding(env, name, value, strict);
    }

    // Assignment to global (var) bindings is backed by the global object.
    let global_object = self.global_object;
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(global_object));
    // Root `value` across key allocation and property definition in case they trigger GC.
    key_scope.push_root(value);
    let key = PropertyKey::from_string(key_scope.alloc_string(name)?);

    let has_binding = key_scope.ordinary_has_property(global_object, key)?;
    if !has_binding {
      if strict {
        // TODO: Should throw a ReferenceError.
        return Err(VmError::Unimplemented(
          "assignment to undeclared identifier in strict mode",
        ));
      }

      // Sloppy-mode: create a new global `var` property.
      key_scope.define_property(global_object, key, global_var_desc(value))?;
      return Ok(());
    }

    if let Some(desc) = key_scope
      .heap()
      .object_get_own_property(global_object, &key)?
    {
      match desc.kind {
        PropertyKind::Data { writable: true, .. } => {
          key_scope
            .heap_mut()
            .object_set_existing_data_property_value(global_object, &key, value)?;
          return Ok(());
        }
        PropertyKind::Data {
          writable: false, ..
        } => {
          // TODO: Should throw a TypeError in strict mode; sloppy-mode is a no-op.
          return Err(VmError::Unimplemented(
            "assignment to non-writable global property",
          ));
        }
        PropertyKind::Accessor { .. } => {
          return Err(VmError::Unimplemented("accessor properties"));
        }
      }
    }

    // Property is inherited through the prototype chain: define an own data property.
    key_scope.define_property(global_object, key, global_var_desc(value))?;
    Ok(())
  }

  fn set_var(&mut self, scope: &mut Scope<'_>, name: &str, value: Value) -> Result<(), VmError> {
    // `var` declarations always assign to the global var environment (the global object), even when
    // a lexical binding shadows the identifier (e.g. a `catch(e)` parameter).
    //
    // Root the initializer value across global-binding creation in case it triggers GC.
    let mut outer_scope = scope.reborrow();
    outer_scope.push_root(value);
    self.declare_var(&mut outer_scope, name)?;

    let global_object = self.global_object;
    let mut key_scope = outer_scope.reborrow();
    key_scope.push_root(Value::Object(global_object));
    key_scope.push_root(value);
    let key = PropertyKey::from_string(key_scope.alloc_string(name)?);

    if let Some(desc) = key_scope
      .heap()
      .object_get_own_property(global_object, &key)?
    {
      match desc.kind {
        PropertyKind::Data { writable: true, .. } => {
          key_scope
            .heap_mut()
            .object_set_existing_data_property_value(global_object, &key, value)?;
          return Ok(());
        }
        PropertyKind::Data {
          writable: false, ..
        } => {
          return Err(VmError::Unimplemented(
            "assignment to non-writable global property",
          ));
        }
        PropertyKind::Accessor { .. } => {
          return Err(VmError::Unimplemented("accessor properties"));
        }
      }
    }

    // If the binding was inherited through the prototype chain, define an own data property.
    key_scope.define_property(global_object, key, global_var_desc(value))?;
    Ok(())
  }
}

/// An (early, incomplete) AST-interpreting execution engine for `parse-js` syntax trees.
pub struct JsRuntime {
  pub vm: Vm,
  pub heap: Heap,
  realm: Realm,
  env: RuntimeEnv,
}

impl JsRuntime {
  pub fn new(vm: Vm, heap: Heap) -> Result<Self, VmError> {
    let mut vm = vm;
    let mut heap = heap;
    let realm = Realm::new(&mut vm, &mut heap)?;
    let env = RuntimeEnv::new(&mut heap, realm.global_object())?;
    Ok(Self {
      vm,
      heap,
      realm,
      env,
    })
  }

  pub fn realm(&self) -> &Realm {
    &self.realm
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

    let mut scope = self.heap.scope();
    let mut evaluator = Evaluator {
      vm: &mut self.vm,
      env: &mut self.env,
    };

    evaluator.hoist_var_decls(&mut scope, &top.stx.body)?;
    let global_lex = evaluator.env.lexical_env;
    evaluator.hoist_lexical_decls_in_stmt_list(&mut scope, global_lex, &top.stx.body)?;

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

impl Drop for JsRuntime {
  fn drop(&mut self) {
    // Unregister persistent roots created by global lexical bindings and the realm. This keeps heap
    // reuse in tests/embeddings from accumulating roots and satisfies `Realm`'s debug assertion.
    self.env.teardown(&mut self.heap);
    self.realm.teardown(&mut self.heap);
  }
}

impl VmJobContext for JsRuntime {
  fn call(&mut self, callee: Value, this: Value, args: &[Value]) -> Result<Value, VmError> {
    // Borrow-split `vm` and `heap` so we can hold a `Scope` while calling into the VM.
    let vm = &mut self.vm;
    let heap = &mut self.heap;
    let mut scope = heap.scope();
    vm.call(&mut scope, callee, this, args)
  }

  fn construct(
    &mut self,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let vm = &mut self.vm;
    let heap = &mut self.heap;
    let mut scope = heap.scope();
    vm.construct(&mut scope, callee, args, new_target)
  }

  fn add_root(&mut self, value: Value) -> RootId {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.remove_root(id)
  }
}

struct Evaluator<'a> {
  vm: &'a mut Vm,
  env: &'a mut RuntimeEnv,
}

#[derive(Clone, Copy, Debug)]
enum Reference<'a> {
  Binding(&'a str),
  Property { object: GcObject, key: PropertyKey },
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

  fn hoist_var_decls(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    let mut names = HashSet::<String>::new();
    for stmt in stmts {
      self.collect_var_names(&stmt.stx, &mut names)?;
    }
    for name in names {
      self.env.declare_var(scope, &name)?;
    }
    Ok(())
  }

  fn hoist_lexical_decls_in_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    for stmt in stmts {
      let Stmt::VarDecl(var) = &*stmt.stx else {
        continue;
      };

      match var.stx.mode {
        VarDeclMode::Let => {
          for declarator in &var.stx.declarators {
            let name = expect_simple_binding_identifier(&declarator.pattern.stx)?;
            scope.env_create_mutable_binding(env, name)?;
          }
        }
        VarDeclMode::Const => {
          for declarator in &var.stx.declarators {
            let name = expect_simple_binding_identifier(&declarator.pattern.stx)?;
            scope.env_create_immutable_binding(env, name)?;
          }
        }
        _ => {}
      }
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
      Stmt::Label(stmt) => {
        self.collect_var_names(&stmt.stx.statement.stx, out)?;
      }
      Stmt::Switch(stmt) => {
        for branch in &stmt.stx.branches {
          for s in &branch.stx.body {
            self.collect_var_names(&s.stx, out)?;
          }
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
    let outer = self.env.lexical_env;
    let block_env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), block_env);

    let result = self
      .hoist_lexical_decls_in_stmt_list(scope, block_env, &block.body)
      .and_then(|_| self.eval_stmt_list(scope, &block.body));

    self.env.set_lexical_env(scope.heap_mut(), outer);
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
      Stmt::While(stmt) => self.eval_while(scope, &stmt.stx, None),
      Stmt::DoWhile(stmt) => self.eval_do_while(scope, &stmt.stx, None),
      Stmt::ForTriple(stmt) => self.eval_for_triple(scope, &stmt.stx, None),
      Stmt::Switch(stmt) => self.eval_switch(scope, &stmt.stx),
      Stmt::Label(stmt) => self.eval_label(scope, &stmt.stx),
      Stmt::Break(stmt) => Ok(Completion::Break(stmt.stx.label.clone(), None)),
      Stmt::Continue(stmt) => Ok(Completion::Continue(stmt.stx.label.clone(), None)),

      _ => Err(VmError::Unimplemented("statement type")),
    }
  }

  fn eval_expr_stmt(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ExprStmt,
  ) -> Result<Completion, VmError> {
    let value = self.eval_expr(scope, &stmt.expr)?;
    Ok(Completion::normal(value))
  }

  fn eval_var_decl(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &VarDecl,
  ) -> Result<Completion, VmError> {
    match decl.mode {
      VarDeclMode::Var => {
        // `var` bindings are hoisted to `undefined` at function/script entry.
        for declarator in &decl.declarators {
          let Some(init) = &declarator.initializer else {
            continue;
          };
          let name = expect_simple_binding_identifier(&declarator.pattern.stx)?;
          let value = self.eval_expr(scope, init)?;
          self.env.set_var(scope, name, value)?;
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

          if !scope.heap().env_has_binding(self.env.lexical_env, name)? {
            // Non-block statement contexts may not have performed lexical hoisting yet.
            scope.env_create_mutable_binding(self.env.lexical_env, name)?;
          }
          scope
            .heap_mut()
            .env_initialize_binding(self.env.lexical_env, name, value)?;
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

          if !scope.heap().env_has_binding(self.env.lexical_env, name)? {
            scope.env_create_immutable_binding(self.env.lexical_env, name)?;
          }
          scope
            .heap_mut()
            .env_initialize_binding(self.env.lexical_env, name, value)?;
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
    let outer = self.env.lexical_env;
    let catch_env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), catch_env);

    let result = {
      // Root the thrown value across catch binding instantiation, which may allocate.
      let mut catch_scope = scope.reborrow();
      catch_scope.push_root(thrown);

      self
        .hoist_lexical_decls_in_stmt_list(&mut catch_scope, catch_env, &catch.body)
        .and_then(|_| {
          if let Some(param) = &catch.parameter {
            self.bind_catch_param(&mut catch_scope, &param.stx, thrown, catch_env)?;
          }
          self.eval_stmt_list(&mut catch_scope, &catch.body)
        })
    };

    self.env.set_lexical_env(scope.heap_mut(), outer);
    result
  }

  fn bind_catch_param(
    &mut self,
    scope: &mut Scope<'_>,
    param: &PatDecl,
    thrown: Value,
    env: GcEnv,
  ) -> Result<(), VmError> {
    match &*param.pat.stx {
      Pat::Id(id) => {
        let name = id.stx.name.as_str();
        if !scope.heap().env_has_binding(env, name)? {
          scope.env_create_mutable_binding(env, name)?;
        }
        scope.heap_mut().env_initialize_binding(env, name, thrown)?;
        Ok(())
      }
      _ => Err(VmError::Unimplemented("destructuring catch parameter")),
    }
  }

  fn eval_return(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ReturnStmt,
  ) -> Result<Completion, VmError> {
    let value = match &stmt.value {
      Some(expr) => self.eval_expr(scope, expr)?,
      None => Value::Undefined,
    };
    Ok(Completion::Return(value))
  }

  fn eval_while(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &WhileStmt,
    active_label: Option<&str>,
  ) -> Result<Completion, VmError> {
    loop {
      let test = self.eval_expr(scope, &stmt.condition)?;
      if !to_boolean(scope.heap(), test)? {
        break;
      }

      match self.eval_stmt(scope, &stmt.body)? {
        Completion::Normal(_) => {}
        Completion::Continue(None, _) => continue,
        Completion::Continue(Some(ref l), _) if active_label == Some(l.as_str()) => continue,
        Completion::Break(None, _) => break,
        Completion::Break(Some(ref l), _) if active_label == Some(l.as_str()) => break,
        other => return Ok(other),
      }
    }
    Ok(Completion::empty())
  }

  fn eval_do_while(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &DoWhileStmt,
    active_label: Option<&str>,
  ) -> Result<Completion, VmError> {
    loop {
      match self.eval_stmt(scope, &stmt.body)? {
        Completion::Normal(_) => {}
        Completion::Continue(None, _) => {}
        Completion::Continue(Some(ref l), _) if active_label == Some(l.as_str()) => {}
        Completion::Break(None, _) => break,
        Completion::Break(Some(ref l), _) if active_label == Some(l.as_str()) => break,
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
    active_label: Option<&str>,
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
        Completion::Continue(Some(ref l), _) if active_label == Some(l.as_str()) => {}
        Completion::Break(None, _) => break,
        Completion::Break(Some(ref l), _) if active_label == Some(l.as_str()) => break,
        other => return Ok(other),
      }

      if let Some(post) = &stmt.post {
        let _ = self.eval_expr(scope, post)?;
      }
    }

    Ok(Completion::empty())
  }

  fn eval_for_body(
    &mut self,
    scope: &mut Scope<'_>,
    body: &ForBody,
  ) -> Result<Completion, VmError> {
    self.eval_stmt_list(scope, &body.body)
  }

  fn eval_label(&mut self, scope: &mut Scope<'_>, stmt: &LabelStmt) -> Result<Completion, VmError> {
    let label = stmt.name.as_str();

    // `continue <label>` is only valid when the labelled statement is a loop. We support labelled
    // loops by passing the active label through to the loop evaluator.
    let completion = match &*stmt.statement.stx {
      Stmt::While(inner) => {
        // One tick for evaluating the labelled loop statement itself (normally done by
        // `eval_stmt`).
        self.tick()?;
        self.eval_while(scope, &inner.stx, Some(label))?
      }
      Stmt::DoWhile(inner) => {
        self.tick()?;
        self.eval_do_while(scope, &inner.stx, Some(label))?
      }
      Stmt::ForTriple(inner) => {
        self.tick()?;
        self.eval_for_triple(scope, &inner.stx, Some(label))?
      }
      // TODO: ForIn/ForOf.
      _ => self.eval_stmt(scope, &stmt.statement)?,
    };

    match completion {
      Completion::Break(Some(target), v) => {
        if target == label {
          Ok(Completion::Normal(v))
        } else {
          Ok(Completion::Break(Some(target), v))
        }
      }
      Completion::Continue(Some(target), v) => {
        if target == label {
          Err(VmError::Unimplemented("continue to non-loop label"))
        } else {
          Ok(Completion::Continue(Some(target), v))
        }
      }
      other => Ok(other),
    }
  }

  fn eval_switch(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &SwitchStmt,
  ) -> Result<Completion, VmError> {
    let discriminant = self.eval_expr(scope, &stmt.test)?;
    let mut switch_scope = scope.reborrow();
    switch_scope.push_root(discriminant);

    let outer = self.env.lexical_env;
    let switch_env = switch_scope.env_create(Some(outer))?;
    self
      .env
      .set_lexical_env(switch_scope.heap_mut(), switch_env);

    let result = (|| -> Result<Completion, VmError> {
      // `switch` shares one lexical scope across all case clauses.
      for branch in &stmt.branches {
        self.hoist_lexical_decls_in_stmt_list(&mut switch_scope, switch_env, &branch.stx.body)?;
      }

      // Select the first matching case clause, or `default` if no clause matches.
      let mut default_idx: Option<usize> = None;
      let mut start_idx: Option<usize> = None;
      for (i, branch) in stmt.branches.iter().enumerate() {
        match &branch.stx.case {
          None => {
            if default_idx.is_none() {
              default_idx = Some(i);
            }
          }
          Some(case_expr) => {
            let case_value = self.eval_expr(&mut switch_scope, case_expr)?;
            if strict_equal(switch_scope.heap(), discriminant, case_value)? {
              start_idx = Some(i);
              break;
            }
          }
        }
      }
      let Some(start_idx) = start_idx.or(default_idx) else {
        return Ok(Completion::empty());
      };

      // Evaluate statement lists from the selected clause until a break or abrupt completion.
      let last_root = switch_scope.heap_mut().add_root(Value::Undefined);
      let mut last_value: Option<Value> = None;

      for branch in stmt.branches.iter().skip(start_idx) {
        for stmt in &branch.stx.body {
          let completion = self.eval_stmt(&mut switch_scope, stmt)?;
          let completion = completion.update_empty(last_value);
          match completion {
            Completion::Normal(v) => {
              if let Some(v) = v {
                last_value = Some(v);
                switch_scope.heap_mut().set_root(last_root, v);
              }
            }
            abrupt => {
              switch_scope.heap_mut().remove_root(last_root);
              return Ok(abrupt);
            }
          }
        }
      }

      switch_scope.heap_mut().remove_root(last_root);
      Ok(Completion::Normal(last_value))
    })();

    self.env.set_lexical_env(switch_scope.heap_mut(), outer);
    let completion = result?;
    Ok(match completion {
      Completion::Break(None, v) => Completion::Normal(v),
      other => other,
    })
  }

  fn eval_expr(&mut self, scope: &mut Scope<'_>, expr: &Node<Expr>) -> Result<Value, VmError> {
    // One tick per expression.
    self.tick()?;

    match &*expr.stx {
      Expr::LitStr(node) => self.eval_lit_str(scope, node),
      Expr::LitNum(node) => self.eval_lit_num(&node.stx),
      Expr::LitBool(node) => self.eval_lit_bool(&node.stx),
      Expr::LitNull(_) => Ok(Value::Null),
      Expr::LitArr(node) => self.eval_lit_arr(scope, &node.stx),
      Expr::LitObj(node) => self.eval_lit_obj(scope, &node.stx),
      Expr::This(_) => Ok(Value::Object(self.env.global_object)),
      Expr::Id(node) => self.eval_id(scope, &node.stx),
      Expr::Member(_) | Expr::ComputedMember(_) => {
        let reference = self.eval_reference(scope, expr)?;
        self.get_value_from_reference(scope, &reference)
      }
      Expr::Unary(node) => self.eval_unary(scope, &node.stx),
      Expr::Binary(node) => self.eval_binary(scope, &node.stx),
      Expr::Cond(node) => self.eval_cond(scope, &node.stx),

      // Patterns sometimes show up in expression position (e.g. assignment targets). We only
      // support simple identifier patterns for now.
      Expr::IdPat(node) => self.eval_id_pat(scope, &node.stx),

      _ => Err(VmError::Unimplemented("expression type")),
    }
  }

  fn eval_reference<'b>(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &'b Node<Expr>,
  ) -> Result<Reference<'b>, VmError> {
    match &*expr.stx {
      Expr::Id(id) => Ok(Reference::Binding(&id.stx.name)),
      Expr::IdPat(id) => Ok(Reference::Binding(&id.stx.name)),
      Expr::Member(member) => {
        if member.stx.optional_chaining {
          return Err(VmError::Unimplemented("optional chaining member access"));
        }
        let object = self.eval_expr(scope, &member.stx.left)?;
        let Value::Object(object) = object else {
          return Err(VmError::Unimplemented("member access on non-object"));
        };
        let mut key_scope = scope.reborrow();
        key_scope.push_root(Value::Object(object));
        let key_s = key_scope.alloc_string(&member.stx.right)?;
        Ok(Reference::Property {
          object,
          key: PropertyKey::from_string(key_s),
        })
      }
      Expr::ComputedMember(member) => {
        if member.stx.optional_chaining {
          return Err(VmError::Unimplemented(
            "optional chaining computed member access",
          ));
        }
        let object = self.eval_expr(scope, &member.stx.object)?;
        let Value::Object(object) = object else {
          return Err(VmError::Unimplemented("computed member access on non-object"));
        };
        let mut key_scope = scope.reborrow();
        key_scope.push_root(Value::Object(object));
        let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
        key_scope.push_root(member_value);
        let key = key_scope.heap_mut().to_property_key(member_value)?;
        Ok(Reference::Property { object, key })
      }
      _ => Err(VmError::Unimplemented("expression is not a reference")),
    }
  }

  fn root_reference(&self, scope: &mut Scope<'_>, reference: &Reference<'_>) {
    let Reference::Property { object, key } = *reference else {
      return;
    };
    scope.push_root(Value::Object(object));
    match key {
      PropertyKey::String(s) => scope.push_root(Value::String(s)),
      PropertyKey::Symbol(s) => scope.push_root(Value::Symbol(s)),
    };
  }

  fn get_value_from_reference(
    &mut self,
    scope: &mut Scope<'_>,
    reference: &Reference<'_>,
  ) -> Result<Value, VmError> {
    match *reference {
      Reference::Binding(name) => self
        .env
        .get(self.vm, scope, name)?
        .ok_or(VmError::Unimplemented("unbound identifier")),
      Reference::Property { object, key } => {
        let mut get_scope = scope.reborrow();
        self.root_reference(&mut get_scope, reference);
        get_scope.ordinary_get(self.vm, object, key, Value::Object(object))
      }
    }
  }

  fn put_value_to_reference(
    &mut self,
    scope: &mut Scope<'_>,
    reference: &Reference<'_>,
    value: Value,
  ) -> Result<(), VmError> {
    match *reference {
      Reference::Binding(name) => self.env.set(scope, name, value, false),
      Reference::Property { object, key } => {
        let ok = scope.ordinary_set(self.vm, object, key, value, Value::Object(object))?;
        if ok {
          Ok(())
        } else {
          Err(VmError::Unimplemented("OrdinarySet returned false"))
        }
      }
    }
  }

  fn eval_lit_str(
    &mut self,
    scope: &mut Scope<'_>,
    node: &Node<LitStrExpr>,
  ) -> Result<Value, VmError> {
    let s = alloc_string_from_lit_str(scope, node)?;
    Ok(Value::String(s))
  }

  fn eval_lit_num(&self, expr: &LitNumExpr) -> Result<Value, VmError> {
    Ok(Value::Number(expr.value.0))
  }

  fn eval_lit_bool(&self, expr: &LitBoolExpr) -> Result<Value, VmError> {
    Ok(Value::Bool(expr.value))
  }

  fn eval_lit_arr(&mut self, scope: &mut Scope<'_>, expr: &LitArrExpr) -> Result<Value, VmError> {
    let mut arr_scope = scope.reborrow();
    let arr = arr_scope.alloc_object()?;
    arr_scope.push_root(Value::Object(arr));

    for (idx, elem) in expr.elements.iter().enumerate() {
      match elem {
        LitArrElem::Empty => {}
        LitArrElem::Rest(_) => return Err(VmError::Unimplemented("array spread")),
        LitArrElem::Single(elem_expr) => {
          let mut elem_scope = arr_scope.reborrow();
          let value = self.eval_expr(&mut elem_scope, elem_expr)?;
          elem_scope.push_root(value);
          let key_s = elem_scope.alloc_string(&idx.to_string())?;
          elem_scope.push_root(Value::String(key_s));
          let key = PropertyKey::from_string(key_s);
          let ok = elem_scope.create_data_property(arr, key, value)?;
          if !ok {
            return Err(VmError::Unimplemented("CreateDataProperty returned false"));
          }
        }
      }
    }

    let length_key_s = arr_scope.alloc_string("length")?;
    let length_desc = PropertyDescriptor {
      enumerable: false,
      configurable: false,
      kind: PropertyKind::Data {
        value: Value::Number(expr.elements.len() as f64),
        writable: true,
      },
    };
    arr_scope.define_property(arr, PropertyKey::from_string(length_key_s), length_desc)?;

    Ok(Value::Object(arr))
  }

  fn eval_lit_obj(&mut self, scope: &mut Scope<'_>, expr: &LitObjExpr) -> Result<Value, VmError> {
    let mut obj_scope = scope.reborrow();
    let obj = obj_scope.alloc_object()?;
    obj_scope.push_root(Value::Object(obj));

    for member in &expr.members {
      let mut member_scope = obj_scope.reborrow();
      let member = &member.stx.typ;

      match member {
        ObjMemberType::Valued { key, val } => {
          let key = match key {
            ClassOrObjKey::Direct(direct) => {
              let key_s = member_scope.alloc_string(&direct.stx.key)?;
              PropertyKey::from_string(key_s)
            }
            ClassOrObjKey::Computed(expr) => {
              let value = self.eval_expr(&mut member_scope, expr)?;
              member_scope.push_root(value);
              member_scope.heap_mut().to_property_key(value)?
            }
          };

          match key {
            PropertyKey::String(s) => member_scope.push_root(Value::String(s)),
            PropertyKey::Symbol(s) => member_scope.push_root(Value::Symbol(s)),
          };

          let ClassOrObjVal::Prop(Some(value_expr)) = val else {
            return Err(VmError::Unimplemented("object literal member"));
          };
          let value = self.eval_expr(&mut member_scope, value_expr)?;
          member_scope.push_root(value);
          let ok = member_scope.create_data_property(obj, key, value)?;
          if !ok {
            return Err(VmError::Unimplemented("CreateDataProperty returned false"));
          }
        }
        ObjMemberType::Shorthand { id } => {
          let key_s = member_scope.alloc_string(&id.stx.name)?;
          member_scope.push_root(Value::String(key_s));
          let key = PropertyKey::from_string(key_s);
          let value = self.eval_id(&mut member_scope, &id.stx)?;
          member_scope.push_root(value);
          let ok = member_scope.create_data_property(obj, key, value)?;
          if !ok {
            return Err(VmError::Unimplemented("CreateDataProperty returned false"));
          }
        }
        ObjMemberType::Rest { .. } => return Err(VmError::Unimplemented("object spread")),
      }
    }

    Ok(Value::Object(obj))
  }

  fn eval_id(&mut self, scope: &mut Scope<'_>, expr: &IdExpr) -> Result<Value, VmError> {
    self.env.get(self.vm, scope, &expr.name)?
      .ok_or(VmError::Unimplemented("unbound identifier"))
  }

  fn eval_id_pat(&mut self, scope: &mut Scope<'_>, expr: &IdPat) -> Result<Value, VmError> {
    self.env.get(self.vm, scope, &expr.name)?
      .ok_or(VmError::Unimplemented("unbound identifier"))
  }

  fn eval_unary(&mut self, scope: &mut Scope<'_>, expr: &UnaryExpr) -> Result<Value, VmError> {
    match expr.operator {
      OperatorName::LogicalNot => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        Ok(Value::Bool(!to_boolean(scope.heap(), argument)?))
      }
      OperatorName::UnaryPlus => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        Ok(Value::Number(to_number(scope.heap_mut(), argument)?))
      }
      OperatorName::UnaryNegation => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        Ok(Value::Number(-to_number(scope.heap_mut(), argument)?))
      }
      OperatorName::Typeof => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        let t = typeof_name(scope.heap(), argument)?;
        let s = scope.alloc_string(t)?;
        Ok(Value::String(s))
      }
      OperatorName::Void => {
        let _ = self.eval_expr(scope, &expr.argument)?;
        Ok(Value::Undefined)
      }
      OperatorName::Delete => match &*expr.argument.stx {
        Expr::Member(_) | Expr::ComputedMember(_) => {
          let reference = self.eval_reference(scope, &expr.argument)?;
          match reference {
            Reference::Property { object, key } => Ok(Value::Bool(scope.ordinary_delete(object, key)?)),
            // Deleting bindings (`delete x`) is not supported yet.
            Reference::Binding(_) => Ok(Value::Bool(false)),
          }
        }
        // `delete` of non-reference expressions always returns true (after evaluating the operand).
        _ => {
          let _ = self.eval_expr(scope, &expr.argument)?;
          Ok(Value::Bool(true))
        }
      },
      _ => Err(VmError::Unimplemented("unary operator")),
    }
  }

  fn eval_cond(&mut self, scope: &mut Scope<'_>, expr: &CondExpr) -> Result<Value, VmError> {
    let test = self.eval_expr(scope, &expr.test)?;
    if to_boolean(scope.heap(), test)? {
      self.eval_expr(scope, &expr.consequent)
    } else {
      self.eval_expr(scope, &expr.alternate)
    }
  }

  fn eval_binary(&mut self, scope: &mut Scope<'_>, expr: &BinaryExpr) -> Result<Value, VmError> {
    match expr.operator {
      OperatorName::Assignment => {
        let reference = self.eval_reference(scope, &expr.left)?;
        let mut rhs_scope = scope.reborrow();
        self.root_reference(&mut rhs_scope, &reference);
        let value = self.eval_expr(&mut rhs_scope, &expr.right)?;
        rhs_scope.push_root(value);
        self.put_value_to_reference(&mut rhs_scope, &reference, value)?;
        Ok(value)
      }
      OperatorName::LogicalAnd => {
        let left = self.eval_expr(scope, &expr.left)?;
        if !to_boolean(scope.heap(), left)? {
          return Ok(left);
        }
        self.eval_expr(scope, &expr.right)
      }
      OperatorName::LogicalOr => {
        let left = self.eval_expr(scope, &expr.left)?;
        if to_boolean(scope.heap(), left)? {
          return Ok(left);
        }
        self.eval_expr(scope, &expr.right)
      }
      OperatorName::NullishCoalescing => {
        let left = self.eval_expr(scope, &expr.left)?;
        if is_nullish(left) {
          self.eval_expr(scope, &expr.right)
        } else {
          Ok(left)
        }
      }
      OperatorName::StrictEquality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(strict_equal(rhs_scope.heap(), left, right)?))
      }
      OperatorName::StrictInequality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(!strict_equal(rhs_scope.heap(), left, right)?))
      }
      OperatorName::Equality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(abstract_equality(rhs_scope.heap_mut(), left, right)?))
      }
      OperatorName::Inequality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(!abstract_equality(
          rhs_scope.heap_mut(),
          left,
          right,
        )?))
      }
      OperatorName::Addition => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        add_operator(rhs_scope.heap_mut(), left, right)
      }
      OperatorName::Subtraction
      | OperatorName::Multiplication
      | OperatorName::Division
      | OperatorName::Remainder
      | OperatorName::LessThan
      | OperatorName::LessThanOrEqual
      | OperatorName::GreaterThan
      | OperatorName::GreaterThanOrEqual => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left);
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        // Root `right` for the duration of numeric conversion: `ToNumber` may allocate when called
        // on objects (via `ToPrimitive`).
        rhs_scope.push_root(right);
        let left_n = to_number(rhs_scope.heap_mut(), left)?;
        let right_n = to_number(rhs_scope.heap_mut(), right)?;

        match expr.operator {
          OperatorName::Subtraction => Ok(Value::Number(left_n - right_n)),
          OperatorName::Multiplication => Ok(Value::Number(left_n * right_n)),
          OperatorName::Division => Ok(Value::Number(left_n / right_n)),
          OperatorName::Remainder => Ok(Value::Number(left_n % right_n)),
          OperatorName::LessThan => Ok(Value::Bool(left_n < right_n)),
          OperatorName::LessThanOrEqual => Ok(Value::Bool(left_n <= right_n)),
          OperatorName::GreaterThan => Ok(Value::Bool(left_n > right_n)),
          OperatorName::GreaterThanOrEqual => Ok(Value::Bool(left_n >= right_n)),
          _ => unreachable!(),
        }
      }
      _ => Err(VmError::Unimplemented("binary operator")),
    }
  }
}

fn alloc_string_from_lit_str(
  scope: &mut Scope<'_>,
  node: &Node<LitStrExpr>,
) -> Result<GcString, VmError> {
  if let Some(units) = literal_string_code_units(&node.assoc) {
    scope.alloc_string_from_code_units(units)
  } else {
    scope.alloc_string_from_utf8(&node.stx.value)
  }
}

fn expect_simple_binding_identifier<'a>(pat_decl: &'a PatDecl) -> Result<&'a str, VmError> {
  match &*pat_decl.pat.stx {
    Pat::Id(id) => Ok(&id.stx.name),
    _ => Err(VmError::Unimplemented("destructuring patterns")),
  }
}

fn is_nullish(value: Value) -> bool {
  matches!(value, Value::Undefined | Value::Null)
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

fn typeof_name(heap: &Heap, value: Value) -> Result<&'static str, VmError> {
  Ok(match value {
    Value::Undefined => "undefined",
    Value::Null => "object",
    Value::Bool(_) => "boolean",
    Value::Number(_) => "number",
    Value::String(_) => "string",
    Value::Symbol(_) => "symbol",
    Value::Object(obj) => match heap.get_function_call_handler(obj) {
      Ok(_) => "function",
      Err(VmError::NotCallable) => "object",
      Err(err) => return Err(err),
    },
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
