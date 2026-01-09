use crate::destructure::{bind_assignment_target, bind_pattern, BindingKind};
use crate::iterator;
use crate::ops::{abstract_equality, to_number};
use crate::{
  EnvRootId, GcEnv, GcObject, GcString, Heap, JsBigInt, PropertyDescriptor, PropertyDescriptorPatch,
  PropertyKey, PropertyKind, Realm, RootId, Scope, SourceText, StackFrame, Value, Vm, VmError,
  VmHostHooks, VmJobContext,
};
use diagnostics::FileId;
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::lit::{
  LitArrElem, LitArrExpr, LitBigIntExpr, LitBoolExpr, LitNumExpr, LitObjExpr, LitStrExpr,
  LitTemplateExpr, LitTemplatePart,
};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{
  ArrowFuncExpr, BinaryExpr, CallExpr, ComputedMemberExpr, CondExpr, Expr, FuncExpr, IdExpr,
  MemberExpr, UnaryExpr,
};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::{literal_string_code_units, Node, ParenthesizedExpr};
use parse_js::ast::stmt::decl::{FuncDecl, PatDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  BlockStmt, CatchBlock, DoWhileStmt, ExprStmt, ForBody, ForInOfLhs, ForOfStmt, ForTripleStmt,
  IfStmt, LabelStmt, ReturnStmt, Stmt, SwitchStmt, ThrowStmt, TryStmt, WhileStmt,
};
use parse_js::operator::OperatorName;
use parse_js::token::TT;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::collections::HashSet;
use std::sync::Arc;
 
use crate::function::ThisMode;
use crate::vm::EcmaFunctionKind;

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

fn detect_use_strict_directive(stmts: &[Node<Stmt>]) -> bool {
  for stmt in stmts {
    let Stmt::Expr(expr_stmt) = &*stmt.stx else {
      break;
    };

    let expr = &expr_stmt.stx.expr;

    // Parenthesized string literals are not directive prologues.
    if expr.assoc.get::<ParenthesizedExpr>().is_some() {
      break;
    }

    let Expr::LitStr(lit) = &*expr.stx else {
      break;
    };

    if lit.stx.value == "use strict" {
      return true;
    }
  }
  false
}

fn throw_type_error(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> Result<VmError, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let value = crate::error_object::new_error(
    scope,
    intr.type_error_prototype(),
    "TypeError",
    message,
  )?;
  Ok(VmError::Throw(value))
}

fn throw_reference_error(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> Result<VmError, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let value = crate::error_object::new_error(
    scope,
    intr.reference_error_prototype(),
    "ReferenceError",
    message,
  )?;
  Ok(VmError::Throw(value))
}
 
#[derive(Clone, Copy, Debug)]
enum VarEnv {
  GlobalObject,
  Env(GcEnv),
}

#[derive(Debug)]
pub(crate) struct RuntimeEnv {
  global_object: GcObject,
  lexical_env: GcEnv,
  lexical_root: EnvRootId,
  var_env: VarEnv,
  source: Arc<SourceText>,
  base_offset: u32,
  prefix_len: u32,
}

impl RuntimeEnv {
  fn new(
    heap: &mut Heap,
    global_object: GcObject,
  ) -> Result<Self, VmError> {
    // Root the global object across env allocation in case it triggers GC.
    let mut scope = heap.scope();
    scope.push_root(Value::Object(global_object))?;

    let lexical_env = scope.env_create(None)?;
    let lexical_root = scope.heap_mut().add_env_root(lexical_env)?;

    Ok(Self {
      global_object,
      lexical_env,
      lexical_root,
      var_env: VarEnv::GlobalObject,
      source: Arc::new(SourceText::new("<init>", "")),
      base_offset: 0,
      prefix_len: 0,
    })
  }

  pub(crate) fn new_with_var_env(
    heap: &mut Heap,
    global_object: GcObject,
    lexical_env: GcEnv,
    var_env: GcEnv,
  ) -> Result<Self, VmError> {
    // Root the global object across root registration in case it triggers GC.
    let mut scope = heap.scope();
    scope.push_root(Value::Object(global_object))?;
    scope.push_env_root(lexical_env)?;
    scope.push_env_root(var_env)?;

    let lexical_root = scope.heap_mut().add_env_root(lexical_env)?;

    Ok(Self {
      global_object,
      lexical_env,
      lexical_root,
      var_env: VarEnv::Env(var_env),
      source: Arc::new(SourceText::new("<init>", "")),
      base_offset: 0,
      prefix_len: 0,
    })
  }

  pub(crate) fn teardown(&mut self, heap: &mut Heap) {
    heap.remove_env_root(self.lexical_root);
  }

  fn set_lexical_env(&mut self, heap: &mut Heap, env: GcEnv) {
    self.lexical_env = env;
    heap.set_env_root(self.lexical_root, env);
  }

  pub(crate) fn set_source_info(&mut self, source: Arc<SourceText>, base_offset: u32, prefix_len: u32) {
    self.source = source;
    self.base_offset = base_offset;
    self.prefix_len = prefix_len;
  }

  pub(crate) fn source(&self) -> Arc<SourceText> {
    self.source.clone()
  }

  pub(crate) fn base_offset(&self) -> u32 {
    self.base_offset
  }

  pub(crate) fn prefix_len(&self) -> u32 {
    self.prefix_len
  }

  pub(crate) fn global_object(&self) -> GcObject {
    self.global_object
  }

  pub(crate) fn lexical_env(&self) -> GcEnv {
    self.lexical_env
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
    match self.var_env {
      VarEnv::GlobalObject => {
        let global_object = self.global_object;

        // Root the global object across property-key allocation in case it triggers GC.
        let mut key_scope = scope.reborrow();
        key_scope.push_root(Value::Object(global_object))?;

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
      VarEnv::Env(env) => {
        if scope.heap().env_has_binding(env, name)? {
          return Ok(());
        }
        scope.env_create_mutable_binding(env, name)?;
        scope
          .heap_mut()
          .env_initialize_binding(env, name, Value::Undefined)?;
        Ok(())
      }
    }
  }

  fn get(
    &self,
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    name: &str,
  ) -> Result<Option<Value>, VmError> {
    if let Some(env) = self.resolve_lexical_binding(scope.heap(), name)? {
      match scope.heap().env_get_binding_value(env, name, false) {
        Ok(v) => return Ok(Some(v)),
        // TDZ sentinel from `Heap::{env_get_binding_value, env_set_mutable_binding}`.
        Err(VmError::Throw(Value::Null)) => {
          let msg = format!("Cannot access '{}' before initialization", name);
          return Err(throw_reference_error(vm, scope, &msg)?);
        }
        Err(err) => return Err(err),
      }
    }

    // Fall back to global object property lookup.
    let global_object = self.global_object;
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(global_object))?;
    let key_s = key_scope.alloc_string(name)?;
    key_scope.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);

    // Distinguish between a missing property (unbound identifier) and a present property whose
    // value is actually `undefined`.
    if !key_scope.ordinary_has_property(global_object, key)? {
      return Ok(None);
    }

    let receiver = Value::Object(global_object);
    Ok(Some(key_scope.ordinary_get(vm, global_object, key, receiver)?))
  }

  pub(crate) fn set(
    &mut self,
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    name: &str,
    value: Value,
    strict: bool,
  ) -> Result<(), VmError> {
    if let Some(env) = self.resolve_lexical_binding(scope.heap(), name)? {
      match scope
        .heap_mut()
        .env_set_mutable_binding(env, name, value, strict)
      {
        Ok(()) => return Ok(()),
        // TDZ sentinel from `Heap::{env_get_binding_value, env_set_mutable_binding}`.
        Err(VmError::Throw(Value::Null)) => {
          let msg = format!("Cannot access '{}' before initialization", name);
          return Err(throw_reference_error(vm, scope, &msg)?);
        }
        // `const` assignment sentinel from `Heap::env_set_mutable_binding`.
        Err(VmError::Throw(Value::Undefined)) => {
          return Err(throw_type_error(vm, scope, "Assignment to constant variable.")?);
        }
        Err(err) => return Err(err),
      }
    }

    // Assignment to global (var) bindings is backed by the global object.
    let global_object = self.global_object;
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(global_object))?;
    // Root `value` across key allocation and property definition in case they trigger GC.
    key_scope.push_root(value)?;
    let key = PropertyKey::from_string(key_scope.alloc_string(name)?);

    let has_binding = key_scope.ordinary_has_property(global_object, key)?;
    if !has_binding {
      if strict {
        let msg = format!("{name} is not defined");
        return Err(throw_reference_error(vm, &mut key_scope, &msg)?);
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
        PropertyKind::Data { writable: false, .. } => {
          if strict {
            let msg = format!("Cannot assign to read only property '{name}'");
            return Err(throw_type_error(vm, &mut key_scope, &msg)?);
          }
          return Ok(());
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

  pub(crate) fn set_var(
    &mut self,
    scope: &mut Scope<'_>,
    name: &str,
    value: Value,
  ) -> Result<(), VmError> {
    // `var` declarations always assign to the global/function var environment, even when a lexical
    // binding shadows the identifier (e.g. a `catch(e)` parameter).
    // Root the initializer value across var-env binding creation/assignment in case it triggers GC.
    let mut outer_scope = scope.reborrow();
    outer_scope.push_root(value)?;
    self.declare_var(&mut outer_scope, name)?;

    match self.var_env {
      VarEnv::GlobalObject => {
        let global_object = self.global_object;
        let mut key_scope = outer_scope.reborrow();
        key_scope.push_root(Value::Object(global_object))?;
        key_scope.push_root(value)?;
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
            PropertyKind::Data { writable: false, .. } => {
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
      VarEnv::Env(env) => outer_scope
        .heap_mut()
        .env_set_mutable_binding(env, name, value, false),
    }
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
    self.exec_script_source(Arc::new(SourceText::new("<inline>", source)))
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`).
  pub fn exec_script_source(&mut self, source: Arc<SourceText>) -> Result<Value, VmError> {
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };
    let top = parse_with_options(&source.text, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;
    let strict = detect_use_strict_directive(&top.stx.body);

    let global_object = self.realm.global_object();
    self.env.set_source_info(source.clone(), 0, 0);

    let (line, col) = source.line_col(0);
    let frame = StackFrame {
      function: None,
      source: source.name.clone(),
      line,
      col,
    };
    let mut vm_frame = self.vm.enter_frame(frame)?;

    let mut scope = self.heap.scope();
    let global_this = Value::Object(global_object);
    let mut evaluator = Evaluator {
      vm: &mut *vm_frame,
      env: &mut self.env,
      strict,
      this: global_this,
    };

    evaluator.hoist_var_decls(&mut scope, &top.stx.body)?;
    let global_lex = evaluator.env.lexical_env;
    evaluator.hoist_lexical_decls_in_stmt_list(&mut scope, global_lex, &top.stx.body)?;
    evaluator.hoist_function_decls_in_stmt_list(&mut scope, &top.stx.body)?;

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
  fn call(
    &mut self,
    host: &mut dyn VmHostHooks,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    // Borrow-split `vm` and `heap` so we can hold a `Scope` while calling into the VM.
    let vm = &mut self.vm;
    let heap = &mut self.heap;
    let mut scope = heap.scope();
    vm.call_with_host(&mut scope, host, callee, this, args)
  }

  fn construct(
    &mut self,
    host: &mut dyn VmHostHooks,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    let vm = &mut self.vm;
    let heap = &mut self.heap;
    let mut scope = heap.scope();
    vm.construct_with_host(&mut scope, host, callee, args, new_target)
  }

  fn add_root(&mut self, value: Value) -> Result<RootId, VmError> {
    self.heap.add_root(value)
  }

  fn remove_root(&mut self, id: RootId) {
    self.heap.remove_root(id)
  }
}

struct Evaluator<'a> {
  vm: &'a mut Vm,
  env: &'a mut RuntimeEnv,
  strict: bool,
  this: Value,
}

#[derive(Clone, Copy, Debug)]
enum Reference<'a> {
  Binding(&'a str),
  Property { object: GcObject, key: PropertyKey },
}

#[derive(Clone, Copy, Debug)]
enum ToPrimitiveHint {
  Default,
  String,
  Number,
}

impl ToPrimitiveHint {
  fn as_str(self) -> &'static str {
    match self {
      ToPrimitiveHint::Default => "default",
      ToPrimitiveHint::String => "string",
      ToPrimitiveHint::Number => "number",
    }
  }
}

#[derive(Clone, Copy, Debug)]
enum NumericValue {
  Number(f64),
  BigInt(JsBigInt),
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

  fn hoist_function_decls_in_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    for stmt in stmts {
      self.hoist_function_decls_in_stmt(scope, &stmt.stx)?;
    }
    Ok(())
  }

  fn hoist_function_decls_in_stmt(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &Stmt,
  ) -> Result<(), VmError> {
    match stmt {
      Stmt::FunctionDecl(decl) => self.instantiate_function_decl(scope, decl),
      Stmt::Block(block) => self.hoist_function_decls_in_stmt_list(scope, &block.stx.body),
      Stmt::If(stmt) => {
        self.hoist_function_decls_in_stmt(scope, &stmt.stx.consequent.stx)?;
        if let Some(alt) = &stmt.stx.alternate {
          self.hoist_function_decls_in_stmt(scope, &alt.stx)?;
        }
        Ok(())
      }
      Stmt::Try(stmt) => {
        self.hoist_function_decls_in_stmt_list(scope, &stmt.stx.wrapped.stx.body)?;
        if let Some(catch) = &stmt.stx.catch {
          self.hoist_function_decls_in_stmt_list(scope, &catch.stx.body)?;
        }
        if let Some(finally) = &stmt.stx.finally {
          self.hoist_function_decls_in_stmt_list(scope, &finally.stx.body)?;
        }
        Ok(())
      }
      Stmt::While(stmt) => self.hoist_function_decls_in_stmt(scope, &stmt.stx.body.stx),
      Stmt::DoWhile(stmt) => self.hoist_function_decls_in_stmt(scope, &stmt.stx.body.stx),
      Stmt::ForTriple(stmt) => self.hoist_function_decls_in_stmt_list(scope, &stmt.stx.body.stx.body),
      Stmt::ForOf(stmt) => self.hoist_function_decls_in_stmt_list(scope, &stmt.stx.body.stx.body),
      Stmt::Label(stmt) => self.hoist_function_decls_in_stmt(scope, &stmt.stx.statement.stx),
      Stmt::Switch(stmt) => {
        for branch in &stmt.stx.branches {
          self.hoist_function_decls_in_stmt_list(scope, &branch.stx.body)?;
        }
        Ok(())
      }
      _ => Ok(()),
    }
  }

  fn instantiate_function_decl(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &Node<FuncDecl>,
  ) -> Result<(), VmError> {
    use crate::function::ThisMode;
    use crate::vm::EcmaFunctionKind;

    let Some(name) = &decl.stx.name else {
      return Err(VmError::Unimplemented("anonymous function declaration"));
    };

    let func = &decl.stx.function.stx;
    if func.async_ || func.generator {
      return Err(VmError::Unimplemented("async/generator functions"));
    }
    let is_strict = self.strict
      || match &func.body {
        Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
        Some(FuncBody::Expression(_)) => false,
        None => return Err(VmError::Unimplemented("function without body")),
      };

    let this_mode = if func.arrow {
      ThisMode::Lexical
    } else if is_strict {
      ThisMode::Strict
    } else {
      ThisMode::Global
    };

    let name_s = scope.alloc_string(&name.stx.name)?;
    let length = function_length(func);

    let rel_start = decl.loc.start_u32().saturating_sub(self.env.prefix_len());
    let rel_end = decl.loc.end_u32().saturating_sub(self.env.prefix_len());
    let span_start = self.env.base_offset().saturating_add(rel_start);
    let span_end = self.env.base_offset().saturating_add(rel_end);

    let code_id = self.vm.register_ecma_function(self.env.source(), span_start, span_end, EcmaFunctionKind::Decl)?;
    let func_obj = scope.alloc_ecma_function(
      code_id,
      true,
      name_s,
      length,
      this_mode,
      is_strict,
      Some(self.env.lexical_env),
    )?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    scope
      .heap_mut()
      .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
    scope
      .heap_mut()
      .set_function_realm(func_obj, self.env.global_object())?;

    let mut assign_scope = scope.reborrow();
    assign_scope.push_root(Value::Object(func_obj))?;
    self
      .env
      .set_var(&mut assign_scope, &name.stx.name, Value::Object(func_obj))?;
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
            self.hoist_lexical_names_from_pat(scope, env, &declarator.pattern.stx.pat.stx, true)?;
          }
        }
        VarDeclMode::Const => {
          for declarator in &var.stx.declarators {
            self.hoist_lexical_names_from_pat(scope, env, &declarator.pattern.stx.pat.stx, false)?;
          }
        }
        _ => {}
      }
    }
    Ok(())
  }

  fn hoist_lexical_names_from_pat(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    pat: &Pat,
    mutable: bool,
  ) -> Result<(), VmError> {
    match pat {
      Pat::Id(id) => {
        if mutable {
          scope.env_create_mutable_binding(env, &id.stx.name)?;
        } else {
          scope.env_create_immutable_binding(env, &id.stx.name)?;
        }
        Ok(())
      }
      Pat::Obj(obj) => {
        for prop in &obj.stx.properties {
          self.hoist_lexical_names_from_pat(scope, env, &prop.stx.target.stx, mutable)?;
        }
        if let Some(rest) = &obj.stx.rest {
          self.hoist_lexical_names_from_pat(scope, env, &rest.stx, mutable)?;
        }
        Ok(())
      }
      Pat::Arr(arr) => {
        for elem in &arr.stx.elements {
          if let Some(elem) = elem {
            self.hoist_lexical_names_from_pat(scope, env, &elem.target.stx, mutable)?;
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.hoist_lexical_names_from_pat(scope, env, &rest.stx, mutable)?;
        }
        Ok(())
      }
      Pat::AssignTarget(_) => Err(VmError::Unimplemented("lexical declaration assignment targets")),
    }
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
      Stmt::ForOf(stmt) => {
        if let ForInOfLhs::Decl((mode, pat_decl)) = &stmt.stx.lhs {
          if *mode == VarDeclMode::Var {
            self.collect_var_names_from_pat_decl(&pat_decl.stx, out)?;
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
      // Function declarations are hoisted like `var` declarations, but we must not traverse into
      // the function body.
      Stmt::FunctionDecl(decl) => {
        if let Some(name) = &decl.stx.name {
          out.insert(name.stx.name.clone());
        }
      }

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
    self.collect_var_names_from_pat(&pat_decl.pat.stx, out)
  }

  fn collect_var_names_from_pat(&self, pat: &Pat, out: &mut HashSet<String>) -> Result<(), VmError> {
    match pat {
      Pat::Id(id) => {
        out.insert(id.stx.name.clone());
        Ok(())
      }
      Pat::Obj(obj) => {
        for prop in &obj.stx.properties {
          self.collect_var_names_from_pat(&prop.stx.target.stx, out)?;
        }
        if let Some(rest) = &obj.stx.rest {
          self.collect_var_names_from_pat(&rest.stx, out)?;
        }
        Ok(())
      }
      Pat::Arr(arr) => {
        for elem in &arr.stx.elements {
          if let Some(elem) = elem {
            self.collect_var_names_from_pat(&elem.target.stx, out)?;
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.collect_var_names_from_pat(&rest.stx, out)?;
        }
        Ok(())
      }
      Pat::AssignTarget(_) => Err(VmError::Unimplemented("var declaration assignment targets")),
    }
  }

  fn eval_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<Completion, VmError> {
    // Root the running completion value so it cannot be collected while evaluating subsequent
    // statements (which may allocate and trigger GC).
    let last_root = scope.heap_mut().add_root(Value::Undefined)?;
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

  fn eval_stmt(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &Node<Stmt>,
  ) -> Result<Completion, VmError> {
    self.eval_stmt_labelled(scope, stmt, &[])
  }

  /// Evaluates a statement with an associated label set.
  ///
  /// This models ECMA-262 `LabelledEvaluation` / `LoopEvaluation` label propagation:
  /// nested label statements extend `label_set`, and iteration statements use it to determine which
  /// labelled `continue` completions are consumed by the loop.
  fn eval_stmt_labelled(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &Node<Stmt>,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    // One tick per statement.
    self.tick()?;

    let res = match &*stmt.stx {
      Stmt::Empty(_) => Ok(Completion::empty()),
      Stmt::Expr(expr_stmt) => self.eval_expr_stmt(scope, &expr_stmt.stx),
      Stmt::VarDecl(var_decl) => self.eval_var_decl(scope, &var_decl.stx),
      Stmt::Block(block) => self.eval_block_stmt(scope, &block.stx),
      Stmt::If(stmt) => self.eval_if(scope, &stmt.stx),
      Stmt::Throw(stmt) => self.eval_throw(scope, &stmt.stx),
      Stmt::Try(stmt) => self.eval_try(scope, &stmt.stx),
      Stmt::Return(stmt) => self.eval_return(scope, &stmt.stx),
      Stmt::While(stmt) => self.eval_while(scope, &stmt.stx, label_set),
      Stmt::DoWhile(stmt) => self.eval_do_while(scope, &stmt.stx, label_set),
      Stmt::ForTriple(stmt) => self.eval_for_triple(scope, &stmt.stx, label_set),
      Stmt::ForOf(stmt) => self.eval_for_of(scope, &stmt.stx, label_set),
      Stmt::Switch(stmt) => self.eval_switch(scope, &stmt.stx),
      Stmt::Label(stmt) => self.eval_label(scope, &stmt.stx, label_set),
      // Function declarations are instantiated during hoisting.
      Stmt::FunctionDecl(_) => Ok(Completion::empty()),
      Stmt::Break(stmt) => Ok(Completion::Break(stmt.stx.label.clone(), None)),
      Stmt::Continue(stmt) => Ok(Completion::Continue(stmt.stx.label.clone(), None)),

      _ => Err(VmError::Unimplemented("statement type")),
    };

    // Treat internal `VmError::Throw` as a JS throw completion so it is catchable by `try/catch`.
    match res {
      Err(VmError::Throw(v)) => Ok(Completion::Throw(v)),
      other => other,
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
            // Destructuring declarations require an initializer (early error in real JS).
            if !matches!(&*declarator.pattern.stx.pat.stx, Pat::Id(_)) {
              return Err(VmError::Unimplemented("destructuring var without initializer"));
            }
            continue;
          };
          let value = self.eval_expr(scope, init)?;
          bind_pattern(
            self.vm,
            scope,
            self.env,
            &declarator.pattern.stx.pat.stx,
            value,
            BindingKind::Var,
            self.strict,
            self.this,
          )?;
        }
        Ok(Completion::empty())
      }
      VarDeclMode::Let => {
        for declarator in &decl.declarators {
          let Pat::Id(id) = &*declarator.pattern.stx.pat.stx else {
            let Some(init) = &declarator.initializer else {
              return Err(VmError::Unimplemented("destructuring let without initializer"));
            };
            let value = self.eval_expr(scope, init)?;
            bind_pattern(
              self.vm,
              scope,
              self.env,
              &declarator.pattern.stx.pat.stx,
              value,
              BindingKind::Let,
              self.strict,
              self.this,
            )?;
            continue;
          };

          let name = id.stx.name.as_str();
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
          let Some(init) = &declarator.initializer else {
            // TODO: should be a syntax error (early error).
            return Err(VmError::Unimplemented("const without initializer"));
          };
          let value = self.eval_expr(scope, init)?;

          if !matches!(&*declarator.pattern.stx.pat.stx, Pat::Id(_)) {
            bind_pattern(
              self.vm,
              scope,
              self.env,
              &declarator.pattern.stx.pat.stx,
              value,
              BindingKind::Const,
              self.strict,
              self.this,
            )?;
            continue;
          }

          let Pat::Id(id) = &*declarator.pattern.stx.pat.stx else {
            debug_assert!(false, "expected Pat::Id after matches! guard");
            return Err(VmError::InvariantViolation(
              "internal error: const declaration pattern mismatch",
            ));
          };
          let name = id.stx.name.as_str();

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
          _ => return Err(VmError::Unimplemented("try/catch missing thrown value")),
        };
        result = self.eval_catch(scope, &catch.stx, thrown)?;
      }
    }

    if let Some(finally) = &stmt.finally {
      // Root the pending completion's value (if any) while evaluating `finally`, which may
      // allocate and trigger GC.
      let pending_root = result
        .value()
        .map(|v| scope.heap_mut().add_root(v))
        .transpose()?;
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
      catch_scope.push_root(thrown)?;

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
    // Bind into the provided catch environment (which should also be the current lexical env).
    let _ = env;
    bind_pattern(
      self.vm,
      scope,
      self.env,
      &param.pat.stx,
      thrown,
      BindingKind::Let,
      self.strict,
      self.this,
    )
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

  /// ECMA-262 `LoopContinues(completion, labelSet)`.
  fn loop_continues(completion: &Completion, label_set: &[String]) -> bool {
    match completion {
      Completion::Normal(_) => true,
      Completion::Continue(None, _) => true,
      Completion::Continue(Some(target), _) => label_set.iter().any(|l| l == target),
      _ => false,
    }
  }

  /// Converts an unlabelled `break` completion from an iteration statement into a normal
  /// completion (ECMA-262 `BreakableStatement` / `LabelledEvaluation` semantics).
  fn normalise_iteration_break(completion: Completion) -> Completion {
    match completion {
      Completion::Break(None, value) => Completion::normal(value.unwrap_or(Value::Undefined)),
      other => other,
    }
  }

  fn eval_while(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &WhileStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    let result = self.while_loop_evaluation(scope, stmt, label_set)?;
    Ok(Self::normalise_iteration_break(result))
  }

  /// ECMA-262 `WhileLoopEvaluation`.
  fn while_loop_evaluation(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &WhileStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    // Root `V` across the loop so the value can't be collected between iterations.
    let mut scope = scope.reborrow();
    let v_root_idx = scope.heap().root_stack.len();
    scope.push_root(Value::Undefined)?;
    let mut v = Value::Undefined;

    loop {
      let test = self.eval_expr(&mut scope, &stmt.condition)?;
      if !to_boolean(scope.heap(), test)? {
        return Ok(Completion::normal(v));
      }

      let stmt_result = self.eval_stmt(&mut scope, &stmt.body)?;
      if !Self::loop_continues(&stmt_result, label_set) {
        return Ok(stmt_result.update_empty(Some(v)));
      }

      if let Some(value) = stmt_result.value() {
        v = value;
        scope.heap_mut().root_stack[v_root_idx] = value;
      }
    }
  }

  fn eval_do_while(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &DoWhileStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    let result = self.do_while_loop_evaluation(scope, stmt, label_set)?;
    Ok(Self::normalise_iteration_break(result))
  }

  /// ECMA-262 `DoWhileLoopEvaluation`.
  fn do_while_loop_evaluation(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &DoWhileStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    // Root `V` across the loop so the value can't be collected between iterations.
    let mut scope = scope.reborrow();
    let v_root_idx = scope.heap().root_stack.len();
    scope.push_root(Value::Undefined)?;
    let mut v = Value::Undefined;

    loop {
      let stmt_result = self.eval_stmt(&mut scope, &stmt.body)?;
      if !Self::loop_continues(&stmt_result, label_set) {
        return Ok(stmt_result.update_empty(Some(v)));
      }

      if let Some(value) = stmt_result.value() {
        v = value;
        scope.heap_mut().root_stack[v_root_idx] = value;
      }

      let test = self.eval_expr(&mut scope, &stmt.condition)?;
      if !to_boolean(scope.heap(), test)? {
        return Ok(Completion::normal(v));
      }
    }
  }

  fn eval_for_triple(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForTripleStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    // Note: this is intentionally minimal and does not implement per-iteration lexical
    // environments for `let`/`const`.
    let result = self.for_triple_loop_evaluation(scope, stmt, label_set)?;
    Ok(Self::normalise_iteration_break(result))
  }

  /// ECMA-262 `ForLoopEvaluation` for `for (init; cond; post) { ... }`.
  fn for_triple_loop_evaluation(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForTripleStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    // Root `V` across the loop so the value can't be collected between iterations.
    let mut scope = scope.reborrow();
    let v_root_idx = scope.heap().root_stack.len();
    scope.push_root(Value::Undefined)?;
    let mut v = Value::Undefined;

    match &stmt.init {
      parse_js::ast::stmt::ForTripleStmtInit::None => {}
      parse_js::ast::stmt::ForTripleStmtInit::Expr(expr) => {
        let _ = self.eval_expr(&mut scope, expr)?;
      }
      parse_js::ast::stmt::ForTripleStmtInit::Decl(decl) => {
        let _ = self.eval_var_decl(&mut scope, &decl.stx)?;
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
        let test = self.eval_expr(&mut scope, cond)?;
        if !to_boolean(scope.heap(), test)? {
          return Ok(Completion::normal(v));
        }
      }

      let stmt_result = self.eval_for_body(&mut scope, &stmt.body.stx)?;
      if !Self::loop_continues(&stmt_result, label_set) {
        return Ok(stmt_result.update_empty(Some(v)));
      }

      if let Some(value) = stmt_result.value() {
        v = value;
        scope.heap_mut().root_stack[v_root_idx] = value;
      }

      if let Some(post) = &stmt.post {
        let _ = self.eval_expr(&mut scope, post)?;
      }
    }
  }

  fn eval_for_of(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForOfStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    let result = self.for_of_loop_evaluation(scope, stmt, label_set)?;
    Ok(Self::normalise_iteration_break(result))
  }

  fn for_of_loop_evaluation(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForOfStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    if stmt.await_ {
      return Err(VmError::Unimplemented("for await..of"));
    }

    let iterable = self.eval_expr(scope, &stmt.rhs)?;

    // Root the iterable + iterator record while evaluating the loop body, which may allocate and
    // trigger GC.
    let mut iter_scope = scope.reborrow();
    iter_scope.push_root(iterable)?;

    let mut iterator_record = iterator::get_iterator(self.vm, &mut iter_scope, iterable)?;
    iter_scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

    // Root `V` across the loop so the value can't be collected between iterations.
    let v_root_idx = iter_scope.heap().root_stack.len();
    iter_scope.push_root(Value::Undefined)?;
    let mut v = Value::Undefined;

    loop {
      // Tick once per iteration so `for (x of xs) {}` is budgeted even when the body is empty.
      self.tick()?;

      let next_value = match iterator::iterator_step_value(self.vm, &mut iter_scope, &mut iterator_record)
      {
        Ok(v) => v,
        Err(err) => {
          let _ = iterator::iterator_close(self.vm, &mut iter_scope, &iterator_record);
          return Err(err);
        }
      };

      let Some(value) = next_value else {
        return Ok(Completion::normal(v));
      };

      let bind_res: Result<(), VmError> = match &stmt.lhs {
        ForInOfLhs::Decl((mode, pat_decl)) => {
          let kind = match *mode {
            VarDeclMode::Var => BindingKind::Var,
            VarDeclMode::Let => BindingKind::Let,
            VarDeclMode::Const => BindingKind::Const,
            _ => {
              return Err(VmError::Unimplemented(
                "for-of loop variable declaration kind",
              ));
            }
          };
          bind_pattern(
            self.vm,
            &mut iter_scope,
            self.env,
            &pat_decl.stx.pat.stx,
            value,
            kind,
            self.strict,
            self.this,
          )
        }
        ForInOfLhs::Assign(pat) => bind_pattern(
          self.vm,
          &mut iter_scope,
          self.env,
          &pat.stx,
          value,
          BindingKind::Assignment,
          self.strict,
          self.this,
        ),
      };

      if let Err(err) = bind_res {
        let _ = iterator::iterator_close(self.vm, &mut iter_scope, &iterator_record);
        return Err(err);
      }

      let body_completion = match self.eval_for_body(&mut iter_scope, &stmt.body.stx) {
        Ok(c) => c,
        Err(err) => {
          let _ = iterator::iterator_close(self.vm, &mut iter_scope, &iterator_record);
          return Err(err);
        }
      };

      if !Self::loop_continues(&body_completion, label_set) {
        let _ = iterator::iterator_close(self.vm, &mut iter_scope, &iterator_record);
        return Ok(body_completion.update_empty(Some(v)));
      }

      if let Some(value) = body_completion.value() {
        v = value;
        iter_scope.heap_mut().root_stack[v_root_idx] = value;
      }
    }
  }

  fn eval_for_body(
    &mut self,
    scope: &mut Scope<'_>,
    body: &ForBody,
  ) -> Result<Completion, VmError> {
    self.eval_stmt_list(scope, &body.body)
  }

  fn eval_label(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &LabelStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    let mut new_label_set = label_set.to_vec();
    new_label_set.push(stmt.name.clone());

    let result = self.eval_stmt_labelled(scope, &stmt.statement, &new_label_set)?;

    match result {
      Completion::Break(Some(target), value) if target == stmt.name => {
        Ok(Completion::normal(value.unwrap_or(Value::Undefined)))
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
    switch_scope.push_root(discriminant)?;

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
      let last_root = switch_scope.heap_mut().add_root(Value::Undefined)?;
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
      Expr::LitBigInt(node) => self.eval_lit_bigint(&node.stx),
      Expr::LitBool(node) => self.eval_lit_bool(&node.stx),
      Expr::LitNull(_) => Ok(Value::Null),
      Expr::LitArr(node) => self.eval_lit_arr(scope, &node.stx),
      Expr::LitObj(node) => self.eval_lit_obj(scope, &node.stx),
      Expr::LitTemplate(node) => self.eval_lit_template(scope, &node.stx),
      Expr::This(_) => Ok(self.this),
      Expr::Id(node) => self.eval_id(scope, &node.stx),
      Expr::Call(node) => self.eval_call(scope, &node.stx),
      Expr::Func(node) => self.eval_func_expr(scope, node),
      Expr::ArrowFunc(node) => self.eval_arrow_func_expr(scope, node),
      Expr::Member(node) => self.eval_member(scope, &node.stx),
      Expr::ComputedMember(node) => self.eval_computed_member(scope, &node.stx),
      Expr::Unary(node) => self.eval_unary(scope, &node.stx),
      Expr::Binary(node) => self.eval_binary(scope, &node.stx),
      Expr::Cond(node) => self.eval_cond(scope, &node.stx),

      // Patterns sometimes show up in expression position (e.g. assignment targets). We only
      // support simple identifier patterns for now.
      Expr::IdPat(node) => self.eval_id_pat(scope, &node.stx),

      _ => Err(VmError::Unimplemented("expression type")),
    }
  }

  fn eval_member(&mut self, scope: &mut Scope<'_>, expr: &MemberExpr) -> Result<Value, VmError> {
    let base = self.eval_expr(scope, &expr.left)?;
    if expr.optional_chaining && is_nullish(base) {
      return Ok(Value::Undefined);
    }

    let Value::Object(object) = base else {
      return Err(VmError::Unimplemented("member access on non-object"));
    };

    // Root `object` across property-key allocation in case it triggers GC.
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(object))?;
    let key_s = key_scope.alloc_string(&expr.right)?;
    let reference = Reference::Property {
      object,
      key: PropertyKey::from_string(key_s),
    };
    self.get_value_from_reference(&mut key_scope, &reference)
  }

  fn eval_computed_member(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &ComputedMemberExpr,
  ) -> Result<Value, VmError> {
    let base = self.eval_expr(scope, &expr.object)?;
    if expr.optional_chaining && is_nullish(base) {
      return Ok(Value::Undefined);
    }

    let Value::Object(object) = base else {
      return Err(VmError::Unimplemented("computed member access on non-object"));
    };

    // Root `object` across key evaluation + `ToPropertyKey`, which may allocate and trigger GC.
    let mut key_scope = scope.reborrow();
    key_scope.push_root(Value::Object(object))?;
    let member_value = self.eval_expr(&mut key_scope, &expr.member)?;
    key_scope.push_root(member_value)?;
    let key = key_scope.heap_mut().to_property_key(member_value)?;
    let reference = Reference::Property { object, key };
    self.get_value_from_reference(&mut key_scope, &reference)
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
        key_scope.push_root(Value::Object(object))?;
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
        key_scope.push_root(Value::Object(object))?;
        let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
        key_scope.push_root(member_value)?;
        let key = key_scope.heap_mut().to_property_key(member_value)?;
        Ok(Reference::Property { object, key })
      }
      _ => Err(VmError::Unimplemented("expression is not a reference")),
    }
  }

  fn root_reference(&self, scope: &mut Scope<'_>, reference: &Reference<'_>) -> Result<(), VmError> {
    let Reference::Property { object, key } = *reference else {
      return Ok(());
    };
    scope.push_root(Value::Object(object))?;
    match key {
      PropertyKey::String(s) => scope.push_root(Value::String(s))?,
      PropertyKey::Symbol(s) => scope.push_root(Value::Symbol(s))?,
    };
    Ok(())
  }

  fn get_value_from_reference(
    &mut self,
    scope: &mut Scope<'_>,
    reference: &Reference<'_>,
  ) -> Result<Value, VmError> {
    match *reference {
      Reference::Binding(name) => match self.env.get(self.vm, scope, name)? {
        Some(v) => Ok(v),
        None => {
          let msg = format!("{name} is not defined");
          Err(throw_reference_error(self.vm, scope, &msg)?)
        }
      },
      Reference::Property { object, key } => {
        let mut get_scope = scope.reborrow();
        self.root_reference(&mut get_scope, reference)?;
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
      Reference::Binding(name) => self.env.set(self.vm, scope, name, value, self.strict),
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

  fn eval_func_expr(&mut self, scope: &mut Scope<'_>, expr: &Node<FuncExpr>) -> Result<Value, VmError> {
    let name = expr.stx.name.as_ref().map(|n| n.stx.name.as_str());
    self.instantiate_function_expr(scope, expr.loc.start_u32(), expr.loc.end_u32(), name, &expr.stx.func.stx)
  }

  fn eval_arrow_func_expr(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<ArrowFuncExpr>,
  ) -> Result<Value, VmError> {
    self.instantiate_arrow_function_expr(scope, expr.loc.start_u32(), expr.loc.end_u32(), &expr.stx.func.stx)
  }

  fn instantiate_function_expr(
    &mut self,
    scope: &mut Scope<'_>,
    loc_start: u32,
    loc_end: u32,
    name: Option<&str>,
    func: &parse_js::ast::func::Func,
  ) -> Result<Value, VmError> {
    use crate::function::ThisMode;
    use crate::vm::EcmaFunctionKind;

    if func.async_ || func.generator {
      return Err(VmError::Unimplemented("async/generator functions"));
    }
    let is_strict = self.strict
      || match &func.body {
        Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
        Some(FuncBody::Expression(_)) => false,
        None => return Err(VmError::Unimplemented("function without body")),
      };
    let this_mode = if func.arrow {
      ThisMode::Lexical
    } else if is_strict {
      ThisMode::Strict
    } else {
      ThisMode::Global
    };

    let name_s = match name {
      Some(name) => scope.alloc_string(name)?,
      None => scope.alloc_string("")?,
    };
    let length = function_length(func);

    let rel_start = loc_start.saturating_sub(self.env.prefix_len());
    let rel_end = loc_end.saturating_sub(self.env.prefix_len());
    let span_start = self.env.base_offset().saturating_add(rel_start);
    let span_end = self.env.base_offset().saturating_add(rel_end);

    let code_id =
      self
        .vm
        .register_ecma_function(self.env.source(), span_start, span_end, EcmaFunctionKind::Expr)?;
    let func_obj = scope.alloc_ecma_function(
      code_id,
      true,
      name_s,
      length,
      this_mode,
      is_strict,
      Some(self.env.lexical_env),
    )?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    scope
      .heap_mut()
      .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
    scope
      .heap_mut()
      .set_function_realm(func_obj, self.env.global_object())?;
    if func.arrow {
      scope.heap_mut().set_function_bound_this(func_obj, self.this)?;
    }
    Ok(Value::Object(func_obj))
  }

  fn instantiate_arrow_function_expr(
    &mut self,
    scope: &mut Scope<'_>,
    loc_start: u32,
    loc_end: u32,
    func: &parse_js::ast::func::Func,
  ) -> Result<Value, VmError> {
    use crate::function::ThisMode;
    use crate::vm::EcmaFunctionKind;

    if func.async_ || func.generator {
      return Err(VmError::Unimplemented("async/generator functions"));
    }
    let is_strict = self.strict
      || match &func.body {
        Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
        Some(FuncBody::Expression(_)) => false,
        None => return Err(VmError::Unimplemented("function without body")),
      };

    let length = function_length(func);

    let rel_start = loc_start.saturating_sub(self.env.prefix_len());
    let rel_end = loc_end.saturating_sub(self.env.prefix_len());
    let span_start = self.env.base_offset().saturating_add(rel_start);
    let span_end = self.env.base_offset().saturating_add(rel_end);

    let code_id =
      self
        .vm
        .register_ecma_function(self.env.source(), span_start, span_end, EcmaFunctionKind::Expr)?;
    let mut alloc_scope = scope.reborrow();
    // Root the captured `this` binding across allocation in case it triggers GC.
    alloc_scope.push_root(self.this)?;
    let name_s = alloc_scope.alloc_string("")?;
    alloc_scope.push_root(Value::String(name_s))?;

    let func_obj = alloc_scope.alloc_ecma_function(
      code_id,
      false,
      name_s,
      length,
      ThisMode::Lexical,
      is_strict,
      Some(self.env.lexical_env),
    )?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    alloc_scope
      .heap_mut()
      .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
    alloc_scope
      .heap_mut()
      .set_function_realm(func_obj, self.env.global_object())?;
    alloc_scope
      .heap_mut()
      .set_function_bound_this(func_obj, self.this)?;
    Ok(Value::Object(func_obj))
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

  fn eval_lit_bigint(&self, expr: &LitBigIntExpr) -> Result<Value, VmError> {
    let mag: u128 = expr
      .value
      .parse()
      .map_err(|_| VmError::Unimplemented("BigInt literal out of range"))?;
    Ok(Value::BigInt(JsBigInt::from_u128(mag)))
  }

  fn eval_lit_bool(&self, expr: &LitBoolExpr) -> Result<Value, VmError> {
    Ok(Value::Bool(expr.value))
  }

  fn eval_lit_template(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &LitTemplateExpr,
  ) -> Result<Value, VmError> {
    // Untagged template literals evaluate by concatenating their parts after `ToString`
    // conversion of substitutions.
    let mut units: Vec<u16> = Vec::new();
    for part in &expr.parts {
      match part {
        LitTemplatePart::String(s) => {
          let len = s.encode_utf16().count();
          units
            .try_reserve(len)
            .map_err(|_| VmError::OutOfMemory)?;
          units.extend(s.encode_utf16());
        }
        LitTemplatePart::Substitution(expr) => {
          let value = self.eval_expr(scope, expr)?;
          scope.push_root(value)?;
          let s = self.to_string_operator(scope, value)?;
          scope.push_root(Value::String(s))?;
          let js = scope.heap().get_string(s)?;
          units
            .try_reserve(js.len_code_units())
            .map_err(|_| VmError::OutOfMemory)?;
          units.extend_from_slice(js.as_code_units());
        }
      }
    }

    let s = scope.alloc_string_from_u16_vec(units)?;
    Ok(Value::String(s))
  }

  fn eval_lit_arr(&mut self, scope: &mut Scope<'_>, expr: &LitArrExpr) -> Result<Value, VmError> {
    let mut arr_scope = scope.reborrow();
    let arr = arr_scope.alloc_array(0)?;
    arr_scope.push_root(Value::Object(arr))?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    arr_scope
      .heap_mut()
      .object_set_prototype(arr, Some(intr.array_prototype()))?;

    let mut next_index: u32 = 0;
    for elem in &expr.elements {
      match elem {
        LitArrElem::Empty => {
          next_index = next_index.saturating_add(1);
        }
        LitArrElem::Rest(rest_expr) => {
          let mut spread_scope = arr_scope.reborrow();
          let spread_value = self.eval_expr(&mut spread_scope, rest_expr)?;
          spread_scope.push_root(spread_value)?;

          let mut iter = iterator::get_iterator(self.vm, &mut spread_scope, spread_value)?;
          spread_scope.push_roots(&[iter.iterator, iter.next_method])?;

          while let Some(value) =
            iterator::iterator_step_value(self.vm, &mut spread_scope, &mut iter)?
          {
            let idx = next_index;
            next_index = next_index.saturating_add(1);

            let mut elem_scope = spread_scope.reborrow();
            elem_scope.push_root(value)?;
            let key_s = elem_scope.alloc_string(&idx.to_string())?;
            elem_scope.push_root(Value::String(key_s))?;
            let key = PropertyKey::from_string(key_s);
            let ok = elem_scope.create_data_property(arr, key, value)?;
            if !ok {
              return Err(VmError::Unimplemented("CreateDataProperty returned false"));
            }
          }
        }
        LitArrElem::Single(elem_expr) => {
          let idx = next_index;
          next_index = next_index.saturating_add(1);

          let mut elem_scope = arr_scope.reborrow();
          let value = self.eval_expr(&mut elem_scope, elem_expr)?;
          elem_scope.push_root(value)?;
          let key_s = elem_scope.alloc_string(&idx.to_string())?;
          elem_scope.push_root(Value::String(key_s))?;
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
        value: Value::Number(next_index as f64),
        writable: true,
      },
    };
    arr_scope.define_property(arr, PropertyKey::from_string(length_key_s), length_desc)?;

    Ok(Value::Object(arr))
  }

  fn eval_lit_obj(&mut self, scope: &mut Scope<'_>, expr: &LitObjExpr) -> Result<Value, VmError> {
    let mut obj_scope = scope.reborrow();
    let obj = obj_scope.alloc_object()?;
    obj_scope.push_root(Value::Object(obj))?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    obj_scope
      .heap_mut()
      .object_set_prototype(obj, Some(intr.object_prototype()))?;

    for member in &expr.members {
      let mut member_scope = obj_scope.reborrow();
      let member = &member.stx.typ;

      match member {
        ObjMemberType::Valued { key, val } => {
          let key_loc_start = match key {
            ClassOrObjKey::Direct(direct) => direct.loc.start_u32(),
            ClassOrObjKey::Computed(expr) => expr.loc.start_u32(),
          };
          let key = match key {
            ClassOrObjKey::Direct(direct) => {
              let key_s = if let Some(units) = literal_string_code_units(&direct.assoc) {
                member_scope.alloc_string_from_code_units(units)?
              } else if direct.stx.tt == TT::LiteralNumber {
                let n = direct
                  .stx
                  .key
                  .parse::<f64>()
                  .map_err(|_| VmError::Unimplemented("numeric literal property name parse"))?;
                member_scope.heap_mut().to_string(Value::Number(n))?
              } else {
                member_scope.alloc_string(&direct.stx.key)?
              };
              PropertyKey::from_string(key_s)
            }
            ClassOrObjKey::Computed(expr) => {
              let value = self.eval_expr(&mut member_scope, expr)?;
              member_scope.push_root(value)?;
              member_scope.heap_mut().to_property_key(value)?
            }
          };

          match key {
            PropertyKey::String(s) => member_scope.push_root(Value::String(s))?,
            PropertyKey::Symbol(s) => member_scope.push_root(Value::Symbol(s))?,
          };

          match val {
            ClassOrObjVal::Prop(Some(value_expr)) => {
              let value = self.eval_expr(&mut member_scope, value_expr)?;
              member_scope.push_root(value)?;
              let ok = member_scope.create_data_property(obj, key, value)?;
              if !ok {
                return Err(VmError::Unimplemented("CreateDataProperty returned false"));
              }
            }
            ClassOrObjVal::Prop(None) => {
              return Err(VmError::Unimplemented(
                "object literal property without initializer",
              ));
            }
            ClassOrObjVal::Method(method) => {
              let func_node = &method.stx.func;
              let length = function_length(&func_node.stx);

              let rel_start = key_loc_start.saturating_sub(self.env.prefix_len());
              let rel_end = func_node.loc.end_u32().saturating_sub(self.env.prefix_len());
              let span_start = self.env.base_offset().saturating_add(rel_start);
              let span_end = self.env.base_offset().saturating_add(rel_end);
              let code = self.vm.register_ecma_function(
                self.env.source(),
                span_start,
                span_end,
                EcmaFunctionKind::ObjectMember,
              )?;

              let is_strict = self.strict
                || match &func_node.stx.body {
                  Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
                  Some(FuncBody::Expression(_)) => false,
                  None => return Err(VmError::Unimplemented("method without body")),
                };

              let this_mode = if func_node.stx.arrow {
                ThisMode::Lexical
              } else if is_strict {
                ThisMode::Strict
              } else {
                ThisMode::Global
              };

              let closure_env = Some(self.env.lexical_env);

              let name_string = match key {
                PropertyKey::String(s) => s,
                PropertyKey::Symbol(_) => member_scope.alloc_string("")?,
              };

              let func_obj = member_scope.alloc_ecma_function(
                code,
                /* is_constructable */ false,
                name_string,
                length,
                this_mode,
                is_strict,
                closure_env,
              )?;
              let intr = self
                .vm
                .intrinsics()
                .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
              member_scope
                .heap_mut()
                .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
              member_scope
                .heap_mut()
                .set_function_realm(func_obj, self.env.global_object())?;
              if func_node.stx.arrow {
                member_scope
                  .heap_mut()
                  .set_function_bound_this(func_obj, self.this)?;
              }
              member_scope.push_root(Value::Object(func_obj))?;

              // Methods use the property key as the function `name` if possible.
              if !matches!(key, PropertyKey::String(_)) {
                crate::function_properties::set_function_name(
                  &mut member_scope,
                  func_obj,
                  key,
                  None,
                )?;
              }

              let ok = member_scope.create_data_property(obj, key, Value::Object(func_obj))?;
              if !ok {
                return Err(VmError::Unimplemented("CreateDataProperty returned false"));
              }
            }
            ClassOrObjVal::Getter(getter) => {
              let func_node = &getter.stx.func;
              let length = function_length(&func_node.stx);

              let rel_start = key_loc_start.saturating_sub(self.env.prefix_len());
              let rel_end = func_node.loc.end_u32().saturating_sub(self.env.prefix_len());
              let span_start = self.env.base_offset().saturating_add(rel_start);
              let span_end = self.env.base_offset().saturating_add(rel_end);
              let code = self.vm.register_ecma_function(
                self.env.source(),
                span_start,
                span_end,
                EcmaFunctionKind::ObjectMember,
              )?;

              let is_strict = self.strict
                || match &func_node.stx.body {
                  Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
                  Some(FuncBody::Expression(_)) => false,
                  None => return Err(VmError::Unimplemented("getter without body")),
                };

              let this_mode = if func_node.stx.arrow {
                ThisMode::Lexical
              } else if is_strict {
                ThisMode::Strict
              } else {
                ThisMode::Global
              };

              let closure_env = Some(self.env.lexical_env);

              let name_string = member_scope.alloc_string("")?;
              let func_obj = member_scope.alloc_ecma_function(
                code,
                /* is_constructable */ false,
                name_string,
                length,
                this_mode,
                is_strict,
                closure_env,
              )?;
              let intr = self
                .vm
                .intrinsics()
                .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
              member_scope
                .heap_mut()
                .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
              member_scope
                .heap_mut()
                .set_function_realm(func_obj, self.env.global_object())?;
              if func_node.stx.arrow {
                member_scope
                  .heap_mut()
                  .set_function_bound_this(func_obj, self.this)?;
              }
              member_scope.push_root(Value::Object(func_obj))?;
              crate::function_properties::set_function_name(&mut member_scope, func_obj, key, Some("get"))?;

              let ok = member_scope.define_own_property(
                obj,
                key,
                PropertyDescriptorPatch {
                  get: Some(Value::Object(func_obj)),
                  enumerable: Some(true),
                  configurable: Some(true),
                  ..Default::default()
                },
              )?;
              if !ok {
                return Err(VmError::Unimplemented("DefineOwnProperty returned false"));
              }
            }
            ClassOrObjVal::Setter(setter) => {
              let func_node = &setter.stx.func;
              let length = function_length(&func_node.stx);

              let rel_start = key_loc_start.saturating_sub(self.env.prefix_len());
              let rel_end = func_node.loc.end_u32().saturating_sub(self.env.prefix_len());
              let span_start = self.env.base_offset().saturating_add(rel_start);
              let span_end = self.env.base_offset().saturating_add(rel_end);
              let code = self.vm.register_ecma_function(
                self.env.source(),
                span_start,
                span_end,
                EcmaFunctionKind::ObjectMember,
              )?;

              let is_strict = self.strict
                || match &func_node.stx.body {
                  Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
                  Some(FuncBody::Expression(_)) => false,
                  None => return Err(VmError::Unimplemented("setter without body")),
                };

              let this_mode = if func_node.stx.arrow {
                ThisMode::Lexical
              } else if is_strict {
                ThisMode::Strict
              } else {
                ThisMode::Global
              };

              let closure_env = Some(self.env.lexical_env);

              let name_string = member_scope.alloc_string("")?;
              let func_obj = member_scope.alloc_ecma_function(
                code,
                /* is_constructable */ false,
                name_string,
                length,
                this_mode,
                is_strict,
                closure_env,
              )?;
              let intr = self
                .vm
                .intrinsics()
                .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
              member_scope
                .heap_mut()
                .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
              member_scope
                .heap_mut()
                .set_function_realm(func_obj, self.env.global_object())?;
              if func_node.stx.arrow {
                member_scope
                  .heap_mut()
                  .set_function_bound_this(func_obj, self.this)?;
              }
              member_scope.push_root(Value::Object(func_obj))?;
              crate::function_properties::set_function_name(&mut member_scope, func_obj, key, Some("set"))?;

              let ok = member_scope.define_own_property(
                obj,
                key,
                PropertyDescriptorPatch {
                  set: Some(Value::Object(func_obj)),
                  enumerable: Some(true),
                  configurable: Some(true),
                  ..Default::default()
                },
              )?;
              if !ok {
                return Err(VmError::Unimplemented("DefineOwnProperty returned false"));
              }
            }
            ClassOrObjVal::IndexSignature(_) => {
              return Err(VmError::Unimplemented("object literal index signature"));
            }
            ClassOrObjVal::StaticBlock(_) => {
              return Err(VmError::Unimplemented("object literal static block"));
            }
          }
        }
        ObjMemberType::Shorthand { id } => {
          let key_s = member_scope.alloc_string(&id.stx.name)?;
          member_scope.push_root(Value::String(key_s))?;
          let key = PropertyKey::from_string(key_s);
          let value = self.eval_id(&mut member_scope, &id.stx)?;
          member_scope.push_root(value)?;
          let ok = member_scope.create_data_property(obj, key, value)?;
          if !ok {
            return Err(VmError::Unimplemented("CreateDataProperty returned false"));
          }
        }
        ObjMemberType::Rest { val } => {
          let src_value = self.eval_expr(&mut member_scope, val)?;
          member_scope.push_root(src_value)?;

          let src_obj = match src_value {
            Value::Undefined | Value::Null => continue,
            Value::Object(o) => o,
            _ => return Err(VmError::Unimplemented("object spread source type")),
          };

          let keys = member_scope.ordinary_own_property_keys(src_obj)?;
          for key in keys {
            let mut key_scope = member_scope.reborrow();
            key_scope.push_root(Value::Object(src_obj))?;
            match key {
              PropertyKey::String(s) => key_scope.push_root(Value::String(s))?,
              PropertyKey::Symbol(s) => key_scope.push_root(Value::Symbol(s))?,
            };

            let Some(desc) = key_scope.ordinary_get_own_property(src_obj, key)? else {
              continue;
            };
            if !desc.enumerable {
              continue;
            }

            let value = key_scope.ordinary_get(self.vm, src_obj, key, Value::Object(src_obj))?;
            key_scope.push_root(value)?;
            let ok = key_scope.create_data_property(obj, key, value)?;
            if !ok {
              return Err(VmError::Unimplemented("CreateDataProperty returned false"));
            }
          }
        }
      }
    }

    Ok(Value::Object(obj))
  }

  fn eval_id(&mut self, scope: &mut Scope<'_>, expr: &IdExpr) -> Result<Value, VmError> {
    match self.env.get(self.vm, scope, &expr.name)? {
      Some(v) => Ok(v),
      None => {
        let msg = format!("{name} is not defined", name = expr.name);
        Err(throw_reference_error(self.vm, scope, &msg)?)
      }
    }
  }

  fn eval_id_pat(&mut self, scope: &mut Scope<'_>, expr: &IdPat) -> Result<Value, VmError> {
    match self.env.get(self.vm, scope, &expr.name)? {
      Some(v) => Ok(v),
      None => {
        let msg = format!("{name} is not defined", name = expr.name);
        Err(throw_reference_error(self.vm, scope, &msg)?)
      }
    }
  }

  fn eval_unary(&mut self, scope: &mut Scope<'_>, expr: &UnaryExpr) -> Result<Value, VmError> {
    match expr.operator {
      OperatorName::Delete => match &*expr.argument.stx {
        Expr::Id(id) => {
          if self.strict {
            let msg = format!("{name} is not defined", name = id.stx.name);
            return Err(throw_reference_error(self.vm, scope, &msg)?);
          }

          // Sloppy-mode: deleting an unqualified identifier returns `true` if the reference is
          // unresolvable, otherwise it performs a global-object property delete. Lexical bindings
          // are not deletable.
          if self
            .env
            .resolve_lexical_binding(scope.heap(), &id.stx.name)?
            .is_some()
          {
            return Ok(Value::Bool(false));
          }

          let global_object = self.env.global_object;
          let mut key_scope = scope.reborrow();
          key_scope.push_root(Value::Object(global_object))?;
          let key_s = key_scope.alloc_string(&id.stx.name)?;
          key_scope.push_root(Value::String(key_s))?;
          let key = PropertyKey::from_string(key_s);

          if !key_scope.ordinary_has_property(global_object, key)? {
            return Ok(Value::Bool(true));
          }

          Ok(Value::Bool(key_scope.ordinary_delete(global_object, key)?))
        }
        Expr::IdPat(id) => {
          if self.strict {
            let msg = format!("{name} is not defined", name = id.stx.name);
            return Err(throw_reference_error(self.vm, scope, &msg)?);
          }

          if self
            .env
            .resolve_lexical_binding(scope.heap(), &id.stx.name)?
            .is_some()
          {
            return Ok(Value::Bool(false));
          }

          let global_object = self.env.global_object;
          let mut key_scope = scope.reborrow();
          key_scope.push_root(Value::Object(global_object))?;
          let key_s = key_scope.alloc_string(&id.stx.name)?;
          key_scope.push_root(Value::String(key_s))?;
          let key = PropertyKey::from_string(key_s);

          if !key_scope.ordinary_has_property(global_object, key)? {
            return Ok(Value::Bool(true));
          }

          Ok(Value::Bool(key_scope.ordinary_delete(global_object, key)?))
        }
        Expr::Member(_) | Expr::ComputedMember(_) => {
          let reference = self.eval_reference(scope, &expr.argument)?;
          match reference {
            Reference::Property { object, key } => Ok(Value::Bool(scope.ordinary_delete(object, key)?)),
            // Deleting bindings (`delete x`) is handled above.
            Reference::Binding(_) => Ok(Value::Bool(false)),
          }
        }
        // `delete` of non-reference expressions always returns true (after evaluating the operand).
        _ => {
          let _ = self.eval_expr(scope, &expr.argument)?;
          Ok(Value::Bool(true))
        }
      },
      OperatorName::LogicalNot => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        Ok(Value::Bool(!to_boolean(scope.heap(), argument)?))
      }
      OperatorName::UnaryPlus => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        let n = self.to_number_operator(scope, argument)?;
        Ok(Value::Number(n))
      }
      OperatorName::UnaryNegation => {
        let argument = self.eval_expr(scope, &expr.argument)?;
        let num = self.to_numeric(scope, argument)?;
        Ok(match num {
          NumericValue::Number(n) => Value::Number(-n),
          NumericValue::BigInt(b) => Value::BigInt(b.negate()),
        })
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
      OperatorName::New => {
        // `parse-js` represents `new f()` as a `UnaryExpr` whose argument is a `CallExpr`.
        let (callee_expr, call_args) = match &*expr.argument.stx {
          Expr::Call(call) => (&call.stx.callee, Some(&call.stx.arguments)),
          _ => (&expr.argument, None),
        };

        let mut new_scope = scope.reborrow();
        let callee = self.eval_expr(&mut new_scope, callee_expr)?;
        new_scope.push_root(callee)?;

        let mut args: Vec<Value> = Vec::new();
        if let Some(call_args) = call_args {
          for arg in call_args {
            if arg.stx.spread {
              let spread_value = self.eval_expr(&mut new_scope, &arg.stx.value)?;
              new_scope.push_root(spread_value)?;

              let mut iter = iterator::get_iterator(self.vm, &mut new_scope, spread_value)?;
              new_scope.push_root(iter.iterator)?;
              new_scope.push_root(iter.next_method)?;

              while let Some(value) =
                iterator::iterator_step_value(self.vm, &mut new_scope, &mut iter)?
              {
                new_scope.push_root(value)?;
                args.push(value);
              }
            } else {
              let value = self.eval_expr(&mut new_scope, &arg.stx.value)?;
              new_scope.push_root(value)?;
              args.push(value);
            }
          }
        }

        // For `new`, the `newTarget` is the same as the constructor.
        self.vm.construct(&mut new_scope, callee, &args, callee)
      }
      _ => Err(VmError::Unimplemented("unary operator")),
    }
  }

  fn eval_call(&mut self, scope: &mut Scope<'_>, expr: &CallExpr) -> Result<Value, VmError> {
    // Special-case direct `eval(...)` calls.
    //
    // `vm-js` does not yet expose a global `eval` builtin, but unit tests (and real-world scripts)
    // expect `eval("...")` to work. Treat an identifier call as direct eval and interpret the
    // argument string in the current environment.
    //
    // This is intentionally minimal but spec-shaped:
    // - Arguments are evaluated left-to-right (including spreads).
    // - Non-String inputs are returned unchanged.
    if !expr.optional_chaining {
      match &*expr.callee.stx {
        Expr::Id(id) if id.stx.name == "eval" => return self.eval_direct_eval(scope, expr),
        Expr::IdPat(id) if id.stx.name == "eval" => return self.eval_direct_eval(scope, expr),
        _ => {}
      }
    }

    // Evaluate the callee and compute the `this` value for the call.
    let (callee_value, this_value) = match &*expr.callee.stx {
      Expr::Member(member) if member.stx.optional_chaining => {
        let base = self.eval_expr(scope, &member.stx.left)?;
        if is_nullish(base) {
          // Optional chaining short-circuit on the base value.
          return Ok(Value::Undefined);
        }
        let Value::Object(object) = base else {
          return Err(VmError::Unimplemented("member access on non-object"));
        };

        // Root `object` across property-key allocation in case it triggers GC.
        let mut key_scope = scope.reborrow();
        key_scope.push_root(Value::Object(object))?;
        let key_s = key_scope.alloc_string(&member.stx.right)?;
        let reference = Reference::Property {
          object,
          key: PropertyKey::from_string(key_s),
        };
        let callee_value = self.get_value_from_reference(&mut key_scope, &reference)?;
        (callee_value, Value::Object(object))
      }
      Expr::ComputedMember(member) if member.stx.optional_chaining => {
        let base = self.eval_expr(scope, &member.stx.object)?;
        if is_nullish(base) {
          return Ok(Value::Undefined);
        }
        let Value::Object(object) = base else {
          return Err(VmError::Unimplemented("computed member access on non-object"));
        };

        // Root `object` across key evaluation + `ToPropertyKey`, which may allocate and trigger GC.
        let mut key_scope = scope.reborrow();
        key_scope.push_root(Value::Object(object))?;
        let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
        key_scope.push_root(member_value)?;
        let key = key_scope.heap_mut().to_property_key(member_value)?;
        let reference = Reference::Property { object, key };
        let callee_value = self.get_value_from_reference(&mut key_scope, &reference)?;
        (callee_value, Value::Object(object))
      }
      Expr::Member(_) | Expr::ComputedMember(_) | Expr::Id(_) | Expr::IdPat(_) => {
        let reference = self.eval_reference(scope, &expr.callee)?;
        let this_value = match reference {
          Reference::Property { object, .. } => Value::Object(object),
          _ => Value::Undefined,
        };

        let mut callee_scope = scope.reborrow();
        self.root_reference(&mut callee_scope, &reference)?;
        let callee_value = self.get_value_from_reference(&mut callee_scope, &reference)?;
        (callee_value, this_value)
      }
      _ => {
        let callee_value = self.eval_expr(scope, &expr.callee)?;
        (callee_value, Value::Undefined)
      }
    };

    // Optional call: if the callee is nullish, return `undefined` without evaluating args.
    if expr.optional_chaining && is_nullish(callee_value) {
      return Ok(Value::Undefined);
    }

    // Root callee/this/args for the duration of the call.
    let mut call_scope = scope.reborrow();
    call_scope.push_roots(&[callee_value, this_value])?;

    let mut args: Vec<Value> = Vec::new();
    args
      .try_reserve_exact(expr.arguments.len())
      .map_err(|_| VmError::OutOfMemory)?;
    for arg in &expr.arguments {
      if arg.stx.spread {
        let spread_value = self.eval_expr(&mut call_scope, &arg.stx.value)?;
        call_scope.push_root(spread_value)?;

        let mut iter = iterator::get_iterator(self.vm, &mut call_scope, spread_value)?;
        call_scope.push_roots(&[iter.iterator, iter.next_method])?;

        while let Some(value) = iterator::iterator_step_value(self.vm, &mut call_scope, &mut iter)?
        {
          call_scope.push_root(value)?;
          args.try_reserve(1).map_err(|_| VmError::OutOfMemory)?;
          args.push(value);
        }
      } else {
        let value = self.eval_expr(&mut call_scope, &arg.stx.value)?;
        call_scope.push_root(value)?;
        args.push(value);
      }
    }
    self
      .vm
      .call(&mut call_scope, callee_value, this_value, &args)
  }

  fn eval_direct_eval(&mut self, scope: &mut Scope<'_>, expr: &CallExpr) -> Result<Value, VmError> {
    let mut call_scope = scope.reborrow();
    let mut args: Vec<Value> = Vec::new();
    args
      .try_reserve_exact(expr.arguments.len())
      .map_err(|_| VmError::OutOfMemory)?;

    for arg in &expr.arguments {
      if arg.stx.spread {
        let spread_value = self.eval_expr(&mut call_scope, &arg.stx.value)?;
        call_scope.push_root(spread_value)?;

        let mut iter = iterator::get_iterator(self.vm, &mut call_scope, spread_value)?;
        call_scope.push_roots(&[iter.iterator, iter.next_method])?;

        while let Some(value) = iterator::iterator_step_value(self.vm, &mut call_scope, &mut iter)? {
          call_scope.push_root(value)?;
          args.try_reserve(1).map_err(|_| VmError::OutOfMemory)?;
          args.push(value);
        }
      } else {
        let value = self.eval_expr(&mut call_scope, &arg.stx.value)?;
        call_scope.push_root(value)?;
        args.push(value);
      }
    }

    let arg0 = args.get(0).copied().unwrap_or(Value::Undefined);
    match arg0 {
      Value::String(s) => self.eval_direct_eval_string(&mut call_scope, s),
      other => Ok(other),
    }
  }

  fn eval_direct_eval_string(
    &mut self,
    scope: &mut Scope<'_>,
    source_string: GcString,
  ) -> Result<Value, VmError> {
    let source = scope
      .heap()
      .get_string(source_string)?
      .to_utf8_lossy();

    let source = Arc::new(SourceText::new("<eval>", source));
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };
    let top = parse_with_options(&source.text, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;
    let strict = self.strict || detect_use_strict_directive(&top.stx.body);

    // Save and restore the runtime's source and lexical environment while running eval code. This
    // keeps nested function source spans aligned with the eval input.
    let prev_source = self.env.source();
    let prev_base_offset = self.env.base_offset();
    let prev_prefix_len = self.env.prefix_len();
    let prev_lexical_env = self.env.lexical_env;
    let prev_strict = self.strict;

    self.env.set_source_info(source.clone(), 0, 0);
    let eval_lex = scope.env_create(Some(prev_lexical_env))?;
    self.env.set_lexical_env(scope.heap_mut(), eval_lex);
    self.strict = strict;

    let result = (|| {
      self.hoist_var_decls(scope, &top.stx.body)?;
      let lex = self.env.lexical_env;
      self.hoist_lexical_decls_in_stmt_list(scope, lex, &top.stx.body)?;
      self.hoist_function_decls_in_stmt_list(scope, &top.stx.body)?;

      let completion = self.eval_stmt_list(scope, &top.stx.body)?;
      match completion {
        Completion::Normal(v) => Ok(v.unwrap_or(Value::Undefined)),
        Completion::Throw(v) => Err(VmError::Throw(v)),
        Completion::Return(_) => Err(VmError::Unimplemented("return in eval")),
        Completion::Break(..) => Err(VmError::Unimplemented("break in eval")),
        Completion::Continue(..) => Err(VmError::Unimplemented("continue in eval")),
      }
    })();

    self.strict = prev_strict;
    self.env.set_lexical_env(scope.heap_mut(), prev_lexical_env);
    self
      .env
      .set_source_info(prev_source, prev_base_offset, prev_prefix_len);

    result
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
        // Destructuring assignment patterns appear in expression position as `Expr::ObjPat` /
        // `Expr::ArrPat` nodes. These are not valid "references" and must be handled by pattern
        // binding.
        match &*expr.left.stx {
          Expr::ObjPat(_) | Expr::ArrPat(_) => {
            let value = self.eval_expr(scope, &expr.right)?;
            bind_assignment_target(
              self.vm,
              scope,
              self.env,
              &expr.left,
              value,
              self.strict,
              self.this,
            )?;
            Ok(value)
          }
          _ => {
            let reference = self.eval_reference(scope, &expr.left)?;
            let mut rhs_scope = scope.reborrow();
            self.root_reference(&mut rhs_scope, &reference)?;
            let value = self.eval_expr(&mut rhs_scope, &expr.right)?;
            rhs_scope.push_root(value)?;
            self.put_value_to_reference(&mut rhs_scope, &reference, value)?;
            Ok(value)
          }
        }
      }
      OperatorName::AssignmentAddition => match &*expr.left.stx {
        Expr::ObjPat(_) | Expr::ArrPat(_) => Err(VmError::Unimplemented(
          "assignment addition to destructuring patterns",
        )),
        _ => {
          let reference = self.eval_reference(scope, &expr.left)?;
          let mut op_scope = scope.reborrow();
          self.root_reference(&mut op_scope, &reference)?;

          let left = self.get_value_from_reference(&mut op_scope, &reference)?;
          // Root `left` across evaluation of the RHS in case it allocates and triggers GC.
          op_scope.push_root(left)?;
          let right = self.eval_expr(&mut op_scope, &expr.right)?;

          let value = self.addition_operator(&mut op_scope, left, right)?;
          op_scope.push_root(value)?;
          self.put_value_to_reference(&mut op_scope, &reference, value)?;
          Ok(value)
        }
      },
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
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(strict_equal(rhs_scope.heap(), left, right)?))
      }
      OperatorName::StrictInequality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(!strict_equal(rhs_scope.heap(), left, right)?))
      }
      OperatorName::Equality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        Ok(Value::Bool(abstract_equality(rhs_scope.heap_mut(), left, right)?))
      }
      OperatorName::Inequality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
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
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        self.addition_operator(&mut rhs_scope, left, right)
      }
      OperatorName::Multiplication => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        rhs_scope.push_root(right)?;

        let left_num = self.to_numeric(&mut rhs_scope, left)?;
        let right_num = self.to_numeric(&mut rhs_scope, right)?;
        match (left_num, right_num) {
          (NumericValue::Number(a), NumericValue::Number(b)) => Ok(Value::Number(a * b)),
          (NumericValue::BigInt(a), NumericValue::BigInt(b)) => {
            let Some(out) = a.checked_mul(b) else {
              return Err(VmError::Unimplemented("BigInt multiplication overflow"));
            };
            Ok(Value::BigInt(out))
          }
          _ => Err(throw_type_error(
            self.vm,
            &mut rhs_scope,
            "Cannot mix BigInt and other types",
          )?),
        }
      }
      OperatorName::Subtraction
      | OperatorName::Division
      | OperatorName::Remainder
      | OperatorName::LessThan
      | OperatorName::LessThanOrEqual
      | OperatorName::GreaterThan
      | OperatorName::GreaterThanOrEqual => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        // Root `right` for the duration of numeric conversion: `ToNumber` may allocate when called
        // on objects (via `ToPrimitive`).
        rhs_scope.push_root(right)?;
        let left_n = self.to_number_operator(&mut rhs_scope, left)?;
        let right_n = self.to_number_operator(&mut rhs_scope, right)?;

        match expr.operator {
          OperatorName::Subtraction => Ok(Value::Number(left_n - right_n)),
          OperatorName::Division => Ok(Value::Number(left_n / right_n)),
          OperatorName::Remainder => Ok(Value::Number(left_n % right_n)),
          OperatorName::LessThan => Ok(Value::Bool(left_n < right_n)),
          OperatorName::LessThanOrEqual => Ok(Value::Bool(left_n <= right_n)),
          OperatorName::GreaterThan => Ok(Value::Bool(left_n > right_n)),
          OperatorName::GreaterThanOrEqual => Ok(Value::Bool(left_n >= right_n)),
          _ => {
            debug_assert!(false, "unexpected operator in numeric binary op fast path");
            Err(VmError::InvariantViolation(
              "internal error: unexpected operator in numeric binary op",
            ))
          }
        }
      }
      _ => Err(VmError::Unimplemented("binary operator")),
    }
  }

  fn is_primitive_value(&self, value: Value) -> bool {
    !matches!(value, Value::Object(_))
  }

  fn to_primitive(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
    hint: ToPrimitiveHint,
  ) -> Result<Value, VmError> {
    let Value::Object(obj) = value else {
      return Ok(value);
    };

    // Root `obj` across property lookups / calls (which may allocate and trigger GC).
    let mut prim_scope = scope.reborrow();
    prim_scope.push_root(Value::Object(obj))?;

    // 1. GetMethod(input, @@toPrimitive).
    let to_prim_sym = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
      .well_known_symbols()
      .to_primitive;
    let to_prim_key = PropertyKey::from_symbol(to_prim_sym);
    let exotic = prim_scope.ordinary_get(self.vm, obj, to_prim_key, Value::Object(obj))?;

    if !matches!(exotic, Value::Undefined | Value::Null) {
      if !prim_scope.heap().is_callable(exotic)? {
        return Err(throw_type_error(self.vm, &mut prim_scope, "@@toPrimitive is not callable")?);
      }

      let hint_s = prim_scope.alloc_string(hint.as_str())?;
      prim_scope.push_root(Value::String(hint_s))?;
      let out = self.vm.call(&mut prim_scope, exotic, Value::Object(obj), &[Value::String(hint_s)])?;
      if self.is_primitive_value(out) {
        return Ok(out);
      }
      return Err(throw_type_error(
        self.vm,
        &mut prim_scope,
        "Cannot convert object to primitive value",
      )?);
    }

    // 2. OrdinaryToPrimitive.
    self.ordinary_to_primitive(&mut prim_scope, obj, hint)
  }

  fn ordinary_to_primitive(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    hint: ToPrimitiveHint,
  ) -> Result<Value, VmError> {
    let hint = match hint {
      ToPrimitiveHint::Default => ToPrimitiveHint::Number,
      other => other,
    };
    let methods = match hint {
      ToPrimitiveHint::String => ["toString", "valueOf"],
      ToPrimitiveHint::Number | ToPrimitiveHint::Default => ["valueOf", "toString"],
    };

    for name in methods {
      let key_s = scope.alloc_string(name)?;
      scope.push_root(Value::String(key_s))?;
      let key = PropertyKey::from_string(key_s);
      let method = scope.ordinary_get(self.vm, obj, key, Value::Object(obj))?;

      if matches!(method, Value::Undefined | Value::Null) {
        continue;
      }
      if !scope.heap().is_callable(method)? {
        continue;
      }

      let result = self.vm.call(scope, method, Value::Object(obj), &[])?;
      if self.is_primitive_value(result) {
        return Ok(result);
      }
    }

    Err(throw_type_error(
      self.vm,
      scope,
      "Cannot convert object to primitive value",
    )?)
  }

  fn to_number_operator(&mut self, scope: &mut Scope<'_>, value: Value) -> Result<f64, VmError> {
    // `ToNumber` includes `ToPrimitive` with a Number hint.
    let mut num_scope = scope.reborrow();
    num_scope.push_root(value)?;
    let prim = self.to_primitive(&mut num_scope, value, ToPrimitiveHint::Number)?;
    num_scope.push_root(prim)?;

    match to_number(num_scope.heap_mut(), prim) {
      Ok(n) => Ok(n),
      Err(VmError::TypeError(msg)) => Err(throw_type_error(self.vm, &mut num_scope, msg)?),
      Err(err) => Err(err),
    }
  }

  fn to_string_operator(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
  ) -> Result<GcString, VmError> {
    // `ToString` includes `ToPrimitive` with a String hint.
    let mut string_scope = scope.reborrow();
    string_scope.push_root(value)?;
    let prim = self.to_primitive(&mut string_scope, value, ToPrimitiveHint::String)?;
    string_scope.push_root(prim)?;
    debug_assert!(self.is_primitive_value(prim), "to_primitive returned object");

    match string_scope.heap_mut().to_string(prim) {
      Ok(s) => Ok(s),
      Err(VmError::TypeError(msg)) => Err(throw_type_error(self.vm, &mut string_scope, msg)?),
      Err(err) => Err(err),
    }
  }

  fn addition_operator(
    &mut self,
    scope: &mut Scope<'_>,
    left: Value,
    right: Value,
  ) -> Result<Value, VmError> {
    // Root inputs and intermediates for the duration of the operation: `+` may allocate
    // (string concatenation, ToString) and thus trigger GC.
    let mut add_scope = scope.reborrow();
    add_scope.push_root(left)?;
    add_scope.push_root(right)?;

    // ECMA-262 AdditionOperator (+): ToPrimitive (default), then string concat if either side is a
    // string; otherwise numeric addition.
    let left_prim = self.to_primitive(&mut add_scope, left, ToPrimitiveHint::Default)?;
    add_scope.push_root(left_prim)?;
    let right_prim = self.to_primitive(&mut add_scope, right, ToPrimitiveHint::Default)?;
    add_scope.push_root(right_prim)?;

    if matches!(left_prim, Value::String(_)) || matches!(right_prim, Value::String(_)) {
      let left_s = self.to_string_operator(&mut add_scope, left_prim)?;
      add_scope.push_root(Value::String(left_s))?;
      let right_s = self.to_string_operator(&mut add_scope, right_prim)?;
      add_scope.push_root(Value::String(right_s))?;

      let left_units = add_scope.heap().get_string(left_s)?.as_code_units();
      let right_units = add_scope.heap().get_string(right_s)?.as_code_units();

      let total_len = left_units
        .len()
        .checked_add(right_units.len())
        .ok_or(VmError::OutOfMemory)?;
      let mut units: Vec<u16> = Vec::new();
      units
        .try_reserve_exact(total_len)
        .map_err(|_| VmError::OutOfMemory)?;
      units.extend_from_slice(left_units);
      units.extend_from_slice(right_units);

      let s = add_scope.alloc_string_from_u16_vec(units)?;
      Ok(Value::String(s))
    } else {
      let left_num = self.to_numeric(&mut add_scope, left_prim)?;
      let right_num = self.to_numeric(&mut add_scope, right_prim)?;
      Ok(match (left_num, right_num) {
        (NumericValue::Number(a), NumericValue::Number(b)) => Value::Number(a + b),
        (NumericValue::BigInt(a), NumericValue::BigInt(b)) => {
          let Some(out) = a.checked_add(b) else {
            return Err(VmError::Unimplemented("BigInt addition overflow"));
          };
          Value::BigInt(out)
        }
        _ => return Err(throw_type_error(self.vm, &mut add_scope, "Cannot mix BigInt and other types")?),
      })
    }
  }

  fn to_numeric(&mut self, scope: &mut Scope<'_>, value: Value) -> Result<NumericValue, VmError> {
    // ECMA-262 `ToNumeric`: ToPrimitive (hint Number), then return BigInt directly or convert to
    // Number.
    let prim = self.to_primitive(scope, value, ToPrimitiveHint::Number)?;
    match prim {
      Value::BigInt(b) => Ok(NumericValue::BigInt(b)),
      other => match to_number(scope.heap_mut(), other) {
        Ok(n) => Ok(NumericValue::Number(n)),
        Err(VmError::TypeError(msg)) => Err(throw_type_error(self.vm, scope, msg)?),
        Err(err) => Err(err),
      },
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

fn function_length(func: &parse_js::ast::func::Func) -> u32 {
  // ECMA-262 `length` is the number of parameters before the first one with a
  // default/rest.
  let mut len: u32 = 0;
  for param in func.parameters.iter() {
    if param.stx.rest || param.stx.default_value.is_some() {
      break;
    }
    len = len.saturating_add(1);
  }
  len
}

pub(crate) fn run_ecma_function(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  env: &mut RuntimeEnv,
  source: Arc<SourceText>,
  base_offset: u32,
  prefix_len: u32,
  strict: bool,
  this: Value,
  func: &Node<Func>,
  args: &[Value],
) -> Result<Value, VmError> {
  if func.stx.async_ || func.stx.generator {
    return Err(VmError::Unimplemented("async/generator functions"));
  }
  env.set_source_info(source, base_offset, prefix_len);

  let Some(body) = &func.stx.body else {
    return Err(VmError::Unimplemented("function without body"));
  };

  let mut evaluator = Evaluator { vm, env, strict, this };

  // Bind parameters.
  for (idx, param) in func.stx.parameters.iter().enumerate() {
    if param.stx.rest || param.stx.default_value.is_some() {
      return Err(VmError::Unimplemented("non-simple function parameters"));
    }
    let value = args.get(idx).copied().unwrap_or(Value::Undefined);
    bind_pattern(
      evaluator.vm,
      scope,
      evaluator.env,
      &param.stx.pattern.stx.pat.stx,
      value,
      BindingKind::Let,
      evaluator.strict,
      evaluator.this,
    )?;
  }

  // Create a minimal `arguments` object for non-arrow functions.
  //
  // test262's harness expects `arguments` to exist and be array-like (`length`, indexed elements).
  // We do not implement mapped arguments objects yet.
  if !func.stx.arrow && !scope.heap().env_has_binding(evaluator.env.lexical_env, "arguments")? {
    let intr = evaluator
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;

    let args_obj = scope.alloc_object()?;
    scope.push_root(Value::Object(args_obj))?;
    scope
      .heap_mut()
      .object_set_prototype(args_obj, Some(intr.object_prototype()))?;

    let len = args.len() as f64;
    let len_key = PropertyKey::from_string(scope.alloc_string("length")?);
    scope.define_property(
      args_obj,
      len_key,
      PropertyDescriptor {
        enumerable: false,
        configurable: true,
        kind: PropertyKind::Data {
          value: Value::Number(len),
          writable: true,
        },
      },
    )?;

    for (i, v) in args.iter().copied().enumerate() {
      let mut idx_scope = scope.reborrow();
      idx_scope.push_root(Value::Object(args_obj))?;
      idx_scope.push_root(v)?;
      let key = PropertyKey::from_string(idx_scope.alloc_string(&i.to_string())?);
      idx_scope.define_property(args_obj, key, global_var_desc(v))?;
    }

    scope.env_create_mutable_binding(evaluator.env.lexical_env, "arguments")?;
    scope
      .heap_mut()
      .env_initialize_binding(evaluator.env.lexical_env, "arguments", Value::Object(args_obj))?;
  }

  match body {
    FuncBody::Expression(expr) => evaluator.eval_expr(scope, expr),
    FuncBody::Block(stmts) => {
      evaluator.hoist_var_decls(scope, stmts)?;
      let func_env = evaluator.env.lexical_env;
      evaluator.hoist_lexical_decls_in_stmt_list(scope, func_env, stmts)?;
      evaluator.hoist_function_decls_in_stmt_list(scope, stmts)?;

      let completion = evaluator.eval_stmt_list(scope, stmts)?;
      match completion {
        Completion::Normal(_) => Ok(Value::Undefined),
        Completion::Return(v) => Ok(v),
        Completion::Throw(v) => Err(VmError::Throw(v)),
        Completion::Break(..) => Err(VmError::Unimplemented("break outside of loop")),
        Completion::Continue(..) => Err(VmError::Unimplemented("continue outside of loop")),
      }
    }
  }
}

pub(crate) fn eval_expr(
  vm: &mut Vm,
  env: &mut RuntimeEnv,
  strict: bool,
  this: Value,
  scope: &mut Scope<'_>,
  expr: &Node<Expr>,
) -> Result<Value, VmError> {
  let mut evaluator = Evaluator { vm, env, strict, this };
  evaluator.eval_expr(scope, expr)
}

fn is_nullish(value: Value) -> bool {
  matches!(value, Value::Undefined | Value::Null)
}

fn to_boolean(heap: &Heap, value: Value) -> Result<bool, VmError> {
  Ok(match value {
    Value::Undefined | Value::Null => false,
    Value::Bool(b) => b,
    Value::Number(n) => n != 0.0 && !n.is_nan(),
    Value::BigInt(n) => !n.is_zero(),
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
    Value::BigInt(_) => "bigint",
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
    (Value::BigInt(x), Value::BigInt(y)) => x == y,
    (Value::String(x), Value::String(y)) => heap.get_string(x)? == heap.get_string(y)?,
    (Value::Symbol(x), Value::Symbol(y)) => x == y,
    (Value::Object(x), Value::Object(y)) => x == y,
    _ => false,
  })
}
