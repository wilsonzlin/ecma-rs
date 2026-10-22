use crate::destructure::{bind_assignment_target, bind_pattern, BindingKind};
use crate::error_object::new_error;
use crate::iterator;
use crate::ops::{abstract_equality, to_number};
use crate::{
  EnvRootId, GcEnv, GcObject, GcString, Heap, JsBigInt, NativeCall, PropertyDescriptor,
  PropertyDescriptorPatch, PropertyKey, PropertyKind, Realm, RootId, Scope, SourceText, StackFrame,
  Value, Vm, VmError, VmHost, VmHostHooks, VmJobContext,
};
use diagnostics::{Diagnostic, FileId};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMemberType};
use parse_js::ast::expr::lit::{
  LitArrElem, LitArrExpr, LitBigIntExpr, LitBoolExpr, LitNumExpr, LitObjExpr, LitRegexExpr,
  LitStrExpr, LitTemplateExpr, LitTemplatePart,
};
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::expr::{
  ArrowFuncExpr, BinaryExpr, CallExpr, ClassExpr, ComputedMemberExpr, CondExpr, Expr, FuncExpr,
  IdExpr, MemberExpr, TaggedTemplateExpr, UnaryExpr, UnaryPostfixExpr,
};
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::{literal_string_code_units, Node, ParenthesizedExpr};
use parse_js::ast::stmt::decl::{ClassDecl, FuncDecl, PatDecl, VarDecl, VarDeclMode};
use parse_js::ast::stmt::{
  BlockStmt, CatchBlock, DoWhileStmt, ExprStmt, ForBody, ForInOfLhs, ForInStmt, ForOfStmt,
  ForTripleStmt, IfStmt, LabelStmt, ReturnStmt, Stmt, SwitchStmt, ThrowStmt, TryStmt, WhileStmt,
  WithStmt,
};
use parse_js::operator::OperatorName;
use parse_js::token::TT;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::collections::HashSet;
use std::sync::Arc;

use crate::function::ThisMode;
use crate::vm::{EcmaFunctionKind, ParsedProgram};

/// `IsAnonymousFunctionDefinition` (ECMA-262), looking through cover parentheses.
fn is_anonymous_function_definition_node(expr: &Node<Expr>) -> bool {
  match &*expr.stx {
    Expr::Func(f) => f.stx.name.is_none(),
    Expr::ArrowFunc(_) => true,
    Expr::Class(c) => c.stx.name.is_none(),
    _ => false,
  }
}

/// A `throw` completion value paired with a captured stack trace.
#[derive(Clone, Debug, PartialEq)]
pub struct Thrown {
  pub value: Value,
  pub stack: Vec<StackFrame>,
}

/// An ECMAScript completion record (ECMA-262).
///
/// We model the "empty" completion value explicitly as `None` so statement-list evaluation can
/// implement `UpdateEmpty` correctly (e.g. `1; if (true) {}` should evaluate to `1`).
#[derive(Clone, Debug, PartialEq)]
pub enum Completion {
  Normal(Option<Value>),
  Throw(Thrown),
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
      Completion::Throw(thrown) => Some(thrown.value),
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

fn global_var_binding_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: true,
    configurable: false,
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
  let value =
    crate::error_object::new_error(scope, intr.type_error_prototype(), "TypeError", message)?;
  Ok(VmError::Throw(value))
}

fn throw_range_error(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> Result<VmError, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let value =
    crate::error_object::new_error(scope, intr.range_error_prototype(), "RangeError", message)?;
  Ok(VmError::Throw(value))
}

fn throw_reference_error(
  vm: &Vm,
  scope: &mut Scope<'_>,
  message: &str,
) -> Result<VmError, VmError> {
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

fn throw_syntax_error(vm: &Vm, scope: &mut Scope<'_>, message: &str) -> Result<VmError, VmError> {
  let intr = vm
    .intrinsics()
    .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
  let value =
    crate::error_object::new_error(scope, intr.syntax_error_prototype(), "SyntaxError", message)?;
  Ok(VmError::Throw(value))
}

fn syntax_error(loc: parse_js::loc::Loc, message: impl Into<String>) -> VmError {
  let span = loc.to_diagnostics_span(FileId(0));
  VmError::Syntax(vec![Diagnostic::error("VMJS0002", message, span)])
}

#[derive(Clone, Copy, Debug)]
enum VarEnv {
  GlobalObject,
  Env(GcEnv),
}

#[derive(Debug)]
pub(crate) struct RuntimeEnv {
  global_object: GcObject,
  /// Realm global declarative Environment Record (outermost). Used by indirect `eval`.
  global_lexical_env: GcEnv,
  lexical_env: GcEnv,
  lexical_root: EnvRootId,
  var_env: VarEnv,
  source: Arc<SourceText>,
  base_offset: u32,
  prefix_len: u32,
}

impl RuntimeEnv {
  fn new(heap: &mut Heap, global_object: GcObject) -> Result<Self, VmError> {
    // Root the global object across env allocation in case it triggers GC.
    let mut scope = heap.scope();
    scope.push_root(Value::Object(global_object))?;

    let lexical_env = scope.env_create(None)?;
    let lexical_root = scope.heap_mut().add_env_root(lexical_env)?;

    Ok(Self {
      global_object,
      global_lexical_env: lexical_env,
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
    // Walk to the outermost environment as the realm global declarative env.
    let mut global_lexical_env = lexical_env;
    while let Some(outer) = scope.heap().env_outer(global_lexical_env)? {
      global_lexical_env = outer;
    }

    Ok(Self {
      global_object,
      global_lexical_env,
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

  fn set_var_env(&mut self, env: GcEnv) {
    self.var_env = VarEnv::Env(env);
  }

  pub(crate) fn set_source_info(
    &mut self,
    source: Arc<SourceText>,
    base_offset: u32,
    prefix_len: u32,
  ) {
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

  pub(crate) fn global_lexical_env(&self) -> GcEnv {
    self.global_lexical_env
  }

  /// Temporarily retarget the realm global / global lexical env (cross-realm `eval`).
  pub(crate) fn set_realm_globals(&mut self, global_object: GcObject, global_lexical_env: GcEnv) {
    self.global_object = global_object;
    self.global_lexical_env = global_lexical_env;
  }

  pub(crate) fn lexical_env(&self) -> GcEnv {
    self.lexical_env
  }

  /// The variable environment, when it is an environment record (function contexts).
  pub(crate) fn var_env_env(&self) -> Option<GcEnv> {
    match self.var_env {
      VarEnv::GlobalObject => None,
      VarEnv::Env(env) => Some(env),
    }
  }

  fn resolve_lexical_binding(
    &self,
    vm: &mut Vm,
    host: &mut dyn VmHost,
    hooks: &mut dyn VmHostHooks,
    scope: &mut Scope<'_>,
    name: &str,
  ) -> Result<Option<GcEnv>, VmError> {
    let mut current = Some(self.lexical_env);
    while let Some(env) = current {
      match scope.heap().env_record_kind(env)? {
        crate::env::EnvRecordKind::Declarative => {
          if scope.heap().env_has_binding(env, name)? {
            return Ok(Some(env));
          }
        }
        crate::env::EnvRecordKind::Object {
          binding_object,
          with_environment,
        } => {
          if Self::object_env_has_binding(
            vm,
            host,
            hooks,
            scope,
            binding_object,
            with_environment,
            name,
          )? {
            return Ok(Some(env));
          }
        }
      }
      current = scope.heap().env_outer(env)?;
    }
    Ok(None)
  }

  /// Object Environment Record `HasBinding` (§9.1.1.2.1), including `@@unscopables` when
  /// `withEnvironment` is set.
  fn object_env_has_binding(
    vm: &mut Vm,
    host: &mut dyn VmHost,
    hooks: &mut dyn VmHostHooks,
    scope: &mut Scope<'_>,
    binding_object: GcObject,
    with_environment: bool,
    name: &str,
  ) -> Result<bool, VmError> {
    let mut s = scope.reborrow();
    s.push_root(Value::Object(binding_object))?;
    let key_s = s.alloc_string(name)?;
    s.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);
    if !s.ordinary_has_property(binding_object, key)? {
      return Ok(false);
    }
    if !with_environment {
      return Ok(true);
    }
    let unscopables_sym = vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
      .well_known_symbols()
      .unscopables;
    let unscopables_key = PropertyKey::from_symbol(unscopables_sym);
    let receiver = Value::Object(binding_object);
    let unscopables = s.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      binding_object,
      unscopables_key,
      receiver,
    )?;
    let Value::Object(unscopables_obj) = unscopables else {
      return Ok(true);
    };
    s.push_root(Value::Object(unscopables_obj))?;
    let blocked = s.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      unscopables_obj,
      key,
      Value::Object(unscopables_obj),
    )?;
    Ok(!to_boolean(s.heap(), blocked)?)
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

        key_scope.define_property(
          global_object,
          key,
          global_var_binding_desc(Value::Undefined),
        )?;
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
    host: &mut dyn VmHost,
    hooks: &mut dyn VmHostHooks,
    scope: &mut Scope<'_>,
    name: &str,
  ) -> Result<Option<Value>, VmError> {
    if let Some(env) = self.resolve_lexical_binding(vm, host, hooks, scope, name)? {
      match scope.heap().env_record_kind(env)? {
        crate::env::EnvRecordKind::Declarative => {
          match scope.heap().env_get_binding_value(env, name, false) {
            Ok(v) => return Ok(Some(v)),
            // TDZ sentinel from `Heap::{env_get_binding_value, env_set_mutable_binding}`.
            Err(VmError::Throw(Value::Null)) => {
              let msg = format!("Cannot access '{name}' before initialization");
              return Err(throw_reference_error(vm, scope, &msg)?);
            }
            Err(err) => return Err(err),
          }
        }
        crate::env::EnvRecordKind::Object { binding_object, .. } => {
          let mut key_scope = scope.reborrow();
          key_scope.push_root(Value::Object(binding_object))?;
          let key_s = key_scope.alloc_string(name)?;
          key_scope.push_root(Value::String(key_s))?;
          let key = PropertyKey::from_string(key_s);
          let receiver = Value::Object(binding_object);
          return Ok(Some(key_scope.ordinary_get_with_host_and_hooks(
            vm,
            host,
            hooks,
            binding_object,
            key,
            receiver,
          )?));
        }
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
    Ok(Some(key_scope.ordinary_get_with_host_and_hooks(
      vm,
      host,
      hooks,
      global_object,
      key,
      receiver,
    )?))
  }

  pub(crate) fn set(
    &mut self,
    vm: &mut Vm,
    host: &mut dyn VmHost,
    hooks: &mut dyn VmHostHooks,
    scope: &mut Scope<'_>,
    name: &str,
    value: Value,
    strict: bool,
  ) -> Result<(), VmError> {
    if let Some(env) = self.resolve_lexical_binding(vm, host, hooks, scope, name)? {
      match scope.heap().env_record_kind(env)? {
        crate::env::EnvRecordKind::Declarative => {
          match scope
            .heap_mut()
            .env_set_mutable_binding(env, name, value, strict)
          {
            Ok(()) => return Ok(()),
            // TDZ sentinel from `Heap::{env_get_binding_value, env_set_mutable_binding}`.
            Err(VmError::Throw(Value::Null)) => {
              let msg = format!("Cannot access '{name}' before initialization");
              return Err(throw_reference_error(vm, scope, &msg)?);
            }
            // Immutable-binding assignment sentinel from `Heap::env_set_mutable_binding`
            // (strict bindings / strict-mode code). Sloppy named-fn-expr names return Ok there.
            Err(VmError::Throw(Value::Undefined)) => {
              return Err(throw_type_error(
                vm,
                scope,
                "Assignment to constant variable.",
              )?);
            }
            Err(err) => return Err(err),
          }
        }
        crate::env::EnvRecordKind::Object { binding_object, .. } => {
          let mut key_scope = scope.reborrow();
          key_scope.push_root(Value::Object(binding_object))?;
          key_scope.push_root(value)?;
          let key_s = key_scope.alloc_string(name)?;
          key_scope.push_root(Value::String(key_s))?;
          let key = PropertyKey::from_string(key_s);
          let receiver = Value::Object(binding_object);
          let ok = key_scope.ordinary_set_with_host_and_hooks(
            vm,
            host,
            hooks,
            binding_object,
            key,
            value,
            receiver,
          )?;
          if !ok && strict {
            let msg = format!("Cannot assign to read only property '{name}'");
            return Err(throw_type_error(vm, &mut key_scope, &msg)?);
          }
          return Ok(());
        }
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
        PropertyKind::Data {
          writable: false, ..
        } => {
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
    vm: &mut Vm,
    scope: &mut Scope<'_>,
    name: &str,
    value: Value,
    strict: bool,
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
            PropertyKind::Data {
              writable: false, ..
            } => {
              // SetMutableBinding / PutValue: non-writable globals (Infinity/NaN/undefined)
              // reject silently in sloppy mode and throw TypeError in strict mode.
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

        // If the binding was inherited through the prototype chain, define an own data property.
        key_scope.define_property(global_object, key, global_var_binding_desc(value))?;
        Ok(())
      }
      VarEnv::Env(env) => outer_scope
        .heap_mut()
        .env_set_mutable_binding(env, name, value, strict),
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
    vm.register_realm(
      realm.global_object(),
      realm.id(),
      *realm.intrinsics(),
      env.global_lexical_env,
      None,
      true,
    );
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

  /// Registers a native call handler and exposes it as a global binding.
  ///
  /// This is a convenience API for embeddings (e.g. FastRender) that need to expose host functions
  /// (`setTimeout`, DOM bindings, etc.) to interpreted scripts.
  pub fn register_global_native_function(
    &mut self,
    name: &str,
    call: NativeCall,
    length: u32,
  ) -> Result<GcObject, VmError> {
    let call_id = self.vm.register_native_call(call)?;

    let mut scope = self.heap.scope();
    let func_name = scope.alloc_string(name)?;
    let func = scope.alloc_native_function(call_id, None, func_name, length)?;

    // Root the function object across allocations while defining it on the global object.
    scope.push_root(Value::Object(func))?;

    let key = PropertyKey::from_string(scope.alloc_string(name)?);
    scope.define_property(
      self.env.global_object(),
      key,
      global_var_desc(Value::Object(func)),
    )?;

    Ok(func)
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`).
  pub fn exec_script(&mut self, source: &str) -> Result<Value, VmError> {
    let mut host = ();
    self.exec_script_with_host(&mut host, source)
  }

  /// Parse and execute a classic script, using a custom host hook implementation.
  ///
  /// This is intended for embeddings that need Promise jobs enqueued by the script to be routed via
  /// `VmHostHooks::host_enqueue_promise_job` (for example, an HTML microtask queue) instead of the
  /// VM-owned microtask queue used by [`JsRuntime::exec_script`].
  pub fn exec_script_with_hooks(
    &mut self,
    hooks: &mut dyn VmHostHooks,
    source: &str,
  ) -> Result<Value, VmError> {
    self.exec_script_source_with_hooks(hooks, Arc::new(SourceText::new("<inline>", source)))
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`).
  pub fn exec_script_source(&mut self, source: Arc<SourceText>) -> Result<Value, VmError> {
    let mut host = ();
    self.exec_script_source_with_host(&mut host, source)
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`) with an explicit
  /// embedder host context.
  pub fn exec_script_with_host(
    &mut self,
    host: &mut dyn VmHost,
    source: &str,
  ) -> Result<Value, VmError> {
    self.exec_script_source_with_host(host, Arc::new(SourceText::new("<inline>", source)))
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`) with an explicit
  /// embedder host context.
  pub fn exec_script_source_with_host(
    &mut self,
    host: &mut dyn VmHost,
    source: Arc<SourceText>,
  ) -> Result<Value, VmError> {
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };
    let top = parse_with_options(&source.text, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;
    let strict = detect_use_strict_directive(&top.stx.body);
    let program = Arc::new(ParsedProgram { top });

    let global_object = self.realm.global_object();
    self.env.set_source_info(source.clone(), 0, 0);

    let (line, col) = source.line_col(0);
    let frame = StackFrame {
      function: None,
      source: source.name.clone(),
      line,
      col,
    };
    // Script evaluation needs a host hook implementation for Promise jobs. `Vm` stores a default
    // microtask queue inside itself, but we need to hold `&mut Vm` and `&mut dyn VmHostHooks`
    // simultaneously. Temporarily move the queue out so it can be passed as `hooks`.
    let mut hooks = std::mem::take(self.vm.microtask_queue_mut());

    let mut vm_frame = self.vm.enter_frame(frame)?;
    let mut program_guard = vm_frame.enter_program(program.clone());

    let mut scope = self.heap.scope();
    // In classic scripts, top-level `this` is the global object (even in strict mode).
    let global_this = Value::Object(global_object);
    let mut evaluator = Evaluator {
      vm: &mut *program_guard,
      host,
      hooks: &mut hooks,
      env: &mut self.env,
      strict,
      this: global_this,
      this_uninitialized: false,
      new_target: Value::Undefined,
      active_function: None,
    };

    let result: Result<Value, VmError> = (|| {
      evaluator.instantiate_script(&mut scope, &program.top.stx.body)?;

      let completion = evaluator.eval_stmt_list(&mut scope, &program.top.stx.body)?;
      match completion {
        Completion::Normal(v) => Ok(v.unwrap_or(Value::Undefined)),
        Completion::Throw(thrown) => Err(VmError::ThrowWithStack {
          value: thrown.value,
          stack: thrown.stack,
        }),
        Completion::Return(_) => Err(VmError::Unimplemented("return outside of function")),
        Completion::Break(..) => Err(VmError::Unimplemented("break outside of loop")),
        Completion::Continue(..) => Err(VmError::Unimplemented("continue outside of loop")),
      }
    })();

    // Restore the VM's microtask queue so the embedding can run a microtask checkpoint later.
    // Drop the program guard first so we can reach the frame guard's microtask queue slot.
    drop(program_guard);
    *vm_frame.microtask_queue_mut() = hooks;

    result
  }

  /// Parse and execute a classic script (ECMAScript dialect, `SourceType::Script`) using a custom
  /// host hook implementation.
  pub fn exec_script_source_with_hooks(
    &mut self,
    hooks: &mut dyn VmHostHooks,
    source: Arc<SourceText>,
  ) -> Result<Value, VmError> {
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };
    let top = parse_with_options(&source.text, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;
    let strict = detect_use_strict_directive(&top.stx.body);
    let program = Arc::new(ParsedProgram { top });

    let global_object = self.realm.global_object();
    self.env.set_source_info(source.clone(), 0, 0);

    let (line, col) = source.line_col(0);
    let frame = StackFrame {
      function: None,
      source: source.name.clone(),
      line,
      col,
    };

    let exec_ctx = crate::ExecutionContext {
      realm: self.realm.id(),
      script_or_module: None,
    };
    let mut vm_ctx = self.vm.execution_context_guard(exec_ctx);
    let prev_host = vm_ctx.push_active_host_hooks(hooks);

    let result = (|| {
      let mut vm_frame = vm_ctx.enter_frame(frame)?;
      let mut program_guard = vm_frame.enter_program(program.clone());

      let mut dummy_host = ();

      let mut scope = self.heap.scope();
      // In classic scripts, top-level `this` is the global object (even in strict mode).
      let global_this = Value::Object(global_object);
      let mut evaluator = Evaluator {
        vm: &mut *program_guard,
        host: &mut dummy_host,
        hooks,
        env: &mut self.env,
        strict,
        this: global_this,
        this_uninitialized: false,
        new_target: Value::Undefined,
        active_function: None,
      };

      evaluator.instantiate_script(&mut scope, &program.top.stx.body)?;

      let completion = evaluator.eval_stmt_list(&mut scope, &program.top.stx.body)?;
      match completion {
        Completion::Normal(v) => Ok(v.unwrap_or(Value::Undefined)),
        Completion::Throw(thrown) => Err(VmError::ThrowWithStack {
          value: thrown.value,
          stack: thrown.stack,
        }),
        Completion::Return(_) => Err(VmError::Unimplemented("return outside of function")),
        Completion::Break(..) => Err(VmError::Unimplemented("break outside of loop")),
        Completion::Continue(..) => Err(VmError::Unimplemented("continue outside of loop")),
      }
    })();

    vm_ctx.pop_active_host_hooks(prev_host);
    drop(vm_ctx);

    // As a safety net, drain any Promise jobs that were enqueued onto the VM-owned microtask queue
    // into the embedding's host hook implementation.
    while let Some((realm, job)) = self.vm.microtask_queue_mut().pop_front() {
      hooks.host_enqueue_promise_job(job, realm);
    }

    result
  }
}

impl Drop for JsRuntime {
  fn drop(&mut self) {
    // Unregister persistent roots created by global lexical bindings and the realm. This keeps heap
    // reuse in tests/embeddings from accumulating roots and satisfies `Realm`'s debug assertion.
    self.vm.teardown_secondary_realms(&mut self.heap);
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

pub(crate) struct Evaluator<'a> {
  vm: &'a mut Vm,
  host: &'a mut dyn VmHost,
  hooks: &'a mut dyn VmHostHooks,
  env: &'a mut RuntimeEnv,
  strict: bool,
  this: Value,
  /// When true, `this` is unbound (derived constructor before `super()`).
  this_uninitialized: bool,
  new_target: Value,
  /// Active ECMAScript function object (`envRec.[[FunctionObject]]`) for `super`.
  active_function: Option<GcObject>,
}

#[derive(Clone, Copy, Debug)]
enum Reference<'a> {
  Binding(&'a str),
  /// Property reference. `base` may be a primitive (PutValue ToObject / GetV); `null`/`undefined`
  /// bases are rejected when the reference is formed.
  Property {
    base: Value,
    key: PropertyKey,
  },
}

/// Result of evaluating one link of an optional chain (ECMA-262 §13.3.9).
///
/// A chain short-circuits when a `?.` link is applied to a nullish base; from that point the entire
/// remaining `OptionalExpression` yields `undefined`, so `ShortCircuit` must propagate up through
/// the enclosing non-optional links until the chain root ends.
#[derive(Clone, Copy, Debug)]
enum ChainVal {
  /// The chain short-circuited (a `?.` saw a nullish base). Overall result is `undefined`.
  ShortCircuit,
  /// A produced value, together with the `this` value a subsequent optional `Call` link would use
  /// if this link is the callee (i.e. the base object/primitive of a member access, else
  /// `undefined`).
  Value { value: Value, this: Value },
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

  #[inline]
  fn call(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    match self.vm.call_with_host_and_hooks(
      &mut *self.host,
      scope,
      &mut *self.hooks,
      callee,
      this,
      args,
    ) {
      // Language-level TypeError so FDI / expression evaluation can reject async
      // promises (e.g. `async function f(x = null()) {}`).
      Err(VmError::NotCallable) => Err(throw_type_error(self.vm, scope, "value is not callable")?),
      other => other,
    }
  }

  #[inline]
  fn construct(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    args: &[Value],
    new_target: Value,
  ) -> Result<Value, VmError> {
    match self.vm.construct_with_host_and_hooks(
      &mut *self.host,
      scope,
      &mut *self.hooks,
      callee,
      args,
      new_target,
    ) {
      Err(VmError::NotConstructable) => Err(throw_type_error(
        self.vm,
        scope,
        "value is not a constructor",
      )?),
      other => other,
    }
  }

  fn instantiate_script(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    self.instantiate_stmt_list(scope, stmts)
  }

  /// Install mapped `arguments` accessors (ECMA-262 `CreateMappedArgumentsObject`).
  ///
  /// For each unique formal name (last occurrence wins), when that formal's index
  /// is within `argumentsList`, replace the ordinary data property with getters/
  /// setters that read/write the parameter Environment Record binding.
  fn wire_mapped_arguments(
    &mut self,
    scope: &mut Scope<'_>,
    args_obj: GcObject,
    func: &Func,
    args_len: usize,
  ) -> Result<(), VmError> {
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    let getter_id = intr.arguments_arg_getter_call();
    let setter_id = intr.arguments_arg_setter_call();
    let param_env = self.env.lexical_env;

    let mut mapped_names = HashSet::<String>::new();
    // Spec walks formals from the end so the last duplicate name owns the map entry.
    for (idx, param) in func.parameters.iter().enumerate().rev() {
      let Pat::Id(id) = &*param.stx.pattern.stx.pat.stx else {
        continue;
      };
      let name = id.stx.name.as_str();
      if !mapped_names.insert(name.to_string()) {
        continue;
      }
      if idx >= args_len {
        continue;
      }

      let mut map_scope = scope.reborrow();
      map_scope.push_root(Value::Object(args_obj))?;
      let name_s = map_scope.alloc_string(name)?;
      map_scope.push_root(Value::String(name_s))?;
      let get_name = map_scope.alloc_string("get")?;
      map_scope.push_root(Value::String(get_name))?;
      let set_name = map_scope.alloc_string("set")?;
      map_scope.push_root(Value::String(set_name))?;

      let getter = map_scope.alloc_native_function_with_slots(
        getter_id,
        None,
        get_name,
        0,
        &[Value::String(name_s)],
      )?;
      map_scope
        .heap_mut()
        .set_function_closure_env(getter, Some(param_env))?;
      map_scope.push_root(Value::Object(getter))?;
      let setter = map_scope.alloc_native_function_with_slots(
        setter_id,
        None,
        set_name,
        1,
        &[Value::String(name_s)],
      )?;
      map_scope
        .heap_mut()
        .set_function_closure_env(setter, Some(param_env))?;
      map_scope.push_root(Value::Object(setter))?;

      let key = PropertyKey::from_string(map_scope.alloc_string(&idx.to_string())?);
      map_scope.define_property(
        args_obj,
        key,
        PropertyDescriptor {
          enumerable: true,
          configurable: true,
          kind: PropertyKind::Accessor {
            get: Value::Object(getter),
            set: Value::Object(setter),
          },
        },
      )?;
    }
    Ok(())
  }

  fn instantiate_function(
    &mut self,
    scope: &mut Scope<'_>,
    func: &Node<Func>,
    args: &[Value],
  ) -> Result<(), VmError> {
    let has_parameter_expressions =
      func.stx.parameters.iter().any(|p| {
        p.stx.default_value.is_some() || !matches!(&*p.stx.pattern.stx.pat.stx, Pat::Id(_))
      });

    // FunctionDeclarationInstantiation (§10.2.11): for non-strict functions with parameter
    // expressions, bind formals in a fresh LexicalEnvironment whose outer is the function env,
    // while VariableEnvironment stays the outer. That makes `eval("var a")` inside a default
    // for formal `a` throw SyntaxError (EvalDeclarationInstantiation walks lex→varEnv).
    let callee_env = self.env.lexical_env;
    let env_rec = if !self.strict && has_parameter_expressions {
      let param_lex = scope.env_create(Some(callee_env))?;
      self.env.set_lexical_env(scope.heap_mut(), param_lex);
      // var_env remains `callee_env` (set at call time to the same function env).
      param_lex
    } else {
      callee_env
    };

    // Pre-create all parameter bindings before evaluating default initializers so identifier
    // references during parameter evaluation observe TDZ semantics.
    for param in &func.stx.parameters {
      self.instantiate_lexical_names_from_pat(
        scope,
        env_rec,
        &param.stx.pattern.stx.pat.stx,
        param.loc,
        true,
      )?;
    }

    // Create a minimal `arguments` object for non-arrow functions.
    //
    // test262's harness expects `arguments` to exist and be array-like (`length`, indexed elements).
    // For non-strict functions with a simple parameter list we later wire mapped accessors
    // (CreateMappedArgumentsObject); otherwise this remains an unmapped ordinary object.
    //
    // `arguments` must be created before default parameter initializers run so defaults can read it.
    let mut arguments_obj: Option<GcObject> = None;
    if !func.stx.arrow
      && !scope
        .heap()
        .env_has_binding(self.env.lexical_env, "arguments")?
    {
      let intr = self
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

      scope.env_create_mutable_binding(self.env.lexical_env, "arguments")?;
      scope.heap_mut().env_initialize_binding(
        self.env.lexical_env,
        "arguments",
        Value::Object(args_obj),
      )?;
      arguments_obj = Some(args_obj);
    }

    // Bind parameters in order, evaluating default initializers as needed.
    for (idx, param) in func.stx.parameters.iter().enumerate() {
      if param.stx.rest {
        // Rest parameter: collect remaining args into an Array.
        let rest_slice = args.get(idx..).unwrap_or(&[]);
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;

        let mut rest_scope = scope.reborrow();
        let arr = rest_scope.alloc_array(0)?;
        rest_scope.push_root(Value::Object(arr))?;
        rest_scope
          .heap_mut()
          .object_set_prototype(arr, Some(intr.array_prototype()))?;

        for (i, v) in rest_slice.iter().copied().enumerate() {
          let mut elem_scope = rest_scope.reborrow();
          elem_scope.push_root(Value::Object(arr))?;
          elem_scope.push_root(v)?;
          let key_s = elem_scope.alloc_string(&i.to_string())?;
          elem_scope.push_root(Value::String(key_s))?;
          let key = PropertyKey::from_string(key_s);
          let ok = elem_scope.create_data_property(arr, key, v)?;
          if !ok {
            return Err(VmError::Unimplemented("CreateDataProperty returned false"));
          }
        }

        bind_pattern(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut rest_scope,
          self.env,
          &param.stx.pattern.stx.pat.stx,
          Value::Object(arr),
          BindingKind::Let,
          self.strict,
          self.this,
        )?;

        if idx + 1 != func.stx.parameters.len() {
          return Err(VmError::Unimplemented("rest parameter must be last"));
        }
        break;
      }

      let mut value = args.get(idx).copied().unwrap_or(Value::Undefined);
      if matches!(value, Value::Undefined) {
        if let Some(default_expr) = &param.stx.default_value {
          value = self.eval_expr(scope, default_expr)?;
        }
      }

      bind_pattern(
        self.vm,
        &mut *self.host,
        &mut *self.hooks,
        scope,
        self.env,
        &param.stx.pattern.stx.pat.stx,
        value,
        BindingKind::Let,
        self.strict,
        self.this,
      )?;
    }

    // CreateMappedArgumentsObject (§10.4.4.7): non-strict + simple parameter list.
    // Parameter bindings are initialized above; install accessors so `arguments[i]`
    // and the corresponding formal stay synchronized.
    if !self.strict {
      if let Some(args_obj) = arguments_obj {
        if is_simple_parameter_list(&func.stx) {
          self.wire_mapped_arguments(scope, args_obj, &func.stx, args.len())?;
        }
      }
    }

    // Body environments (§10.2.11):
    // - hasParameterExpressions: vars live in a fresh env whose outer is the parameter lex env
    //   (so body closures see params; eval-in-params vars stayed on the outer varEnv).
    // - non-strict: always a separate lexical env for top-level `let`/`const` so direct eval can
    //   detect var/let conflicts (`scope-body-lex-distinct`).
    let param_lex = self.env.lexical_env;
    let var_env = if has_parameter_expressions {
      let body_var = scope.env_create(Some(param_lex))?;
      self.env.set_var_env(body_var);
      body_var
    } else {
      // Params and vars share the function env.
      match self.env.var_env {
        VarEnv::Env(e) => e,
        VarEnv::GlobalObject => param_lex,
      }
    };
    if !self.strict {
      let body_lex = scope.env_create(Some(var_env))?;
      self.env.set_lexical_env(scope.heap_mut(), body_lex);
    } else if has_parameter_expressions {
      self.env.set_lexical_env(scope.heap_mut(), var_env);
    }

    if let Some(FuncBody::Block(stmts)) = &func.stx.body {
      self.instantiate_stmt_list(scope, stmts)?;
    }
    Ok(())
  }

  fn instantiate_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    // Minimal early error checks:
    // - Duplicate lexical declarations (let/const) in the same statement list.
    // - Lexical declarations may not collide with var-scoped names (var + function declarations).
    let mut var_names = HashSet::<String>::new();
    for stmt in stmts {
      self.collect_var_names(&stmt.stx, &mut var_names)?;
    }

    if self.strict {
      // Strict mode: only top-level function declarations are var-scoped; block function
      // declarations are instantiated at block entry.
      for stmt in stmts {
        let Stmt::FunctionDecl(decl) = &*stmt.stx else {
          continue;
        };
        let Some(name) = &decl.stx.name else {
          return Err(VmError::Unimplemented("anonymous function declaration"));
        };
        var_names.insert(name.stx.name.clone());
      }
    } else {
      // Non-strict: top-level hoistable decls (all flavors) are var-scoped; nested ordinary
      // FunctionDeclarations may also be (Annex B.3.2). Generators / async forms nested in
      // blocks/switch must *not* receive a var binding — only their CaseBlock/block lexical slot.
      for stmt in stmts {
        match &*stmt.stx {
          Stmt::FunctionDecl(decl) => {
            let Some(name) = &decl.stx.name else {
              return Err(VmError::Unimplemented("anonymous function declaration"));
            };
            var_names.insert(name.stx.name.clone());
          }
          other => self.collect_annex_b_function_decl_names(other, &mut var_names)?,
        }
      }
    }

    let mut lexical_seen = HashSet::<String>::new();
    let mut lexical_bindings: Vec<(String, parse_js::loc::Loc)> = Vec::new();
    for stmt in stmts {
      match &*stmt.stx {
        Stmt::VarDecl(var)
          if var.stx.mode == VarDeclMode::Let || var.stx.mode == VarDeclMode::Const =>
        {
          for declarator in &var.stx.declarators {
            self.collect_lexical_decl_names_from_pat(
              &declarator.pattern.stx.pat.stx,
              stmt.loc,
              &mut lexical_seen,
              &mut lexical_bindings,
            )?;
          }
        }
        Stmt::ClassDecl(decl) => {
          let Some(name) = &decl.stx.name else {
            return Err(VmError::Unimplemented("anonymous class declaration"));
          };
          if !lexical_seen.insert(name.stx.name.clone()) {
            return Err(syntax_error(
              stmt.loc,
              format!("Identifier '{}' has already been declared", name.stx.name),
            ));
          }
          lexical_bindings.push((name.stx.name.clone(), stmt.loc));
        }
        _ => {}
      }
    }

    for (name, loc) in &lexical_bindings {
      if var_names.contains(name) {
        return Err(syntax_error(
          *loc,
          format!("Identifier '{name}' has already been declared"),
        ));
      }
    }

    self.instantiate_var_decls(scope, stmts)?;
    let lex = self.env.lexical_env;
    self.instantiate_lexical_decls_in_stmt_list(scope, lex, stmts)?;
    self.instantiate_var_scoped_function_decls_in_stmt_list(scope, stmts)?;
    Ok(())
  }

  fn instantiate_var_decls(
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

  fn instantiate_var_scoped_function_decls_in_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    if self.strict {
      for stmt in stmts {
        let Stmt::FunctionDecl(decl) = &*stmt.stx else {
          continue;
        };
        self.instantiate_function_decl(scope, decl)?;
      }
      return Ok(());
    }

    // Non-strict: instantiate every top-level hoistable (incl. generator/async), then walk
    // nested statements for Annex B.3.2 ordinary FunctionDeclarations only.
    for stmt in stmts {
      match &*stmt.stx {
        Stmt::FunctionDecl(decl) => self.instantiate_function_decl(scope, decl)?,
        other => self.instantiate_annex_b_nested_function_decls_in_stmt(scope, other)?,
      }
    }
    Ok(())
  }

  /// Annex B.3.2: only *ordinary* nested `function` declarations get an additional var binding.
  /// Generator / async / async-generator declarations stay CaseBlock/block-lexically scoped.
  fn instantiate_annex_b_nested_function_decls_in_stmt(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &Stmt,
  ) -> Result<(), VmError> {
    match stmt {
      Stmt::FunctionDecl(decl) if is_ordinary_function_decl(&decl.stx) => {
        self.instantiate_function_decl(scope, decl)
      }
      Stmt::FunctionDecl(_) => Ok(()),
      Stmt::Block(block) => {
        for s in &block.stx.body {
          self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
        }
        Ok(())
      }
      Stmt::If(stmt) => {
        self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &stmt.stx.consequent.stx)?;
        if let Some(alt) = &stmt.stx.alternate {
          self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &alt.stx)?;
        }
        Ok(())
      }
      Stmt::Try(stmt) => {
        for s in &stmt.stx.wrapped.stx.body {
          self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
        }
        if let Some(catch) = &stmt.stx.catch {
          for s in &catch.stx.body {
            self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
          }
        }
        if let Some(finally) = &stmt.stx.finally {
          for s in &finally.stx.body {
            self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
          }
        }
        Ok(())
      }
      Stmt::While(stmt) => {
        self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &stmt.stx.body.stx)
      }
      Stmt::DoWhile(stmt) => {
        self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &stmt.stx.body.stx)
      }
      Stmt::ForTriple(stmt) => {
        for s in &stmt.stx.body.stx.body {
          self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
        }
        Ok(())
      }
      Stmt::ForIn(stmt) => {
        for s in &stmt.stx.body.stx.body {
          self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
        }
        Ok(())
      }
      Stmt::ForOf(stmt) => {
        for s in &stmt.stx.body.stx.body {
          self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
        }
        Ok(())
      }
      Stmt::Label(stmt) => {
        self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &stmt.stx.statement.stx)
      }
      Stmt::With(stmt) => {
        self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &stmt.stx.body.stx)
      }
      Stmt::Switch(stmt) => {
        for branch in &stmt.stx.branches {
          for s in &branch.stx.body {
            self.instantiate_annex_b_nested_function_decls_in_stmt(scope, &s.stx)?;
          }
        }
        Ok(())
      }
      _ => Ok(()),
    }
  }

  fn collect_annex_b_function_decl_names(
    &self,
    stmt: &Stmt,
    out: &mut HashSet<String>,
  ) -> Result<(), VmError> {
    match stmt {
      Stmt::FunctionDecl(decl) if is_ordinary_function_decl(&decl.stx) => {
        let Some(name) = &decl.stx.name else {
          return Err(VmError::Unimplemented("anonymous function declaration"));
        };
        out.insert(name.stx.name.clone());
        Ok(())
      }
      Stmt::FunctionDecl(_) => Ok(()),
      Stmt::Block(block) => {
        for stmt in &block.stx.body {
          self.collect_annex_b_function_decl_names(&stmt.stx, out)?;
        }
        Ok(())
      }
      Stmt::If(stmt) => {
        self.collect_annex_b_function_decl_names(&stmt.stx.consequent.stx, out)?;
        if let Some(alt) = &stmt.stx.alternate {
          self.collect_annex_b_function_decl_names(&alt.stx, out)?;
        }
        Ok(())
      }
      Stmt::Try(stmt) => {
        for s in &stmt.stx.wrapped.stx.body {
          self.collect_annex_b_function_decl_names(&s.stx, out)?;
        }
        if let Some(catch) = &stmt.stx.catch {
          for s in &catch.stx.body {
            self.collect_annex_b_function_decl_names(&s.stx, out)?;
          }
        }
        if let Some(finally) = &stmt.stx.finally {
          for s in &finally.stx.body {
            self.collect_annex_b_function_decl_names(&s.stx, out)?;
          }
        }
        Ok(())
      }
      Stmt::While(stmt) => self.collect_annex_b_function_decl_names(&stmt.stx.body.stx, out),
      Stmt::DoWhile(stmt) => self.collect_annex_b_function_decl_names(&stmt.stx.body.stx, out),
      Stmt::ForTriple(stmt) => {
        for s in &stmt.stx.body.stx.body {
          self.collect_annex_b_function_decl_names(&s.stx, out)?;
        }
        Ok(())
      }
      Stmt::ForIn(stmt) => {
        for s in &stmt.stx.body.stx.body {
          self.collect_annex_b_function_decl_names(&s.stx, out)?;
        }
        Ok(())
      }
      Stmt::ForOf(stmt) => {
        for s in &stmt.stx.body.stx.body {
          self.collect_annex_b_function_decl_names(&s.stx, out)?;
        }
        Ok(())
      }
      Stmt::Label(stmt) => self.collect_annex_b_function_decl_names(&stmt.stx.statement.stx, out),
      Stmt::With(stmt) => self.collect_annex_b_function_decl_names(&stmt.stx.body.stx, out),
      Stmt::Switch(stmt) => {
        for branch in &stmt.stx.branches {
          for s in &branch.stx.body {
            self.collect_annex_b_function_decl_names(&s.stx, out)?;
          }
        }
        Ok(())
      }
      _ => Ok(()),
    }
  }

  fn collect_lexical_decl_names_from_pat(
    &self,
    pat: &Pat,
    loc: parse_js::loc::Loc,
    seen: &mut HashSet<String>,
    out: &mut Vec<(String, parse_js::loc::Loc)>,
  ) -> Result<(), VmError> {
    match pat {
      Pat::Id(id) => {
        if !seen.insert(id.stx.name.clone()) {
          return Err(syntax_error(
            loc,
            format!("Identifier '{}' has already been declared", id.stx.name),
          ));
        }
        out.push((id.stx.name.clone(), loc));
        Ok(())
      }
      Pat::Obj(obj) => {
        for prop in &obj.stx.properties {
          self.collect_lexical_decl_names_from_pat(&prop.stx.target.stx, loc, seen, out)?;
        }
        if let Some(rest) = &obj.stx.rest {
          self.collect_lexical_decl_names_from_pat(&rest.stx, loc, seen, out)?;
        }
        Ok(())
      }
      Pat::Arr(arr) => {
        for elem in &arr.stx.elements {
          if let Some(elem) = elem {
            self.collect_lexical_decl_names_from_pat(&elem.target.stx, loc, seen, out)?;
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.collect_lexical_decl_names_from_pat(&rest.stx, loc, seen, out)?;
        }
        Ok(())
      }
      Pat::AssignTarget(_) => Err(VmError::Unimplemented(
        "lexical declaration assignment targets",
      )),
    }
  }

  fn instantiate_function_decl(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &Node<FuncDecl>,
  ) -> Result<(), VmError> {
    let Some(name) = &decl.stx.name else {
      return Err(VmError::Unimplemented("anonymous function declaration"));
    };

    let func_obj = self.create_function_object_for_decl(scope, decl, &name.stx.name)?;

    let mut assign_scope = scope.reborrow();
    assign_scope.push_root(Value::Object(func_obj))?;
    self.env.set_var(
      self.vm,
      &mut assign_scope,
      &name.stx.name,
      Value::Object(func_obj),
      self.strict,
    )?;
    Ok(())
  }

  fn create_function_object_for_decl(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &Node<FuncDecl>,
    name: &str,
  ) -> Result<GcObject, VmError> {
    use crate::function::ThisMode;
    use crate::vm::EcmaFunctionKind;

    let func = &decl.stx.function.stx;
    let flavor = FunctionFlavor::of(func)?;
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

    let name_s = scope.alloc_string(name)?;
    let length = function_length(func);

    let rel_start = decl.loc.start_u32().saturating_sub(self.env.prefix_len());
    let rel_end = decl.loc.end_u32().saturating_sub(self.env.prefix_len());
    let span_start = self.env.base_offset().saturating_add(rel_start);
    let span_end = self.env.base_offset().saturating_add(rel_end);

    let code_id = self.vm.register_ecma_function(
      self.env.source(),
      span_start,
      span_end,
      EcmaFunctionKind::Decl,
      &decl.stx.function,
    )?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    let func_obj = scope.alloc_ecma_function(
      code_id,
      true,
      name_s,
      length,
      this_mode,
      is_strict,
      Some(self.env.lexical_env),
      Some(intr.object_prototype()),
    )?;
    scope
      .heap_mut()
      .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
    scope
      .heap_mut()
      .set_function_realm(func_obj, self.env.global_object())?;
    if let Some(realm) = self.vm.current_realm() {
      scope.heap_mut().set_function_job_realm(func_obj, realm)?;
    }
    self.apply_function_flavor(scope, func_obj, flavor)?;
    Ok(func_obj)
  }

  fn instantiate_block_decls_in_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    // Duplicate block-scoped declarations are early errors.
    //
    // Note: switch/catch share this helper even though their scope isn't a syntactic `{}` block.
    let mut seen = HashSet::<String>::new();
    for stmt in stmts {
      match &*stmt.stx {
        Stmt::VarDecl(var)
          if var.stx.mode == VarDeclMode::Let || var.stx.mode == VarDeclMode::Const =>
        {
          for declarator in &var.stx.declarators {
            // Reuse lexical declaration collection logic to detect duplicates across complex patterns.
            let mut tmp = Vec::new();
            self.collect_lexical_decl_names_from_pat(
              &declarator.pattern.stx.pat.stx,
              stmt.loc,
              &mut seen,
              &mut tmp,
            )?;
          }
        }
        Stmt::ClassDecl(decl) => {
          let Some(name) = &decl.stx.name else {
            return Err(VmError::Unimplemented("anonymous class declaration"));
          };
          if !seen.insert(name.stx.name.clone()) {
            return Err(syntax_error(
              stmt.loc,
              format!("Identifier '{}' has already been declared", name.stx.name),
            ));
          }
        }
        Stmt::FunctionDecl(decl) if self.strict || !is_ordinary_function_decl(&decl.stx) => {
          // Lexically scoped hoistable decls cannot redeclare in the same block.
          // Non-strict ordinary FunctionDeclarations allow Annex B redeclaration.
          let Some(name) = &decl.stx.name else {
            return Err(VmError::Unimplemented("anonymous function declaration"));
          };
          if !seen.insert(name.stx.name.clone()) {
            return Err(syntax_error(
              stmt.loc,
              format!("Identifier '{}' has already been declared", name.stx.name),
            ));
          }
        }
        _ => {}
      }
    }

    self.instantiate_lexical_decls_in_stmt_list(scope, env, stmts)?;
    // BlockDeclarationInstantiation (§14.2.3): FunctionDeclaration, GeneratorDeclaration,
    // AsyncFunctionDeclaration, and AsyncGeneratorDeclaration are all lexically scoped to the
    // block / CaseBlock. (Annex B.3.2 may *also* create a var binding for ordinary functions in
    // non-strict code; that is handled separately at script/function instantiation.)
    self.instantiate_block_scoped_function_decls_in_stmt_list(scope, env, stmts)?;
    Ok(())
  }

  fn instantiate_block_scoped_function_decls_in_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    for stmt in stmts {
      let Stmt::FunctionDecl(decl) = &*stmt.stx else {
        continue;
      };
      self.instantiate_block_scoped_function_decl(scope, env, decl)?;
    }
    Ok(())
  }

  fn instantiate_block_scoped_function_decl(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    decl: &Node<FuncDecl>,
  ) -> Result<(), VmError> {
    let Some(name) = &decl.stx.name else {
      return Err(VmError::Unimplemented("anonymous function declaration"));
    };

    // Block-scoped functions are lexically scoped in strict mode.
    if scope.heap().env_has_binding(env, &name.stx.name)? {
      return Err(syntax_error(
        decl.loc,
        format!("Identifier '{}' has already been declared", name.stx.name),
      ));
    }

    scope.env_create_mutable_binding(env, &name.stx.name)?;

    let func_obj = self.create_function_object_for_decl(scope, decl, &name.stx.name)?;

    let mut init_scope = scope.reborrow();
    init_scope.push_root(Value::Object(func_obj))?;
    init_scope
      .heap_mut()
      .env_initialize_binding(env, &name.stx.name, Value::Object(func_obj))?;
    Ok(())
  }

  fn instantiate_lexical_decls_in_stmt_list(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    stmts: &[Node<Stmt>],
  ) -> Result<(), VmError> {
    for stmt in stmts {
      match &*stmt.stx {
        Stmt::VarDecl(var) => match var.stx.mode {
          VarDeclMode::Let => {
            for declarator in &var.stx.declarators {
              self.instantiate_lexical_names_from_pat(
                scope,
                env,
                &declarator.pattern.stx.pat.stx,
                stmt.loc,
                true,
              )?;
            }
          }
          VarDeclMode::Const => {
            for declarator in &var.stx.declarators {
              self.instantiate_lexical_names_from_pat(
                scope,
                env,
                &declarator.pattern.stx.pat.stx,
                stmt.loc,
                false,
              )?;
            }
          }
          _ => {}
        },
        // ClassDeclaration is like `const`: immutable binding, TDZ until evaluation.
        Stmt::ClassDecl(decl) => {
          let Some(name) = &decl.stx.name else {
            return Err(VmError::Unimplemented("anonymous class declaration"));
          };
          if scope.heap().env_has_binding(env, &name.stx.name)? {
            return Err(syntax_error(
              stmt.loc,
              format!("Identifier '{}' has already been declared", name.stx.name),
            ));
          }
          scope.env_create_immutable_binding(env, &name.stx.name, true)?;
        }
        _ => {}
      }
    }
    Ok(())
  }

  fn instantiate_lexical_names_from_pat(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcEnv,
    pat: &Pat,
    loc: parse_js::loc::Loc,
    mutable: bool,
  ) -> Result<(), VmError> {
    match pat {
      Pat::Id(id) => {
        if scope.heap().env_has_binding(env, &id.stx.name)? {
          return Err(syntax_error(
            loc,
            format!("Identifier '{}' has already been declared", id.stx.name),
          ));
        }
        if mutable {
          scope.env_create_mutable_binding(env, &id.stx.name)?;
        } else {
          scope.env_create_immutable_binding(env, &id.stx.name, true)?;
        }
        Ok(())
      }
      Pat::Obj(obj) => {
        for prop in &obj.stx.properties {
          self.instantiate_lexical_names_from_pat(
            scope,
            env,
            &prop.stx.target.stx,
            loc,
            mutable,
          )?;
        }
        if let Some(rest) = &obj.stx.rest {
          self.instantiate_lexical_names_from_pat(scope, env, &rest.stx, loc, mutable)?;
        }
        Ok(())
      }
      Pat::Arr(arr) => {
        for elem in &arr.stx.elements {
          if let Some(elem) = elem {
            self.instantiate_lexical_names_from_pat(scope, env, &elem.target.stx, loc, mutable)?;
          }
        }
        if let Some(rest) = &arr.stx.rest {
          self.instantiate_lexical_names_from_pat(scope, env, &rest.stx, loc, mutable)?;
        }
        Ok(())
      }
      Pat::AssignTarget(_) => Err(VmError::Unimplemented(
        "lexical declaration assignment targets",
      )),
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
      Stmt::ForIn(stmt) => {
        if let ForInOfLhs::Decl((mode, pat_decl)) = &stmt.stx.lhs {
          if *mode == VarDeclMode::Var {
            self.collect_var_names_from_pat_decl(&pat_decl.stx, out)?;
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
      Stmt::With(stmt) => {
        self.collect_var_names(&stmt.stx.body.stx, out)?;
      }
      Stmt::Switch(stmt) => {
        for branch in &stmt.stx.branches {
          for s in &branch.stx.body {
            self.collect_var_names(&s.stx, out)?;
          }
        }
      }
      // Function declarations are *not* VarDeclaredNames of nested statements. Top-level
      // HoistableDeclarations and Annex B nested ordinary functions are collected separately
      // by `collect_var_scoped_names` so generators/async in `switch`/blocks do not leak a
      // var binding (ECMA-262 §14.12 CaseBlock + Annex B.3.2).
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
    self.collect_var_names_from_pat(&pat_decl.pat.stx, out)
  }

  fn collect_var_names_from_pat(
    &self,
    pat: &Pat,
    out: &mut HashSet<String>,
  ) -> Result<(), VmError> {
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
      .instantiate_block_decls_in_stmt_list(scope, block_env, &block.body)
      .and_then(|_| self.eval_stmt_list(scope, &block.body));

    self.env.set_lexical_env(scope.heap_mut(), outer);
    result
  }

  /// `with` statement (ECMA-262 §14.11). Strict-mode `with` is a parse/early error; this path is
  /// only reached for sloppy scripts.
  fn eval_with(&mut self, scope: &mut Scope<'_>, stmt: &WithStmt) -> Result<Completion, VmError> {
    let obj_val = self.eval_expr(scope, &stmt.object)?;
    let binding_object = self.to_object(scope, obj_val)?;
    let outer = self.env.lexical_env;
    let mut with_scope = scope.reborrow();
    with_scope.push_root(Value::Object(binding_object))?;
    with_scope.push_env_root(outer)?;
    let with_env = with_scope.alloc_object_env_record(binding_object, Some(outer), true)?;
    self.env.set_lexical_env(with_scope.heap_mut(), with_env);
    let result = self.eval_stmt(&mut with_scope, &stmt.body);
    self.env.set_lexical_env(with_scope.heap_mut(), outer);
    result
  }

  /// ECMA-262 §7.1.18 `ToObject`.
  fn to_object(&mut self, scope: &mut Scope<'_>, value: Value) -> Result<GcObject, VmError> {
    match value {
      Value::Object(obj) => Ok(obj),
      Value::Null | Value::Undefined => Err(throw_type_error(
        self.vm,
        scope,
        "Cannot convert undefined or null to object",
      )?),
      other => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let object_ctor = Value::Object(intr.object_constructor());
        let mut to_obj_scope = scope.reborrow();
        to_obj_scope.push_root(other)?;
        to_obj_scope.push_root(object_ctor)?;
        let boxed = self.call(&mut to_obj_scope, object_ctor, Value::Undefined, &[other])?;
        match boxed {
          Value::Object(obj) => Ok(obj),
          _ => Err(VmError::InvariantViolation(
            "Object(..) conversion returned non-object",
          )),
        }
      }
    }
  }

  fn eval_stmt(&mut self, scope: &mut Scope<'_>, stmt: &Node<Stmt>) -> Result<Completion, VmError> {
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
      Stmt::Throw(stmt) => self.eval_throw(scope, stmt),
      Stmt::Try(stmt) => self.eval_try(scope, &stmt.stx),
      Stmt::Return(stmt) => self.eval_return(scope, &stmt.stx),
      Stmt::While(stmt) => self.eval_while(scope, &stmt.stx, label_set),
      Stmt::DoWhile(stmt) => self.eval_do_while(scope, &stmt.stx, label_set),
      Stmt::ForTriple(stmt) => self.eval_for_triple(scope, &stmt.stx, label_set),
      Stmt::ForIn(stmt) => self.eval_for_in(scope, &stmt.stx, label_set),
      Stmt::ForOf(stmt) => self.eval_for_of(scope, &stmt.stx, label_set),
      Stmt::Switch(stmt) => {
        let result = self.eval_switch(scope, &stmt.stx)?;
        Ok(Self::normalise_iteration_break(result))
      }
      Stmt::Label(stmt) => self.eval_label(scope, &stmt.stx, label_set),
      // Function declarations are instantiated during hoisting.
      Stmt::FunctionDecl(_) => Ok(Completion::empty()),
      Stmt::ClassDecl(decl) => self.eval_class_decl(scope, &decl.stx),
      Stmt::Break(stmt) => Ok(Completion::Break(stmt.stx.label.clone(), None)),
      Stmt::Continue(stmt) => Ok(Completion::Continue(stmt.stx.label.clone(), None)),
      Stmt::With(stmt) => self.eval_with(scope, &stmt.stx),

      _ => Err(VmError::Unimplemented("statement type")),
    };

    // Treat internal `VmError::Throw*` as a JS throw completion so it is catchable by `try/catch`.
    //
    // This is also the central stack capture point for implicit throws (TDZ errors, TypeErrors,
    // etc) that are surfaced as `Err(VmError::Throw(..))` from lower-level helpers.
    let thrown_at_stmt = |value: Value| {
      let source = self.env.source();
      let rel_start = stmt.loc.start_u32().saturating_sub(self.env.prefix_len());
      let abs_offset = self.env.base_offset().saturating_add(rel_start);
      let (line, col) = source.line_col(abs_offset);

      let mut stack = self.vm.capture_stack();
      if let Some(top) = stack.first_mut() {
        top.source = source.name.clone();
        top.line = line;
        top.col = col;
      } else {
        stack.push(StackFrame {
          function: None,
          source: source.name.clone(),
          line,
          col,
        });
      }

      Thrown { value, stack }
    };

    match res {
      Err(VmError::Throw(value)) => Ok(Completion::Throw(thrown_at_stmt(value))),
      Err(VmError::ThrowWithStack { value, stack }) => {
        Ok(Completion::Throw(Thrown { value, stack }))
      }
      Err(VmError::TypeError(message)) => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = new_error(scope, intr.type_error_prototype(), "TypeError", message)?;
        Ok(Completion::Throw(thrown_at_stmt(err)))
      }
      Err(VmError::PrototypeCycle) => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = new_error(
          scope,
          intr.type_error_prototype(),
          "TypeError",
          "prototype cycle",
        )?;
        Ok(Completion::Throw(thrown_at_stmt(err)))
      }
      Err(VmError::PrototypeChainTooDeep) => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = new_error(
          scope,
          intr.type_error_prototype(),
          "TypeError",
          "prototype chain too deep",
        )?;
        Ok(Completion::Throw(thrown_at_stmt(err)))
      }
      Err(VmError::InvalidPropertyDescriptorPatch) => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = new_error(
          scope,
          intr.type_error_prototype(),
          "TypeError",
          "invalid property descriptor patch: cannot mix data and accessor fields",
        )?;
        Ok(Completion::Throw(thrown_at_stmt(err)))
      }
      Err(VmError::NotCallable) => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = new_error(
          scope,
          intr.type_error_prototype(),
          "TypeError",
          "value is not callable",
        )?;
        Ok(Completion::Throw(thrown_at_stmt(err)))
      }
      Err(VmError::NotConstructable) => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let err = new_error(
          scope,
          intr.type_error_prototype(),
          "TypeError",
          "value is not a constructor",
        )?;
        Ok(Completion::Throw(thrown_at_stmt(err)))
      }
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

  /// Evaluate an initializer with NamedEvaluation when `binding_name` is given and the
  /// initializer is an anonymous function/class definition.
  fn eval_named_initializer(
    &mut self,
    scope: &mut Scope<'_>,
    init: &Node<Expr>,
    binding_name: Option<&str>,
  ) -> Result<Value, VmError> {
    let Some(name) = binding_name.filter(|_| is_anonymous_function_definition_node(init)) else {
      return self.eval_expr(scope, init);
    };
    let v = if let Expr::Class(class) = &*init.stx {
      self.eval_class_expr(scope, class, Some(name))?
    } else {
      self.eval_expr(scope, init)?
    };
    let mut s = scope.reborrow();
    s.push_root(v)?;
    if let Value::Object(func) = v {
      if s.heap().is_callable(v)? {
        // SetFunctionName's contract: the function must not already carry a
        // real name. Class evaluation installs `static name()` methods *after*
        // its own SetFunctionName (so they win, per spec) — re-applying the
        // inferred name here would clobber them. Anonymous defaults (`""`)
        // still take the inferred name (`var f = function() {}`).
        let name_s = s.alloc_string(name)?;
        let name_key = s.alloc_string("name")?;
        let current = s
          .heap()
          .object_get_own_property(func, &PropertyKey::String(name_key))?;
        let has_real_name = match current.map(|d| d.kind) {
          Some(PropertyKind::Data {
            value: Value::String(str_id),
            ..
          }) => !s.heap().get_string(str_id)?.is_empty(),
          Some(_) => true,
          None => false,
        };
        if !has_real_name {
          crate::function_properties::set_function_name(
            &mut s,
            func,
            PropertyKey::from_string(name_s),
            None,
          )?;
        }
      }
    }
    Ok(v)
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
              return Err(VmError::Unimplemented(
                "destructuring var without initializer",
              ));
            }
            continue;
          };
          let binding_name = match &*declarator.pattern.stx.pat.stx {
            Pat::Id(id) => Some(id.stx.name.as_str()),
            _ => None,
          };
          let value = self.eval_named_initializer(scope, init, binding_name)?;
          bind_pattern(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
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
              return Err(VmError::Unimplemented(
                "destructuring let without initializer",
              ));
            };
            let value = self.eval_expr(scope, init)?;
            bind_pattern(
              self.vm,
              &mut *self.host,
              &mut *self.hooks,
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
            Some(init) => self.eval_named_initializer(scope, init, Some(name))?,
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

          if !matches!(&*declarator.pattern.stx.pat.stx, Pat::Id(_)) {
            let value = self.eval_expr(scope, init)?;
            bind_pattern(
              self.vm,
              &mut *self.host,
              &mut *self.hooks,
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
          let value = self.eval_named_initializer(scope, init, Some(name))?;

          if !scope.heap().env_has_binding(self.env.lexical_env, name)? {
            scope.env_create_immutable_binding(self.env.lexical_env, name, true)?;
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
    // ECMA-262 IfStatement evaluation ends with `Return ? UpdateEmpty(stmtCompletion, undefined)`
    // so an empty body yields `undefined` (not empty) — required for `eval('1; if (true) {}')`
    // and so `break` inside `if` does not inherit a prior loop `V` via UpdateEmpty.
    let test = self.eval_expr(scope, &stmt.test)?;
    let stmt_completion = if to_boolean(scope.heap(), test)? {
      self.eval_stmt(scope, &stmt.consequent)?
    } else if let Some(alt) = &stmt.alternate {
      self.eval_stmt(scope, alt)?
    } else {
      Completion::empty()
    };
    Ok(stmt_completion.update_empty(Some(Value::Undefined)))
  }

  fn eval_throw(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &Node<ThrowStmt>,
  ) -> Result<Completion, VmError> {
    let value = self.eval_expr(scope, &stmt.stx.value)?;

    // Capture a stack trace at the throw site.
    //
    // We capture the VM's current call stack and then update the top frame's `source/line/col` to
    // point at the throw statement (rather than the function entry). This aligns better with
    // browser stack traces where the top frame refers to the actual throw location.
    let source = self.env.source();
    let rel_start = stmt.loc.start_u32().saturating_sub(self.env.prefix_len());
    let abs_offset = self.env.base_offset().saturating_add(rel_start);
    let (line, col) = source.line_col(abs_offset);

    let mut stack = self.vm.capture_stack();
    if let Some(top) = stack.first_mut() {
      top.source = source.name.clone();
      top.line = line;
      top.col = col;
    } else {
      stack.push(StackFrame {
        function: None,
        source: source.name.clone(),
        line,
        col,
      });
    }

    Ok(Completion::Throw(Thrown { value, stack }))
  }

  fn eval_try(&mut self, scope: &mut Scope<'_>, stmt: &TryStmt) -> Result<Completion, VmError> {
    let mut result = self.eval_block_stmt(scope, &stmt.wrapped.stx)?;

    if matches!(result, Completion::Throw(_)) {
      if let Some(catch) = &stmt.catch {
        let thrown = match result {
          Completion::Throw(thrown) => thrown.value,
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
        result = finally_result;
      }
    }

    Ok(result.update_empty(Some(Value::Undefined)))
  }

  fn eval_catch(
    &mut self,
    scope: &mut Scope<'_>,
    catch: &CatchBlock,
    thrown: Value,
  ) -> Result<Completion, VmError> {
    // Root the thrown value *before* `env_create`: creating the catch environment may allocate
    // and trigger GC. `Thrown` only carries a bare `Value` (plus stack frames), so without a
    // root here the exception object can be swept during unwind — `InvalidHandle` / debug
    // assert on the subsequent push_root / catch binding.
    scope.push_root(thrown)?;

    let outer = self.env.lexical_env;
    let catch_env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), catch_env);

    let result = {
      let mut catch_scope = scope.reborrow();
      self
        .instantiate_block_decls_in_stmt_list(&mut catch_scope, catch_env, &catch.body)
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
      &mut *self.host,
      &mut *self.hooks,
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

  /// Converts an unlabelled `break` completion from a breakable statement into a normal
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
    let result = self.for_triple_loop_evaluation(scope, stmt, label_set)?;
    Ok(Self::normalise_iteration_break(result))
  }

  /// ECMA-262 `CreatePerIterationEnvironment` (§13.7.4.9).
  ///
  /// Copies `per_iteration_names` from the current lexical environment into a fresh
  /// declarative environment whose `[[OuterEnv]]` is the same as the previous iteration
  /// env's outer (i.e. the environment enclosing the `for` statement).
  fn create_per_iteration_environment(
    &mut self,
    scope: &mut Scope<'_>,
    per_iteration_names: &[String],
  ) -> Result<(), VmError> {
    if per_iteration_names.is_empty() {
      return Ok(());
    }
    let last = self.env.lexical_env;
    let outer = scope
      .heap()
      .env_outer(last)?
      .ok_or(VmError::InvariantViolation(
        "CreatePerIterationEnvironment: last iteration env has null outer",
      ))?;
    let this_iter = scope.env_create(Some(outer))?;
    for name in per_iteration_names {
      let value = scope.heap().env_get_binding_value(last, name, true)?;
      scope.env_create_mutable_binding(this_iter, name)?;
      scope
        .heap_mut()
        .env_initialize_binding(this_iter, name, value)?;
    }
    self.env.set_lexical_env(scope.heap_mut(), this_iter);
    Ok(())
  }

  fn collect_for_triple_per_iteration_names(decl: &VarDecl) -> Vec<String> {
    let mut names = Vec::new();
    for declarator in &decl.declarators {
      Self::collect_pat_binding_names(&declarator.pattern.stx.pat.stx, &mut names);
    }
    names
  }

  fn collect_pat_binding_names(pat: &Pat, out: &mut Vec<String>) {
    match pat {
      Pat::Id(id) => out.push(id.stx.name.clone()),
      Pat::Obj(obj) => {
        for prop in &obj.stx.properties {
          Self::collect_pat_binding_names(&prop.stx.target.stx, out);
        }
        if let Some(rest) = &obj.stx.rest {
          Self::collect_pat_binding_names(&rest.stx, out);
        }
      }
      Pat::Arr(arr) => {
        for elem in &arr.stx.elements {
          if let Some(elem) = elem {
            Self::collect_pat_binding_names(&elem.target.stx, out);
          }
        }
        if let Some(rest) = &arr.stx.rest {
          Self::collect_pat_binding_names(&rest.stx, out);
        }
      }
      Pat::AssignTarget(_) => {}
    }
  }

  /// ECMA-262 `ForLoopEvaluation` / `ForBodyEvaluation` for `for (init; cond; post) { ... }`.
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

    // `for (let/const …; …; …)`:
    // 1. Evaluate the initializer in a fresh `loopEnv` (visible to closures created in init).
    // 2. `CreatePerIterationEnvironment` before the first test and again after each body
    //    (before the increment) so body/test/incr closures capture distinct bindings.
    let (restore_lex, per_iteration_names) = match &stmt.init {
      parse_js::ast::stmt::ForTripleStmtInit::Decl(decl)
        if matches!(decl.stx.mode, VarDeclMode::Let | VarDeclMode::Const) =>
      {
        let outer = self.env.lexical_env;
        let loop_env = scope.env_create(Some(outer))?;
        self.env.set_lexical_env(scope.heap_mut(), loop_env);
        (
          Some(outer),
          Self::collect_for_triple_per_iteration_names(&decl.stx),
        )
      }
      _ => (None, Vec::new()),
    };

    let result = (|| -> Result<Completion, VmError> {
      match &stmt.init {
        parse_js::ast::stmt::ForTripleStmtInit::None => {}
        parse_js::ast::stmt::ForTripleStmtInit::Expr(expr) => {
          let _ = self.eval_expr(&mut scope, expr)?;
        }
        parse_js::ast::stmt::ForTripleStmtInit::Decl(decl) => {
          let _ = self.eval_var_decl(&mut scope, &decl.stx)?;
        }
      }

      // ForBodyEvaluation step 2.
      self.create_per_iteration_environment(&mut scope, &per_iteration_names)?;

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

        // ForBodyEvaluation step 3.e — before the increment.
        self.create_per_iteration_environment(&mut scope, &per_iteration_names)?;

        if let Some(post) = &stmt.post {
          let _ = self.eval_expr(&mut scope, post)?;
        }
      }
    })();

    if let Some(outer) = restore_lex {
      self.env.set_lexical_env(scope.heap_mut(), outer);
    }
    result
  }

  fn eval_for_in(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForInStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    let result = self.for_in_loop_evaluation(scope, stmt, label_set)?;
    Ok(Self::normalise_iteration_break(result))
  }

  fn for_in_loop_evaluation(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForInStmt,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    let rhs_value = self.eval_expr(scope, &stmt.rhs)?;
    if is_nullish(rhs_value) {
      // Minimal semantics: legacy-ish behaviour, treat `null`/`undefined` as an empty iteration.
      return Ok(Completion::normal(Value::Undefined));
    }

    // `for..in` uses `ToObject` on the RHS. Until we have full wrapper objects, treat the `Object`
    // constructor as a converter for primitives.
    let object = match rhs_value {
      Value::Object(obj) => obj,
      other => {
        let intr = self
          .vm
          .intrinsics()
          .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
        let object_ctor = Value::Object(intr.object_constructor());

        let mut to_obj_scope = scope.reborrow();
        to_obj_scope.push_root(other)?;
        to_obj_scope.push_root(object_ctor)?;
        let args = [other];
        let value = self.call(&mut to_obj_scope, object_ctor, Value::Undefined, &args)?;
        match value {
          Value::Object(obj) => obj,
          _ => {
            return Err(VmError::InvariantViolation(
              "Object(..) conversion returned non-object",
            ));
          }
        }
      }
    };

    // Root the base object across key collection + loop body evaluation, which may allocate and
    // trigger GC.
    let mut iter_scope = scope.reborrow();
    iter_scope.push_root(Value::Object(object))?;

    // Snapshot enumerable string keys across the prototype chain, skipping duplicates.
    //
    // Note: this is intentionally minimal and does not track mutations during iteration.
    let mut keys: Vec<GcString> = Vec::new();
    let mut visited: Vec<PropertyKey> = Vec::new();

    let mut current: Option<GcObject> = Some(object);
    while let Some(obj) = current {
      let own_keys = iter_scope.ordinary_own_property_keys(obj)?;
      for key in own_keys {
        let PropertyKey::String(s) = key else {
          continue;
        };

        let Some(desc) = iter_scope.ordinary_get_own_property(obj, key)? else {
          continue;
        };
        if !desc.enumerable {
          continue;
        }

        if visited
          .iter()
          .any(|seen| iter_scope.heap().property_key_eq(seen, &key))
        {
          continue;
        }

        visited.push(key);
        keys.push(s);
        // Root the key for the duration of the loop in case the property is deleted during
        // iteration.
        iter_scope.push_root(Value::String(s))?;
      }

      current = iter_scope.object_get_prototype(obj)?;
    }

    // Root `V` across the loop so the value can't be collected between iterations.
    let v_root_idx = iter_scope.heap().root_stack.len();
    iter_scope.push_root(Value::Undefined)?;
    let mut v = Value::Undefined;

    // If the loop uses a lexical declaration (`let`/`const`), we emulate per-iteration lexical
    // environments by creating a fresh env record per iteration.
    let outer_lex = self.env.lexical_env;

    for key_s in keys {
      // Tick once per iteration so `for (k in o) {}` is budgeted even when the body is empty.
      self.tick()?;

      let mut iter_env: Option<GcEnv> = None;
      if let ForInOfLhs::Decl((mode, _)) = &stmt.lhs {
        if *mode == VarDeclMode::Let || *mode == VarDeclMode::Const {
          let env = iter_scope.env_create(Some(outer_lex))?;
          self.env.set_lexical_env(iter_scope.heap_mut(), env);
          iter_env = Some(env);
        }
      }

      let value = Value::String(key_s);

      let bind_res: Result<(), VmError> = match &stmt.lhs {
        ForInOfLhs::Decl((mode, pat_decl)) => {
          let kind = match *mode {
            VarDeclMode::Var => BindingKind::Var,
            VarDeclMode::Let => BindingKind::Let,
            VarDeclMode::Const => BindingKind::Const,
            _ => {
              return Err(VmError::Unimplemented(
                "for-in loop variable declaration kind",
              ));
            }
          };
          bind_pattern(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
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
          &mut *self.host,
          &mut *self.hooks,
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
        if iter_env.is_some() {
          self.env.set_lexical_env(iter_scope.heap_mut(), outer_lex);
        }
        return Err(err);
      }

      let body_completion = match self.eval_for_body(&mut iter_scope, &stmt.body.stx) {
        Ok(c) => c,
        Err(err) => {
          if iter_env.is_some() {
            self.env.set_lexical_env(iter_scope.heap_mut(), outer_lex);
          }
          return Err(err);
        }
      };

      if iter_env.is_some() {
        self.env.set_lexical_env(iter_scope.heap_mut(), outer_lex);
      }

      if !Self::loop_continues(&body_completion, label_set) {
        return Ok(body_completion.update_empty(Some(v)));
      }

      if let Some(value) = body_completion.value() {
        v = value;
        iter_scope.heap_mut().root_stack[v_root_idx] = value;
      }
    }

    Ok(Completion::normal(v))
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

    let mut iterator_record = iterator::get_iterator(
      self.vm,
      &mut *self.host,
      &mut *self.hooks,
      &mut iter_scope,
      iterable,
    )?;
    iter_scope.push_roots(&[iterator_record.iterator, iterator_record.next_method])?;

    // Root `V` across the loop so the value can't be collected between iterations.
    let v_root_idx = iter_scope.heap().root_stack.len();
    iter_scope.push_root(Value::Undefined)?;
    let mut v = Value::Undefined;

    // Lexical `let`/`const` for-of bindings get a fresh environment per iteration
    // (same shape as for-in).
    let outer_lex = self.env.lexical_env;

    loop {
      // Tick once per iteration so `for (x of xs) {}` is budgeted even when the body is empty.
      self.tick()?;

      let next_value = match iterator::iterator_step_value(
        self.vm,
        &mut *self.host,
        &mut *self.hooks,
        &mut iter_scope,
        &mut iterator_record,
      ) {
        Ok(v) => v,
        Err(err) => {
          let _ = iterator::iterator_close(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
            &mut iter_scope,
            &iterator_record,
          );
          return Err(err);
        }
      };

      let Some(value) = next_value else {
        return Ok(Completion::normal(v));
      };

      let mut iter_env: Option<GcEnv> = None;
      if let ForInOfLhs::Decl((mode, _)) = &stmt.lhs {
        if *mode == VarDeclMode::Let || *mode == VarDeclMode::Const {
          let env = iter_scope.env_create(Some(outer_lex))?;
          self.env.set_lexical_env(iter_scope.heap_mut(), env);
          iter_env = Some(env);
        }
      }

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
            &mut *self.host,
            &mut *self.hooks,
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
          &mut *self.host,
          &mut *self.hooks,
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
        if iter_env.is_some() {
          self.env.set_lexical_env(iter_scope.heap_mut(), outer_lex);
        }
        let _ = iterator::iterator_close(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut iter_scope,
          &iterator_record,
        );
        return Err(err);
      }

      let body_completion = match self.eval_for_body(&mut iter_scope, &stmt.body.stx) {
        Ok(c) => c,
        Err(err) => {
          if iter_env.is_some() {
            self.env.set_lexical_env(iter_scope.heap_mut(), outer_lex);
          }
          let _ = iterator::iterator_close(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
            &mut iter_scope,
            &iterator_record,
          );
          return Err(err);
        }
      };

      if iter_env.is_some() {
        self.env.set_lexical_env(iter_scope.heap_mut(), outer_lex);
      }

      if !Self::loop_continues(&body_completion, label_set) {
        let _ = iterator::iterator_close(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut iter_scope,
          &iterator_record,
        );
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
        // ECMA-262 `LabelledEvaluation`: a labelled `break` is consumed by the matching label,
        // preserving the completion value (which may be ~empty~).
        Ok(Completion::Normal(value))
      }
      other => Ok(other),
    }
  }

  fn eval_switch(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &SwitchStmt,
  ) -> Result<Completion, VmError> {
    // 13.12.3 Runtime Semantics: Evaluation, SwitchStatement
    let discriminant = self.eval_expr(scope, &stmt.test)?;

    // Root the discriminant across selector evaluation and case-body execution, which may allocate
    // and trigger GC.
    let mut switch_scope = scope.reborrow();
    switch_scope.push_root(discriminant)?;

    // `switch` creates a new lexical environment for the entire case block.
    let outer = self.env.lexical_env;
    let switch_env = switch_scope.env_create(Some(outer))?;
    self
      .env
      .set_lexical_env(switch_scope.heap_mut(), switch_env);

    let result = (|| -> Result<Completion, VmError> {
      // `switch` shares one lexical scope across all case clauses.
      for branch in &stmt.branches {
        self.instantiate_block_decls_in_stmt_list(
          &mut switch_scope,
          switch_env,
          &branch.stx.body,
        )?;
      }

      // ECMA-262 `CaseBlockEvaluation`: `V` starts as `undefined` and is never ~empty~ for normal
      // completion.
      let v_root_idx = switch_scope.heap().root_stack.len();
      switch_scope.push_root(Value::Undefined)?;
      let mut v = Value::Undefined;

      let default_idx = stmt.branches.iter().position(|b| b.stx.case.is_none());

      match default_idx {
        None => {
          let mut found = false;
          for branch in &stmt.branches {
            let Some(case_expr) = &branch.stx.case else {
              continue;
            };

            if !found {
              let case_value = self.eval_expr(&mut switch_scope, case_expr)?;
              found = strict_equal(switch_scope.heap(), discriminant, case_value)?;
            }

            if found {
              let r = self.eval_stmt_list(&mut switch_scope, &branch.stx.body)?;
              if let Some(value) = r.value() {
                v = value;
                switch_scope.heap_mut().root_stack[v_root_idx] = value;
              }
              if r.is_abrupt() {
                return Ok(r.update_empty(Some(v)));
              }
            }
          }
          Ok(Completion::normal(v))
        }
        Some(default_idx) => {
          let (a, rest) = stmt.branches.split_at(default_idx);
          let default_branch = &rest[0];
          let b = &rest[1..];

          let mut found = false;
          for branch in a {
            let Some(case_expr) = &branch.stx.case else {
              continue;
            };

            if !found {
              let case_value = self.eval_expr(&mut switch_scope, case_expr)?;
              found = strict_equal(switch_scope.heap(), discriminant, case_value)?;
            }

            if found {
              let r = self.eval_stmt_list(&mut switch_scope, &branch.stx.body)?;
              if let Some(value) = r.value() {
                v = value;
                switch_scope.heap_mut().root_stack[v_root_idx] = value;
              }
              if r.is_abrupt() {
                return Ok(r.update_empty(Some(v)));
              }
            }
          }

          let mut found_in_b = false;
          if !found {
            for branch in b {
              let Some(case_expr) = &branch.stx.case else {
                continue;
              };

              if !found_in_b {
                let case_value = self.eval_expr(&mut switch_scope, case_expr)?;
                found_in_b = strict_equal(switch_scope.heap(), discriminant, case_value)?;
              }

              if found_in_b {
                let r = self.eval_stmt_list(&mut switch_scope, &branch.stx.body)?;
                if let Some(value) = r.value() {
                  v = value;
                  switch_scope.heap_mut().root_stack[v_root_idx] = value;
                }
                if r.is_abrupt() {
                  return Ok(r.update_empty(Some(v)));
                }
              }
            }
          }

          if found_in_b {
            return Ok(Completion::normal(v));
          }

          let default_r = self.eval_stmt_list(&mut switch_scope, &default_branch.stx.body)?;
          if let Some(value) = default_r.value() {
            v = value;
            switch_scope.heap_mut().root_stack[v_root_idx] = value;
          }
          if default_r.is_abrupt() {
            return Ok(default_r.update_empty(Some(v)));
          }

          // NOTE: The following is another complete iteration of the after-default clauses.
          for branch in b {
            let r = self.eval_stmt_list(&mut switch_scope, &branch.stx.body)?;
            if let Some(value) = r.value() {
              v = value;
              switch_scope.heap_mut().root_stack[v_root_idx] = value;
            }
            if r.is_abrupt() {
              return Ok(r.update_empty(Some(v)));
            }
          }

          Ok(Completion::normal(v))
        }
      }
    })();

    // Restore the outer lexical environment no matter how control leaves the switch.
    self.env.set_lexical_env(switch_scope.heap_mut(), outer);
    result
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
      Expr::LitRegex(node) => self.eval_lit_regex(scope, &node.stx),
      Expr::LitArr(node) => self.eval_lit_arr(scope, &node.stx),
      Expr::LitObj(node) => self.eval_lit_obj(scope, &node.stx),
      Expr::LitTemplate(node) => self.eval_lit_template(scope, &node.stx),
      Expr::TaggedTemplate(node) => self.eval_tagged_template(scope, &node.stx),
      Expr::This(_) => self.get_this_binding(scope),
      Expr::NewTarget(_) => Ok(self.new_target),
      Expr::Super(_) => Err(VmError::Unimplemented(
        "'super' keyword unexpected in this position",
      )),
      Expr::Id(node) => self.eval_id(scope, &node.stx),
      // Whole optional chains (§13.3.9) are evaluated as a unit so a `?.` short-circuit propagates
      // through the remaining non-optional links (e.g. `a?.b.c` yields `undefined`, not a throw).
      Expr::Call(_) | Expr::Member(_) | Expr::ComputedMember(_) if contains_optional_link(expr) => {
        self.eval_optional_chain(scope, expr)
      }
      Expr::Call(node) => self.eval_call(scope, &node.stx),
      Expr::Func(node) => self.eval_func_expr(scope, node),
      Expr::ArrowFunc(node) => self.eval_arrow_func_expr(scope, node),
      Expr::Class(node) => self.eval_class_expr(scope, node, None),
      Expr::Member(node) => self.eval_member(scope, &node.stx),
      Expr::ComputedMember(node) => self.eval_computed_member(scope, &node.stx),
      Expr::Unary(node) => self.eval_unary(scope, &node.stx),
      Expr::UnaryPostfix(node) => self.eval_unary_postfix(scope, &node.stx),
      Expr::Binary(node) => self.eval_binary(scope, &node.stx),
      Expr::Cond(node) => self.eval_cond(scope, &node.stx),

      // Patterns sometimes show up in expression position (e.g. assignment targets). We only
      // support simple identifier patterns for now.
      Expr::IdPat(node) => self.eval_id_pat(scope, &node.stx),

      _ => Err(VmError::Unimplemented("expression type")),
    }
  }

  fn eval_member(&mut self, scope: &mut Scope<'_>, expr: &MemberExpr) -> Result<Value, VmError> {
    if matches!(&*expr.left.stx, Expr::Super(_)) {
      let key_s = scope.alloc_string(&expr.right)?;
      let key = PropertyKey::from_string(key_s);
      let (value, _) = self.eval_super_property(scope, key)?;
      return Ok(value);
    }
    let base = self.eval_expr(scope, &expr.left)?;
    if expr.optional_chaining && is_nullish(base) {
      return Ok(Value::Undefined);
    }

    // Root `base` across property-key allocation in case it triggers GC. `base` may be a primitive:
    // `GetV` (§7.3.2 / §13.3.3) resolves the property against the matching wrapper prototype without
    // allocating a wrapper object.
    let mut key_scope = scope.reborrow();
    key_scope.push_root(base)?;
    let key_s = key_scope.alloc_string(&expr.right)?;
    let key = PropertyKey::from_string(key_s);
    self.get_v(&mut key_scope, base, key)
  }

  fn eval_computed_member(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &ComputedMemberExpr,
  ) -> Result<Value, VmError> {
    if matches!(&*expr.object.stx, Expr::Super(_)) {
      let member_value = self.eval_expr(scope, &expr.member)?;
      scope.push_root(member_value)?;
      let key = self.to_property_key_operator(scope, member_value)?;
      let (value, _) = self.eval_super_property(scope, key)?;
      return Ok(value);
    }
    let base = self.eval_expr(scope, &expr.object)?;
    if expr.optional_chaining && is_nullish(base) {
      return Ok(Value::Undefined);
    }

    // Root `base` across key evaluation + `ToPropertyKey`, which may allocate and trigger GC.
    let mut key_scope = scope.reborrow();
    key_scope.push_root(base)?;
    let member_value = self.eval_expr(&mut key_scope, &expr.member)?;
    key_scope.push_root(member_value)?;
    let key = self.to_property_key_operator(&mut key_scope, member_value)?;
    self.get_v(&mut key_scope, base, key)
  }

  /// Evaluates a whole `OptionalExpression` (ECMA-262 §13.3.9), applying full-chain short-circuit:
  /// once any `?.` link sees a nullish base, the entire chain evaluates to `undefined`.
  fn eval_optional_chain(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<Expr>,
  ) -> Result<Value, VmError> {
    match self.eval_chain(scope, expr)? {
      ChainVal::ShortCircuit => Ok(Value::Undefined),
      ChainVal::Value { value, .. } => Ok(value),
    }
  }

  /// Evaluates one node of an optional chain, threading short-circuit and the callee `this` value.
  ///
  /// A parenthesized sub-expression is a chain boundary: it is evaluated as a fresh expression
  /// (which may itself be a separate optional chain), and its own short-circuit does not propagate
  /// out (ECMA-262 §13.3.9 — `(a?.b).c` throws when `a` is nullish).
  fn eval_chain(&mut self, scope: &mut Scope<'_>, expr: &Node<Expr>) -> Result<ChainVal, VmError> {
    // Evaluate a base sub-expression, threading its `this` binding. Parenthesization is a
    // short-circuit boundary (§13.3.9): a `?.` inside parentheses does not propagate its
    // short-circuit outward — it becomes a plain `undefined` value — but the `this` value from the
    // inner reference is still preserved (`(a.b)?.()` and `(a?.b).c` both bind `this` to `a`).
    let eval_base =
      |this: &mut Self, scope: &mut Scope<'_>, base: &Node<Expr>| -> Result<ChainVal, VmError> {
        let parenthesized = base.assoc.get::<ParenthesizedExpr>().is_some();
        match &*base.stx {
          Expr::Member(_) | Expr::ComputedMember(_) | Expr::Call(_) => {
            let result = this.eval_chain(scope, base)?;
            if parenthesized {
              Ok(match result {
                ChainVal::ShortCircuit => ChainVal::Value {
                  value: Value::Undefined,
                  this: Value::Undefined,
                },
                v => v,
              })
            } else {
              Ok(result)
            }
          }
          _ => {
            let value = this.eval_expr(scope, base)?;
            Ok(ChainVal::Value {
              value,
              this: Value::Undefined,
            })
          }
        }
      };

    match &*expr.stx {
      Expr::Member(node) => {
        let member = &node.stx;
        if matches!(&*member.left.stx, Expr::Super(_)) {
          let key_s = scope.alloc_string(&member.right)?;
          let key = PropertyKey::from_string(key_s);
          let (value, this_value) = self.eval_super_property(scope, key)?;
          return Ok(ChainVal::Value {
            value,
            this: this_value,
          });
        }
        let base = match eval_base(self, scope, &member.left)? {
          ChainVal::ShortCircuit => return Ok(ChainVal::ShortCircuit),
          ChainVal::Value { value, .. } => value,
        };
        if member.optional_chaining && is_nullish(base) {
          return Ok(ChainVal::ShortCircuit);
        }
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let key_s = key_scope.alloc_string(&member.right)?;
        let key = PropertyKey::from_string(key_s);
        let value = self.get_v(&mut key_scope, base, key)?;
        Ok(ChainVal::Value { value, this: base })
      }
      Expr::ComputedMember(node) => {
        let member = &node.stx;
        if matches!(&*member.object.stx, Expr::Super(_)) {
          let member_value = self.eval_expr(scope, &member.member)?;
          scope.push_root(member_value)?;
          let key = self.to_property_key_operator(scope, member_value)?;
          let (value, this_value) = self.eval_super_property(scope, key)?;
          return Ok(ChainVal::Value {
            value,
            this: this_value,
          });
        }
        let base = match eval_base(self, scope, &member.object)? {
          ChainVal::ShortCircuit => return Ok(ChainVal::ShortCircuit),
          ChainVal::Value { value, .. } => value,
        };
        if member.optional_chaining && is_nullish(base) {
          return Ok(ChainVal::ShortCircuit);
        }
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let member_value = self.eval_expr(&mut key_scope, &member.member)?;
        key_scope.push_root(member_value)?;
        let key = self.to_property_key_operator(&mut key_scope, member_value)?;
        let value = self.get_v(&mut key_scope, base, key)?;
        Ok(ChainVal::Value { value, this: base })
      }
      Expr::Call(node) => {
        let call = &node.stx;
        if matches!(&*call.callee.stx, Expr::Super(_)) {
          let value = self.eval_super_call(scope, call)?;
          if call.optional_chaining && is_nullish(value) {
            return Ok(ChainVal::ShortCircuit);
          }
          return Ok(ChainVal::Value {
            value,
            this: Value::Undefined,
          });
        }
        let (callee_value, this_value) = match eval_base(self, scope, &call.callee)? {
          ChainVal::ShortCircuit => return Ok(ChainVal::ShortCircuit),
          ChainVal::Value { value, this } => (value, this),
        };
        if call.optional_chaining && is_nullish(callee_value) {
          return Ok(ChainVal::ShortCircuit);
        }
        let value = self.eval_call_with_callee(scope, call, callee_value, this_value)?;
        Ok(ChainVal::Value {
          value,
          this: Value::Undefined,
        })
      }
      // Non-chain expression (chain root, e.g. an identifier): evaluate normally.
      _ => {
        let value = self.eval_expr(scope, expr)?;
        Ok(ChainVal::Value {
          value,
          this: Value::Undefined,
        })
      }
    }
  }

  /// Resolves the target property reference for `delete <OptionalExpression>`.
  ///
  /// Returns `Ok(None)` when the chain short-circuits (a nullish `?.` base, or a nullish/primitive
  /// base for the final delete link — deleting a property of a primitive is a no-op that yields
  /// `true`), else `Ok(Some((object, key)))` for the ordinary delete.
  fn eval_chain_delete(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<Expr>,
  ) -> Result<Option<(GcObject, PropertyKey)>, VmError> {
    match &*expr.stx {
      Expr::Member(node) => {
        let member = &node.stx;
        let base = match self.eval_chain(scope, &member.left)? {
          ChainVal::ShortCircuit => return Ok(None),
          ChainVal::Value { value, .. } => value,
        };
        if member.optional_chaining && is_nullish(base) {
          return Ok(None);
        }
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let key_s = key_scope.alloc_string(&member.right)?;
        let key = PropertyKey::from_string(key_s);
        match base {
          Value::Object(object) => Ok(Some((object, key))),
          Value::Undefined | Value::Null => Err(throw_type_error(
            self.vm,
            &mut key_scope,
            "Cannot delete property of null or undefined",
          )?),
          _ => Ok(None),
        }
      }
      Expr::ComputedMember(node) => {
        let member = &node.stx;
        let base = match self.eval_chain(scope, &member.object)? {
          ChainVal::ShortCircuit => return Ok(None),
          ChainVal::Value { value, .. } => value,
        };
        if member.optional_chaining && is_nullish(base) {
          return Ok(None);
        }
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let member_value = self.eval_expr(&mut key_scope, &member.member)?;
        key_scope.push_root(member_value)?;
        let key = self.to_property_key_operator(&mut key_scope, member_value)?;
        match base {
          Value::Object(object) => Ok(Some((object, key))),
          Value::Undefined | Value::Null => Err(throw_type_error(
            self.vm,
            &mut key_scope,
            "Cannot delete property of null or undefined",
          )?),
          _ => Ok(None),
        }
      }
      _ => {
        // Not a member access at the top: evaluate for side effects; `delete` yields `true`.
        let _ = self.eval_expr(scope, expr)?;
        Ok(None)
      }
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
        let base = self.eval_expr(scope, &member.stx.left)?;
        if matches!(base, Value::Undefined | Value::Null) {
          let type_name = if matches!(base, Value::Null) {
            "null"
          } else {
            "undefined"
          };
          let msg = format!(
            "Cannot set properties of {type_name} (setting '{}')",
            member.stx.right
          );
          return Err(throw_type_error(self.vm, scope, &msg)?);
        }
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let key_s = key_scope.alloc_string(&member.stx.right)?;
        Ok(Reference::Property {
          base,
          key: PropertyKey::from_string(key_s),
        })
      }
      Expr::ComputedMember(member) => {
        if member.stx.optional_chaining {
          return Err(VmError::Unimplemented(
            "optional chaining computed member access",
          ));
        }
        let base = self.eval_expr(scope, &member.stx.object)?;
        if matches!(base, Value::Undefined | Value::Null) {
          return Err(throw_type_error(
            self.vm,
            scope,
            "Cannot set properties of null or undefined",
          )?);
        }
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
        key_scope.push_root(member_value)?;
        let key = self.to_property_key_operator(&mut key_scope, member_value)?;
        Ok(Reference::Property { base, key })
      }
      _ => Err(VmError::Unimplemented("expression is not a reference")),
    }
  }

  fn root_reference(
    &self,
    scope: &mut Scope<'_>,
    reference: &Reference<'_>,
  ) -> Result<(), VmError> {
    let Reference::Property { base, key } = *reference else {
      return Ok(());
    };
    scope.push_root(base)?;
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
      Reference::Binding(name) => {
        match self.env.get(self.vm, self.host, self.hooks, scope, name)? {
          Some(v) => Ok(v),
          None => {
            let msg = format!("{name} is not defined");
            Err(throw_reference_error(self.vm, scope, &msg)?)
          }
        }
      }
      Reference::Property { base, key } => {
        let mut get_scope = scope.reborrow();
        self.root_reference(&mut get_scope, reference)?;
        self.get_v(&mut get_scope, base, key)
      }
    }
  }

  /// ECMAScript `GetV(V, P)` (ECMA-262 §7.3.2): get property `key` from an arbitrary value `base`,
  /// using `base` itself as the receiver / `this` for accessors and methods.
  ///
  /// Unlike `[[Get]]` on an object, `GetV` accepts primitive bases. Per §13.3.3 (property access on
  /// primitive bases), rather than allocating a wrapper object for a *get* we resolve the property
  /// against the matching well-known prototype (`String.prototype`, `Number.prototype`, …) with the
  /// primitive as the receiver. String `length` and integer-index access are the String exotic
  /// own-property behaviors (§10.4.3 / §22.1.3.1) and are handled before the prototype lookup.
  ///
  /// `null`/`undefined` bases throw a catchable `TypeError` (§7.3.2 step 1 → ToObject throws).
  fn get_v(
    &mut self,
    scope: &mut Scope<'_>,
    base: Value,
    key: PropertyKey,
  ) -> Result<Value, VmError> {
    // Resolve the property against `proto` with `base` as the receiver, rooting both across any
    // accessor call / allocation that `[[Get]]` may perform.
    let get_on_proto = |this: &mut Self, scope: &mut Scope<'_>, proto: GcObject| {
      let mut get_scope = scope.reborrow();
      get_scope.push_root(base)?;
      get_scope.push_root(Value::Object(proto))?;
      match key {
        PropertyKey::String(s) => get_scope.push_root(Value::String(s))?,
        PropertyKey::Symbol(s) => get_scope.push_root(Value::Symbol(s))?,
      };
      get_scope.ordinary_get_with_host_and_hooks(this.vm, this.host, this.hooks, proto, key, base)
    };

    match base {
      Value::Object(object) => {
        let mut get_scope = scope.reborrow();
        get_scope.push_root(Value::Object(object))?;
        match key {
          PropertyKey::String(s) => get_scope.push_root(Value::String(s))?,
          PropertyKey::Symbol(s) => get_scope.push_root(Value::Symbol(s))?,
        };
        get_scope.ordinary_get_with_host_and_hooks(
          self.vm,
          self.host,
          self.hooks,
          object,
          key,
          Value::Object(object),
        )
      }
      Value::Undefined | Value::Null => {
        let type_name = if matches!(base, Value::Null) {
          "null"
        } else {
          "undefined"
        };
        let prop = match key {
          PropertyKey::String(s) => scope.heap().get_string(s)?.to_utf8_lossy(),
          PropertyKey::Symbol(_) => "Symbol(...)".to_string(),
        };
        let msg = format!("Cannot read properties of {type_name} (reading '{prop}')");
        Err(throw_type_error(self.vm, scope, &msg)?)
      }
      Value::String(s) => {
        // String exotic own properties: `length` and canonical integer indices.
        if let PropertyKey::String(k) = key {
          let k_str = scope.heap().get_string(k)?.to_utf8_lossy();
          if k_str == "length" {
            let len = scope.heap().get_string(s)?.len_code_units();
            return Ok(Value::Number(len as f64));
          }
          if let Some(idx) = canonical_array_index(&k_str) {
            let units = scope.heap().get_string(s)?.as_code_units();
            if idx < units.len() {
              let unit = units[idx];
              let out = scope.alloc_string_from_u16_vec(vec![unit])?;
              return Ok(Value::String(out));
            }
            // Out-of-range integer index: the exotic own property is absent and
            // `String.prototype` has no such property, so the result is `undefined`.
            return Ok(Value::Undefined);
          }
        }
        let proto = self.string_prototype()?;
        get_on_proto(self, scope, proto)
      }
      Value::Number(_) => {
        let proto = self.number_prototype()?;
        get_on_proto(self, scope, proto)
      }
      Value::Bool(_) => {
        let proto = self.boolean_prototype()?;
        get_on_proto(self, scope, proto)
      }
      Value::Symbol(_) => {
        let proto = self.symbol_prototype()?;
        get_on_proto(self, scope, proto)
      }
      Value::BigInt(_) => {
        let proto = self.bigint_prototype()?;
        get_on_proto(self, scope, proto)
      }
    }
  }

  fn string_prototype(&self) -> Result<GcObject, VmError> {
    Ok(
      self
        .vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
        .string_prototype(),
    )
  }
  fn number_prototype(&self) -> Result<GcObject, VmError> {
    Ok(
      self
        .vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
        .number_prototype(),
    )
  }
  fn boolean_prototype(&self) -> Result<GcObject, VmError> {
    Ok(
      self
        .vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
        .boolean_prototype(),
    )
  }
  fn symbol_prototype(&self) -> Result<GcObject, VmError> {
    Ok(
      self
        .vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
        .symbol_prototype(),
    )
  }
  fn bigint_prototype(&self) -> Result<GcObject, VmError> {
    Ok(
      self
        .vm
        .intrinsics()
        .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
        .bigint_prototype(),
    )
  }

  fn put_value_to_reference(
    &mut self,
    scope: &mut Scope<'_>,
    reference: &Reference<'_>,
    value: Value,
  ) -> Result<(), VmError> {
    match *reference {
      Reference::Binding(name) => self.env.set(
        self.vm,
        self.host,
        self.hooks,
        scope,
        name,
        value,
        self.strict,
      ),
      Reference::Property { base, key } => {
        // PutValue (§6.2.5.5): for a property reference, `[[Set]]` is invoked with
        // GetThisValue(V) as the receiver. When HasPrimitiveBase, the Set *target* is
        // ToObject(base); we start at the matching intrinsic prototype (equivalent for
        // ordinary wrappers with no own properties) so Proxy traps on that chain fire.
        let (target, receiver) = match base {
          Value::Object(object) => (object, Value::Object(object)),
          Value::Undefined | Value::Null => {
            return Err(throw_type_error(
              self.vm,
              scope,
              "Cannot set properties of null or undefined",
            )?);
          }
          Value::Number(_) => (self.number_prototype()?, base),
          Value::Bool(_) => (self.boolean_prototype()?, base),
          Value::String(_) => (self.string_prototype()?, base),
          Value::Symbol(_) => (self.symbol_prototype()?, base),
          Value::BigInt(_) => (self.bigint_prototype()?, base),
        };
        let mut set_scope = scope.reborrow();
        set_scope.push_root(base)?;
        set_scope.push_root(Value::Object(target))?;
        set_scope.push_root(value)?;
        let ok = set_scope.ordinary_set_with_host_and_hooks(
          self.vm, self.host, self.hooks, target, key, value, receiver,
        )?;
        if ok {
          Ok(())
        } else if self.strict {
          Err(throw_type_error(
            self.vm,
            &mut set_scope,
            "Cannot assign to read-only property",
          )?)
        } else {
          // Sloppy-mode assignment to a non-writable/non-extensible target fails silently.
          Ok(())
        }
      }
    }
  }

  fn eval_func_expr(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<FuncExpr>,
  ) -> Result<Value, VmError> {
    let name = expr.stx.name.as_ref().map(|n| n.stx.name.as_str());
    self.instantiate_function_expr(
      scope,
      expr.loc.start_u32(),
      expr.loc.end_u32(),
      name,
      &expr.stx.func,
    )
  }

  fn eval_class_decl(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &ClassDecl,
  ) -> Result<Completion, VmError> {
    let Some(name) = &decl.name else {
      return Err(VmError::Unimplemented("anonymous class declaration"));
    };
    let class_name = name.stx.name.as_str();
    let value = self.eval_class_definition(
      scope,
      Some(class_name),
      Some(class_name),
      decl.extends.as_ref(),
      &decl.members,
    )?;
    let mut init_scope = scope.reborrow();
    init_scope.push_root(value)?;
    init_scope
      .heap_mut()
      .env_initialize_binding(self.env.lexical_env, class_name, value)?;
    Ok(Completion::empty())
  }

  fn eval_class_expr(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<ClassExpr>,
    name_override: Option<&str>,
  ) -> Result<Value, VmError> {
    let binding = expr.stx.name.as_ref().map(|n| n.stx.name.as_str());
    let class_name = name_override.or(binding);
    self.eval_class_definition(
      scope,
      binding,
      class_name,
      expr.stx.extends.as_ref(),
      &expr.stx.members,
    )
  }

  /// ClassDefinitionEvaluation (ECMA-262 §15.7.14).
  ///
  /// - `class_binding`: BindingIdentifier for named class expressions/declarations (class env).
  /// - `class_name`: name property / NamedEvaluation name (`None` → empty string, then static
  ///   `name` methods may overwrite).
  /// - Supports `extends` + `[[HomeObject]]` / derived `[[ConstructorKind]]` for `super`.
  fn eval_class_definition(
    &mut self,
    scope: &mut Scope<'_>,
    class_binding: Option<&str>,
    class_name: Option<&str>,
    extends: Option<&Node<Expr>>,
    members: &[Node<ClassMember>],
  ) -> Result<Value, VmError> {
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;

    let outer_lex = self.env.lexical_env;
    // Class env is required when there is a BindingIdentifier *or* private elements (so methods
    // can resolve `#name` via the lexical outer chain — a minimal PrivateEnvironment stand-in).
    let has_private = members.iter().any(|m| class_member_is_private(&m.stx));
    let class_env = if class_binding.is_some() || has_private {
      let env = scope.env_create(Some(outer_lex))?;
      if let Some(binding) = class_binding {
        scope.env_create_immutable_binding(env, binding, true)?;
      }
      Some(env)
    } else {
      None
    };
    let closure_env = class_env.unwrap_or(outer_lex);

    let mut class_scope = scope.reborrow();
    if let Some(env) = class_env {
      self.env.set_lexical_env(class_scope.heap_mut(), env);
    }

    let result = (|| -> Result<Value, VmError> {
      // Evaluate ClassHeritage inside the class environment (named class expr self-reference).
      let (proto_parent, ctor_parent, is_derived) = if let Some(heritage) = extends {
        let superclass = self.eval_expr(&mut class_scope, heritage)?;
        class_scope.push_root(superclass)?;
        match superclass {
          Value::Null => (None, Some(intr.function_prototype()), true),
          Value::Object(super_obj) => {
            if !class_scope
              .heap()
              .is_constructor(Value::Object(super_obj))?
            {
              return Err(throw_type_error(
                self.vm,
                &mut class_scope,
                "Class extends value is not a constructor",
              )?);
            }
            let proto_key = PropertyKey::from_string(class_scope.alloc_string("prototype")?);
            let proto_parent_val = class_scope.ordinary_get_with_host_and_hooks(
              self.vm,
              &mut *self.host,
              &mut *self.hooks,
              super_obj,
              proto_key,
              Value::Object(super_obj),
            )?;
            let proto_parent = match proto_parent_val {
              Value::Object(o) => Some(o),
              Value::Null => None,
              _ => {
                return Err(throw_type_error(
                  self.vm,
                  &mut class_scope,
                  "Class extends value does not have a valid prototype property",
                )?)
              }
            };
            (proto_parent, Some(super_obj), true)
          }
          _ => {
            return Err(throw_type_error(
              self.vm,
              &mut class_scope,
              "Class extends value is not a constructor or null",
            )?)
          }
        }
      } else {
        (
          Some(intr.object_prototype()),
          Some(intr.function_prototype()),
          false,
        )
      };

      let constructor_member = members.iter().find(|m| is_class_constructor_method(&m.stx));

      let name_s = class_scope.alloc_string(class_name.unwrap_or(""))?;
      class_scope.push_root(Value::String(name_s))?;

      let ctor = if let Some(ctor_member) = constructor_member {
        let ClassOrObjVal::Method(method) = &ctor_member.stx.val else {
          return Err(VmError::Unimplemented("class constructor must be a method"));
        };
        let func_node = &method.stx.func;
        let length = function_length(&func_node.stx);
        let rel_start = ctor_member
          .loc
          .start_u32()
          .saturating_sub(self.env.prefix_len());
        let rel_end = func_node
          .loc
          .end_u32()
          .saturating_sub(self.env.prefix_len());
        let span_start = self.env.base_offset().saturating_add(rel_start);
        let span_end = self.env.base_offset().saturating_add(rel_end);
        let code = self.vm.register_ecma_function(
          self.env.source(),
          span_start,
          span_end,
          EcmaFunctionKind::ObjectMember,
          func_node,
        )?;
        // Class bodies are strict; alloc also runs MakeConstructor (prototype wired below).
        let func_obj = class_scope.alloc_ecma_function(
          code,
          /* is_constructable */ true,
          name_s,
          length,
          ThisMode::Strict,
          true,
          Some(closure_env),
          Some(intr.object_prototype()),
        )?;
        class_scope
          .heap_mut()
          .set_function_is_class_constructor(func_obj, true)?;
        func_obj
      } else if is_derived {
        class_scope.alloc_native_function(
          intr.class_constructor_call(),
          Some(intr.class_default_derived_construct()),
          name_s,
          0,
        )?
      } else {
        class_scope.alloc_native_function(
          intr.class_constructor_call(),
          Some(intr.class_default_construct()),
          name_s,
          0,
        )?
      };

      class_scope.push_root(Value::Object(ctor))?;
      class_scope
        .heap_mut()
        .object_set_prototype(ctor, ctor_parent)?;
      class_scope
        .heap_mut()
        .set_function_realm(ctor, self.env.global_object())?;
      if let Some(realm) = self.vm.current_realm() {
        class_scope.heap_mut().set_function_job_realm(ctor, realm)?;
      }
      if is_derived {
        class_scope
          .heap_mut()
          .set_function_is_derived_constructor(ctor, true)?;
        class_scope
          .heap_mut()
          .set_function_is_class_constructor(ctor, true)?;
      }

      // SetFunctionName happens before static elements so `static name()` can overwrite.
      crate::function_properties::set_function_name(
        &mut class_scope,
        ctor,
        PropertyKey::from_string(name_s),
        None,
      )?;

      // Reuse MakeConstructor's prototype object; classes make `.prototype` non-writable.
      let proto_key = PropertyKey::from_string(class_scope.alloc_string("prototype")?);
      let proto = match class_scope.heap().get_own_property(ctor, proto_key)? {
        Some(desc) => match desc.kind {
          PropertyKind::Data {
            value: Value::Object(o),
            ..
          } => o,
          _ => {
            return Err(VmError::InvariantViolation(
              "class constructor missing .prototype object",
            ))
          }
        },
        None => {
          return Err(VmError::InvariantViolation(
            "class constructor missing .prototype",
          ))
        }
      };
      class_scope.push_root(Value::Object(proto))?;
      class_scope
        .heap_mut()
        .object_set_prototype(proto, proto_parent)?;
      // MakeMethod(F, proto) — constructor [[HomeObject]] for super property in ctors.
      class_scope
        .heap_mut()
        .set_function_home_object(ctor, proto)?;
      class_scope.define_property(
        ctor,
        proto_key,
        PropertyDescriptor {
          enumerable: false,
          configurable: false,
          kind: PropertyKind::Data {
            value: Value::Object(proto),
            writable: false,
          },
        },
      )?;

      // Bind private names into the class env and collect instance private keys to install.
      let mut instance_private_names: Vec<crate::GcSymbol> = Vec::new();
      if has_private {
        let private_env = class_env.expect("private elements require class env");
        for member in members {
          if is_class_constructor_method(&member.stx) {
            continue;
          }
          if let Some(name_str) = private_member_name(&member.stx) {
            if !class_scope.heap().env_has_binding(private_env, name_str)? {
              let desc = class_scope.alloc_string(name_str)?;
              class_scope.push_root(Value::String(desc))?;
              let sym = class_scope.new_symbol(Some(desc))?;
              class_scope.push_root(Value::Symbol(sym))?;
              class_scope.env_create_immutable_binding(private_env, name_str, true)?;
              class_scope.heap_mut().env_initialize_binding(
                private_env,
                name_str,
                Value::Symbol(sym),
              )?;
              if !member.stx.static_ {
                instance_private_names
                  .try_reserve(1)
                  .map_err(|_| VmError::OutOfMemory)?;
                instance_private_names.push(sym);
              }
            } else if !member.stx.static_ {
              // Getter+setter share one private name; ensure the instance list has it once.
              let value = class_scope
                .heap()
                .env_get_binding_value(private_env, name_str, true)?;
              if let Value::Symbol(sym) = value {
                if !instance_private_names.contains(&sym) {
                  instance_private_names
                    .try_reserve(1)
                    .map_err(|_| VmError::OutOfMemory)?;
                  instance_private_names.push(sym);
                }
              }
            }
          }
        }
      }

      for member in members {
        if is_class_constructor_method(&member.stx) {
          continue;
        }
        self.define_class_element(&mut class_scope, ctor, proto, member)?;
      }

      if !instance_private_names.is_empty() {
        class_scope
          .heap_mut()
          .set_function_instance_private_names(ctor, instance_private_names.into_boxed_slice())?;
      }

      if let Some(binding) = class_binding {
        class_scope
          .heap_mut()
          .env_initialize_binding(closure_env, binding, Value::Object(ctor))?;
      }

      Ok(Value::Object(ctor))
    })();

    self.env.set_lexical_env(class_scope.heap_mut(), outer_lex);
    result
  }

  fn define_class_element(
    &mut self,
    scope: &mut Scope<'_>,
    constructor: GcObject,
    proto: GcObject,
    member: &Node<ClassMember>,
  ) -> Result<(), VmError> {
    let member = &member.stx;
    if let ClassOrObjVal::StaticBlock(block) = &member.val {
      return self.eval_class_static_block(scope, constructor, &block.stx);
    }
    // Private fields/methods/accessors: names are bound during ClassDefinitionEvaluation;
    // instance keys are installed at construction. Method/accessor bodies are not attached yet
    // (sufficient for `#x in` presence checks).
    if matches!(&member.key, ClassOrObjKey::Direct(d) if d.stx.tt == TT::PrivateMember) {
      match &member.val {
        ClassOrObjVal::Prop(_)
        | ClassOrObjVal::Method(_)
        | ClassOrObjVal::Getter(_)
        | ClassOrObjVal::Setter(_) => return Ok(()),
        ClassOrObjVal::StaticBlock(_) | ClassOrObjVal::IndexSignature(_) => {
          return Err(VmError::Unimplemented("private class elements"));
        }
      }
    }

    let key_loc_start = match &member.key {
      ClassOrObjKey::Direct(direct) => direct.loc.start_u32(),
      ClassOrObjKey::Computed(expr) => expr.loc.start_u32(),
    };
    let key = match &member.key {
      ClassOrObjKey::Direct(direct) => {
        let key_s = if let Some(units) = literal_string_code_units(&direct.assoc) {
          scope.alloc_string_from_code_units(units)?
        } else if direct.stx.tt == TT::LiteralNumber {
          let n = direct
            .stx
            .key
            .parse::<f64>()
            .map_err(|_| VmError::Unimplemented("numeric literal property name parse"))?;
          scope.heap_mut().to_string(Value::Number(n))?
        } else {
          scope.alloc_string(&direct.stx.key)?
        };
        PropertyKey::from_string(key_s)
      }
      ClassOrObjKey::Computed(expr) => {
        let value = self.eval_expr(scope, expr)?;
        scope.push_root(value)?;
        self.to_property_key_operator(scope, value)?
      }
    };
    match key {
      PropertyKey::String(s) => scope.push_root(Value::String(s))?,
      PropertyKey::Symbol(s) => scope.push_root(Value::Symbol(s))?,
    };

    let home = if member.static_ { constructor } else { proto };
    scope.push_root(Value::Object(home))?;

    match &member.val {
      ClassOrObjVal::Method(method) => {
        let func_node = &method.stx.func;
        let flavor = FunctionFlavor::of(&func_node.stx)?;
        let length = function_length(&func_node.stx);
        let rel_start = key_loc_start.saturating_sub(self.env.prefix_len());
        let rel_end = func_node
          .loc
          .end_u32()
          .saturating_sub(self.env.prefix_len());
        let span_start = self.env.base_offset().saturating_add(rel_start);
        let span_end = self.env.base_offset().saturating_add(rel_end);
        let code = self.vm.register_ecma_function(
          self.env.source(),
          span_start,
          span_end,
          EcmaFunctionKind::ObjectMember,
          func_node,
        )?;
        let name_string = match key {
          PropertyKey::String(s) => s,
          PropertyKey::Symbol(_) => scope.alloc_string("")?,
        };
        let func_obj = scope.alloc_ecma_function(
          code,
          /* is_constructable */ false,
          name_string,
          length,
          ThisMode::Strict,
          true,
          Some(self.env.lexical_env),
          None,
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
        if let Some(realm) = self.vm.current_realm() {
          scope.heap_mut().set_function_job_realm(func_obj, realm)?;
        }
        self.apply_function_flavor(scope, func_obj, flavor)?;
        scope.push_root(Value::Object(func_obj))?;
        // MakeMethod(F, home) — [[HomeObject]] for `super` property access.
        scope.heap_mut().set_function_home_object(func_obj, home)?;
        if !matches!(key, PropertyKey::String(_)) {
          crate::function_properties::set_function_name(scope, func_obj, key, None)?;
        }
        // Class methods are non-enumerable.
        scope.define_property(
          home,
          key,
          PropertyDescriptor {
            enumerable: false,
            configurable: true,
            kind: PropertyKind::Data {
              value: Value::Object(func_obj),
              writable: true,
            },
          },
        )?;
      }
      ClassOrObjVal::Getter(getter) => {
        let func_node = &getter.stx.func;
        let length = function_length(&func_node.stx);
        let rel_start = key_loc_start.saturating_sub(self.env.prefix_len());
        let rel_end = func_node
          .loc
          .end_u32()
          .saturating_sub(self.env.prefix_len());
        let span_start = self.env.base_offset().saturating_add(rel_start);
        let span_end = self.env.base_offset().saturating_add(rel_end);
        let code = self.vm.register_ecma_function(
          self.env.source(),
          span_start,
          span_end,
          EcmaFunctionKind::ObjectMember,
          func_node,
        )?;
        let name_string = scope.alloc_string("")?;
        let func_obj = scope.alloc_ecma_function(
          code,
          false,
          name_string,
          length,
          ThisMode::Strict,
          true,
          Some(self.env.lexical_env),
          None,
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
        if let Some(realm) = self.vm.current_realm() {
          scope.heap_mut().set_function_job_realm(func_obj, realm)?;
        }
        scope.push_root(Value::Object(func_obj))?;
        scope.heap_mut().set_function_home_object(func_obj, home)?;
        crate::function_properties::set_function_name(scope, func_obj, key, Some("get"))?;
        let existing = scope.heap().get_own_property(home, key)?;
        let set = match existing.map(|d| d.kind) {
          Some(PropertyKind::Accessor { set, .. }) => set,
          _ => Value::Undefined,
        };
        scope.define_property(
          home,
          key,
          PropertyDescriptor {
            enumerable: false,
            configurable: true,
            kind: PropertyKind::Accessor {
              get: Value::Object(func_obj),
              set,
            },
          },
        )?;
      }
      ClassOrObjVal::Setter(setter) => {
        let func_node = &setter.stx.func;
        let length = function_length(&func_node.stx);
        let rel_start = key_loc_start.saturating_sub(self.env.prefix_len());
        let rel_end = func_node
          .loc
          .end_u32()
          .saturating_sub(self.env.prefix_len());
        let span_start = self.env.base_offset().saturating_add(rel_start);
        let span_end = self.env.base_offset().saturating_add(rel_end);
        let code = self.vm.register_ecma_function(
          self.env.source(),
          span_start,
          span_end,
          EcmaFunctionKind::ObjectMember,
          func_node,
        )?;
        let name_string = scope.alloc_string("")?;
        let func_obj = scope.alloc_ecma_function(
          code,
          false,
          name_string,
          length,
          ThisMode::Strict,
          true,
          Some(self.env.lexical_env),
          None,
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
        if let Some(realm) = self.vm.current_realm() {
          scope.heap_mut().set_function_job_realm(func_obj, realm)?;
        }
        scope.push_root(Value::Object(func_obj))?;
        scope.heap_mut().set_function_home_object(func_obj, home)?;
        crate::function_properties::set_function_name(scope, func_obj, key, Some("set"))?;
        let existing = scope.heap().get_own_property(home, key)?;
        let get = match existing.map(|d| d.kind) {
          Some(PropertyKind::Accessor { get, .. }) => get,
          _ => Value::Undefined,
        };
        scope.define_property(
          home,
          key,
          PropertyDescriptor {
            enumerable: false,
            configurable: true,
            kind: PropertyKind::Accessor {
              get,
              set: Value::Object(func_obj),
            },
          },
        )?;
      }
      ClassOrObjVal::Prop(_) => {
        return Err(VmError::Unimplemented("class fields"));
      }
      ClassOrObjVal::StaticBlock(_) => {
        // Handled at the top of `define_class_element`.
        return Err(VmError::InvariantViolation(
          "class static block reached element define path",
        ));
      }
      ClassOrObjVal::IndexSignature(_) => {
        return Err(VmError::Unimplemented("class index signature"));
      }
    }
    Ok(())
  }

  /// Class static initialization block (ECMA-262 §15.7.10 / ClassStaticBlockDefinitionEvaluation).
  ///
  /// Minimal implementation: evaluate the block's statement list in a fresh declarative
  /// environment (child of the class env) with `this` bound to the constructor. Sufficient for
  /// generator/`await`-as-identifier early-error tests and typical side-effecting static blocks.
  fn eval_class_static_block(
    &mut self,
    scope: &mut Scope<'_>,
    constructor: GcObject,
    block: &parse_js::ast::class_or_object::ClassStaticBlock,
  ) -> Result<(), VmError> {
    let outer = self.env.lexical_env;
    let block_env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), block_env);
    let prev_this = self.this;
    self.this = Value::Object(constructor);
    scope.push_root(Value::Object(constructor))?;
    let result = self
      .instantiate_block_decls_in_stmt_list(scope, block_env, &block.body)
      .and_then(|_| self.eval_stmt_list(scope, &block.body));
    self.this = prev_this;
    self.env.set_lexical_env(scope.heap_mut(), outer);
    match result? {
      Completion::Normal(_) => Ok(()),
      Completion::Throw(t) => Err(VmError::ThrowWithStack {
        value: t.value,
        stack: t.stack,
      }),
      Completion::Return(_) | Completion::Break(_, _) | Completion::Continue(_, _) => Err(
        VmError::InvariantViolation("abrupt completion escaped class static block"),
      ),
    }
  }

  fn eval_arrow_func_expr(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<ArrowFuncExpr>,
  ) -> Result<Value, VmError> {
    self.instantiate_arrow_function_expr(
      scope,
      expr.loc.start_u32(),
      expr.loc.end_u32(),
      &expr.stx.func,
    )
  }

  fn instantiate_function_expr(
    &mut self,
    scope: &mut Scope<'_>,
    loc_start: u32,
    loc_end: u32,
    name: Option<&str>,
    func_node: &Node<Func>,
  ) -> Result<Value, VmError> {
    use crate::function::ThisMode;
    use crate::vm::EcmaFunctionKind;

    let func = &*func_node.stx;
    let flavor = FunctionFlavor::of(func)?;
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

    // Named FunctionExpression: fresh env with immutable name binding (§15.2.1 /
    // NamedEvaluation). Closure [[Environment]] is that env so body references see
    // the function; sloppy assignment to the name is a silent no-op.
    let outer_lex = self.env.lexical_env;
    let closure_env = if let Some(binding_name) = name {
      let name_env = scope.env_create(Some(outer_lex))?;
      // Named function-expression name: CreateImmutableBinding(N, false).
      scope.env_create_immutable_binding(name_env, binding_name, false)?;
      name_env
    } else {
      outer_lex
    };

    let code_id = self.vm.register_ecma_function(
      self.env.source(),
      span_start,
      span_end,
      EcmaFunctionKind::Expr,
      func_node,
    )?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    let func_obj = scope.alloc_ecma_function(
      code_id,
      true,
      name_s,
      length,
      this_mode,
      is_strict,
      Some(closure_env),
      Some(intr.object_prototype()),
    )?;
    scope
      .heap_mut()
      .object_set_prototype(func_obj, Some(intr.function_prototype()))?;
    scope
      .heap_mut()
      .set_function_realm(func_obj, self.env.global_object())?;
    if let Some(realm) = self.vm.current_realm() {
      scope.heap_mut().set_function_job_realm(func_obj, realm)?;
    }
    if func.arrow {
      scope
        .heap_mut()
        .set_function_bound_this(func_obj, self.this)?;
      scope
        .heap_mut()
        .set_function_bound_new_target(func_obj, self.new_target)?;
    }
    self.apply_function_flavor(scope, func_obj, flavor)?;

    if let Some(binding_name) = name {
      scope.heap_mut().env_initialize_binding(
        closure_env,
        binding_name,
        Value::Object(func_obj),
      )?;
    }

    Ok(Value::Object(func_obj))
  }

  fn instantiate_arrow_function_expr(
    &mut self,
    scope: &mut Scope<'_>,
    loc_start: u32,
    loc_end: u32,
    func_node: &Node<Func>,
  ) -> Result<Value, VmError> {
    use crate::function::ThisMode;
    use crate::vm::EcmaFunctionKind;

    let func = &*func_node.stx;
    // Generator arrows are not a grammar production; async arrows are allowed.
    if func.generator {
      return Err(VmError::Unimplemented("async/generator functions"));
    }
    let flavor = FunctionFlavor::of(func)?;
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

    let code_id = self.vm.register_ecma_function(
      self.env.source(),
      span_start,
      span_end,
      EcmaFunctionKind::Expr,
      func_node,
    )?;
    let mut alloc_scope = scope.reborrow();
    // Root captured lexical bindings across allocation in case it triggers GC.
    let roots = [self.this, self.new_target];
    alloc_scope.push_roots(&roots)?;
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
      None,
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
    if let Some(realm) = self.vm.current_realm() {
      alloc_scope
        .heap_mut()
        .set_function_job_realm(func_obj, realm)?;
    }
    alloc_scope
      .heap_mut()
      .set_function_bound_this(func_obj, self.this)?;
    alloc_scope
      .heap_mut()
      .set_function_bound_new_target(func_obj, self.new_target)?;
    self.apply_function_flavor(&mut alloc_scope, func_obj, flavor)?;
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
    // `parse-js` stores a canonical decimal string (no trailing `n`).
    let b = JsBigInt::from_decimal_str(&expr.value)
      .ok_or(VmError::Unimplemented("malformed BigInt literal"))?;
    Ok(Value::BigInt(b))
  }

  fn eval_lit_bool(&self, expr: &LitBoolExpr) -> Result<Value, VmError> {
    Ok(Value::Bool(expr.value))
  }

  /// RegularExpressionLiteral → `RegExpCreate` via `%RegExp%` (§13.2.7 / §22.2.3.1).
  fn eval_lit_regex(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &LitRegexExpr,
  ) -> Result<Value, VmError> {
    // `value` includes delimiters and flags, e.g. `/[a-z]/i`.
    let raw = expr.value.as_str();
    let Some(body) = raw.strip_prefix('/') else {
      return Err(VmError::Unimplemented("malformed RegExp literal"));
    };
    let Some(last_slash) = body.rfind('/') else {
      return Err(VmError::Unimplemented("malformed RegExp literal"));
    };
    let pattern = &body[..last_slash];
    let flags = &body[last_slash + 1..];
    let mut s = scope.reborrow();
    let pattern_s = s.alloc_string(pattern)?;
    s.push_root(Value::String(pattern_s))?;
    let flags_s = s.alloc_string(flags)?;
    s.push_root(Value::String(flags_s))?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    let ctor = Value::Object(intr.regexp_constructor());
    s.push_root(ctor)?;
    self.call(
      &mut s,
      ctor,
      Value::Undefined,
      &[Value::String(pattern_s), Value::String(flags_s)],
    )
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
          units.try_reserve(len).map_err(|_| VmError::OutOfMemory)?;
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

  fn eval_tagged_template(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &TaggedTemplateExpr,
  ) -> Result<Value, VmError> {
    // Compute `callee` and `this` similarly to `CallExpression` evaluation.
    let (callee_value, this_value) = match &*expr.function.stx {
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
          base: Value::Object(object),
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
          return Err(VmError::Unimplemented(
            "computed member access on non-object",
          ));
        };

        // Root `object` across key evaluation + `ToPropertyKey`, which may allocate and trigger GC.
        let mut key_scope = scope.reborrow();
        key_scope.push_root(Value::Object(object))?;
        let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
        key_scope.push_root(member_value)?;
        let key = self.to_property_key_operator(&mut key_scope, member_value)?;
        let reference = Reference::Property {
          base: Value::Object(object),
          key,
        };
        let callee_value = self.get_value_from_reference(&mut key_scope, &reference)?;
        (callee_value, Value::Object(object))
      }
      Expr::Member(_) | Expr::ComputedMember(_) | Expr::Id(_) | Expr::IdPat(_) => {
        let reference = self.eval_reference(scope, &expr.function)?;
        let this_value = match reference {
          // Method-call `this` is the reference base (object or primitive).
          Reference::Property { base, .. } => base,
          _ => Value::Undefined,
        };

        let mut callee_scope = scope.reborrow();
        self.root_reference(&mut callee_scope, &reference)?;
        let callee_value = self.get_value_from_reference(&mut callee_scope, &reference)?;
        (callee_value, this_value)
      }
      _ => {
        let callee_value = self.eval_expr(scope, &expr.function)?;
        (callee_value, Value::Undefined)
      }
    };

    // Root callee/this/args for the duration of the call.
    let mut call_scope = scope.reborrow();
    call_scope.push_roots(&[callee_value, this_value])?;

    let template_obj = self.create_template_object(&mut call_scope, &expr.parts)?;
    call_scope.push_root(Value::Object(template_obj))?;

    let mut args: Vec<Value> = Vec::new();
    let subst_count = expr
      .parts
      .iter()
      .filter(|p| matches!(p, LitTemplatePart::Substitution(_)))
      .count();
    args
      .try_reserve_exact(subst_count + 1)
      .map_err(|_| VmError::OutOfMemory)?;
    args.push(Value::Object(template_obj));

    // Evaluate substitutions left-to-right.
    for part in &expr.parts {
      let LitTemplatePart::Substitution(sub_expr) = part else {
        continue;
      };
      let value = self.eval_expr(&mut call_scope, sub_expr)?;
      call_scope.push_root(value)?;
      args.push(value);
    }

    self.call(&mut call_scope, callee_value, this_value, &args)
  }

  fn create_template_object(
    &mut self,
    scope: &mut Scope<'_>,
    parts: &[LitTemplatePart],
  ) -> Result<GcObject, VmError> {
    let seg_count = parts
      .iter()
      .filter(|p| matches!(p, LitTemplatePart::String(_)))
      .count();

    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;

    let cooked = scope.alloc_array(seg_count)?;
    scope.push_root(Value::Object(cooked))?;
    scope
      .heap_mut()
      .object_set_prototype(cooked, Some(intr.array_prototype()))?;

    let raw = scope.alloc_array(seg_count)?;
    scope.push_root(Value::Object(raw))?;
    scope
      .heap_mut()
      .object_set_prototype(raw, Some(intr.array_prototype()))?;

    let mut idx: u32 = 0;
    for part in parts {
      let LitTemplatePart::String(s) = part else {
        continue;
      };

      let mut elem_scope = scope.reborrow();
      let cooked_s = elem_scope.alloc_string(s)?;
      elem_scope.push_root(Value::String(cooked_s))?;
      let key_s = elem_scope.alloc_string(&idx.to_string())?;
      elem_scope.push_root(Value::String(key_s))?;
      let key = PropertyKey::from_string(key_s);

      let ok = elem_scope.create_data_property(cooked, key, Value::String(cooked_s))?;
      if !ok {
        return Err(VmError::Unimplemented("CreateDataProperty returned false"));
      }
      let ok = elem_scope.create_data_property(raw, key, Value::String(cooked_s))?;
      if !ok {
        return Err(VmError::Unimplemented("CreateDataProperty returned false"));
      }

      idx = idx.saturating_add(1);
    }

    let raw_key_s = scope.alloc_string("raw")?;
    scope.push_root(Value::String(raw_key_s))?;
    scope.define_property(
      cooked,
      PropertyKey::from_string(raw_key_s),
      PropertyDescriptor {
        enumerable: false,
        configurable: false,
        kind: PropertyKind::Data {
          value: Value::Object(raw),
          writable: false,
        },
      },
    )?;

    Ok(cooked)
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

          let mut iter = iterator::get_iterator(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
            &mut spread_scope,
            spread_value,
          )?;
          spread_scope.push_roots(&[iter.iterator, iter.next_method])?;

          while let Some(value) = iterator::iterator_step_value(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
            &mut spread_scope,
            &mut iter,
          )? {
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
      self.apply_lit_obj_member(&mut obj_scope, obj, &member.stx.typ)?;
    }

    Ok(Value::Object(obj))
  }

  /// Applies a single object-literal member onto `obj` (shared by recursive and resumable paths).
  fn apply_lit_obj_member(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    member: &ObjMemberType,
  ) -> Result<(), VmError> {
    let mut member_scope = scope.reborrow();
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
            self.to_property_key_operator(&mut member_scope, value)?
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
            let rel_end = func_node
              .loc
              .end_u32()
              .saturating_sub(self.env.prefix_len());
            let span_start = self.env.base_offset().saturating_add(rel_start);
            let span_end = self.env.base_offset().saturating_add(rel_end);
            let code = self.vm.register_ecma_function(
              self.env.source(),
              span_start,
              span_end,
              EcmaFunctionKind::ObjectMember,
              func_node,
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
              None,
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
            if let Some(realm) = self.vm.current_realm() {
              member_scope
                .heap_mut()
                .set_function_job_realm(func_obj, realm)?;
            }
            if func_node.stx.arrow {
              member_scope
                .heap_mut()
                .set_function_bound_this(func_obj, self.this)?;
              member_scope
                .heap_mut()
                .set_function_bound_new_target(func_obj, self.new_target)?;
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
            let rel_end = func_node
              .loc
              .end_u32()
              .saturating_sub(self.env.prefix_len());
            let span_start = self.env.base_offset().saturating_add(rel_start);
            let span_end = self.env.base_offset().saturating_add(rel_end);
            let code = self.vm.register_ecma_function(
              self.env.source(),
              span_start,
              span_end,
              EcmaFunctionKind::ObjectMember,
              func_node,
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
              None,
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
            if let Some(realm) = self.vm.current_realm() {
              member_scope
                .heap_mut()
                .set_function_job_realm(func_obj, realm)?;
            }
            if func_node.stx.arrow {
              member_scope
                .heap_mut()
                .set_function_bound_this(func_obj, self.this)?;
              member_scope
                .heap_mut()
                .set_function_bound_new_target(func_obj, self.new_target)?;
            }
            member_scope.push_root(Value::Object(func_obj))?;
            crate::function_properties::set_function_name(
              &mut member_scope,
              func_obj,
              key,
              Some("get"),
            )?;

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
            let rel_end = func_node
              .loc
              .end_u32()
              .saturating_sub(self.env.prefix_len());
            let span_start = self.env.base_offset().saturating_add(rel_start);
            let span_end = self.env.base_offset().saturating_add(rel_end);
            let code = self.vm.register_ecma_function(
              self.env.source(),
              span_start,
              span_end,
              EcmaFunctionKind::ObjectMember,
              func_node,
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
              None,
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
            if let Some(realm) = self.vm.current_realm() {
              member_scope
                .heap_mut()
                .set_function_job_realm(func_obj, realm)?;
            }
            if func_node.stx.arrow {
              member_scope
                .heap_mut()
                .set_function_bound_this(func_obj, self.this)?;
              member_scope
                .heap_mut()
                .set_function_bound_new_target(func_obj, self.new_target)?;
            }
            member_scope.push_root(Value::Object(func_obj))?;
            crate::function_properties::set_function_name(
              &mut member_scope,
              func_obj,
              key,
              Some("set"),
            )?;

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
          Value::Undefined | Value::Null => return Ok(()),
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

          let value = key_scope.ordinary_get_with_host_and_hooks(
            self.vm,
            &mut *self.host,
            &mut *self.hooks,
            src_obj,
            key,
            Value::Object(src_obj),
          )?;
          key_scope.push_root(value)?;
          let ok = key_scope.create_data_property(obj, key, value)?;
          if !ok {
            return Err(VmError::Unimplemented("CreateDataProperty returned false"));
          }
        }
      }
    }
    Ok(())
  }

  fn eval_id(&mut self, scope: &mut Scope<'_>, expr: &IdExpr) -> Result<Value, VmError> {
    match self.env.get(
      self.vm,
      &mut *self.host,
      &mut *self.hooks,
      scope,
      &expr.name,
    )? {
      Some(v) => Ok(v),
      None => {
        let msg = format!("{name} is not defined", name = expr.name);
        Err(throw_reference_error(self.vm, scope, &msg)?)
      }
    }
  }

  fn eval_id_pat(&mut self, scope: &mut Scope<'_>, expr: &IdPat) -> Result<Value, VmError> {
    match self.env.get(
      self.vm,
      &mut *self.host,
      &mut *self.hooks,
      scope,
      &expr.name,
    )? {
      Some(v) => Ok(v),
      None => {
        let msg = format!("{name} is not defined", name = expr.name);
        Err(throw_reference_error(self.vm, scope, &msg)?)
      }
    }
  }

  /// RelationalExpression: `PrivateIdentifier in ShiftExpression` (ECMA-262 §13.10.1).
  fn eval_private_in(
    &mut self,
    scope: &mut Scope<'_>,
    private_name: &str,
    right: Value,
  ) -> Result<Value, VmError> {
    let mut s = scope.reborrow();
    s.push_root(right)?;
    let Value::Object(obj) = right else {
      return Err(throw_type_error(
        self.vm,
        &mut s,
        "Right-hand side of 'in' should be an object",
      )?);
    };
    s.push_root(Value::Object(obj))?;
    let name_sym = self.resolve_private_name_symbol(&mut s, private_name)?;
    s.push_root(Value::Symbol(name_sym))?;
    Ok(Value::Bool(
      s.heap().object_has_private_element(obj, name_sym)?,
    ))
  }

  fn resolve_private_name_symbol(
    &mut self,
    scope: &mut Scope<'_>,
    name: &str,
  ) -> Result<crate::GcSymbol, VmError> {
    let Some(env) =
      self
        .env
        .resolve_lexical_binding(self.vm, &mut *self.host, &mut *self.hooks, scope, name)?
    else {
      return Err(throw_reference_error(
        self.vm,
        scope,
        &format!("{name} is not defined"),
      )?);
    };
    match scope.heap().env_get_binding_value(env, name, true)? {
      Value::Symbol(s) => Ok(s),
      _ => Err(VmError::InvariantViolation(
        "private name binding is not a symbol",
      )),
    }
  }

  fn eval_unary(&mut self, scope: &mut Scope<'_>, expr: &UnaryExpr) -> Result<Value, VmError> {
    match expr.operator {
      OperatorName::PrefixIncrement => self.eval_update_expression(scope, &expr.argument, 1, true),
      OperatorName::PrefixDecrement => self.eval_update_expression(scope, &expr.argument, -1, true),
      OperatorName::PostfixIncrement => {
        self.eval_update_expression(scope, &expr.argument, 1, false)
      }
      OperatorName::PostfixDecrement => {
        self.eval_update_expression(scope, &expr.argument, -1, false)
      }
      OperatorName::Delete => match &*expr.argument.stx {
        Expr::Id(id) => {
          if self.strict {
            return Err(throw_type_error(
              self.vm,
              scope,
              "Delete of an unqualified identifier in strict mode.",
            )?);
          }

          // Sloppy-mode: deleting an unqualified identifier returns `true` if the reference is
          // unresolvable, otherwise it performs a global-object property delete. Lexical bindings
          // are not deletable.
          if self
            .env
            .resolve_lexical_binding(self.vm, self.host, self.hooks, scope, &id.stx.name)?
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
            return Err(throw_type_error(
              self.vm,
              scope,
              "Delete of an unqualified identifier in strict mode.",
            )?);
          }

          if self
            .env
            .resolve_lexical_binding(self.vm, self.host, self.hooks, scope, &id.stx.name)?
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
        // `delete <OptionalExpression>` short-circuits: if the chain is nullish it yields `true`
        // without deleting anything (ECMA-262 §13.5.1.2 / §13.3.9 — `delete a?.b` is `true` when
        // `a` is nullish).
        Expr::Member(_) | Expr::ComputedMember(_) if contains_optional_link(&expr.argument) => {
          match self.eval_chain_delete(scope, &expr.argument)? {
            None => Ok(Value::Bool(true)),
            Some((object, key)) => Ok(Value::Bool(scope.ordinary_delete(object, key)?)),
          }
        }
        Expr::Member(_) | Expr::ComputedMember(_) => {
          let reference = self.eval_reference(scope, &expr.argument)?;
          match reference {
            Reference::Property { base, key } => {
              let Value::Object(object) = base else {
                // `delete` on a primitive property reference: ToObject then OrdinaryDelete.
                // Temporary wrappers have no own props for typical keys → success/`true`.
                return Ok(Value::Bool(true));
              };
              let ok = scope.ordinary_delete(object, key)?;
              if !ok && self.strict {
                return Err(throw_type_error(
                  self.vm,
                  scope,
                  "Cannot delete non-configurable property",
                )?);
              }
              Ok(Value::Bool(ok))
            }
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
      OperatorName::BitwiseNot => {
        // ECMA-262 §13.5.6: ToNumeric, then Number::bitwiseNOT (`-x-1` on ToInt32)
        // or BigInt::bitwiseNOT (`-x-1`).
        let argument = self.eval_expr(scope, &expr.argument)?;
        let mut arg_scope = scope.reborrow();
        arg_scope.push_root(argument)?;
        Ok(match self.to_numeric(&mut arg_scope, argument)? {
          NumericValue::Number(n) => Value::Number(!number_to_int32(n) as f64),
          NumericValue::BigInt(b) => {
            let neg_one = JsBigInt::from_u128(1).negate();
            let out = b
              .negate()
              .checked_add(neg_one)
              .ok_or(VmError::OutOfMemory)?;
            Value::BigInt(out)
          }
        })
      }
      OperatorName::Typeof => {
        let argument = match &*expr.argument.stx {
          Expr::Id(id) => {
            // Preserve the `typeof` special-case: unresolvable identifiers yield `"undefined"`
            // instead of throwing a ReferenceError.
            self.tick()?;
            self
              .env
              .get(
                self.vm,
                &mut *self.host,
                &mut *self.hooks,
                scope,
                &id.stx.name,
              )?
              .unwrap_or(Value::Undefined)
          }
          Expr::IdPat(id) => {
            self.tick()?;
            self
              .env
              .get(
                self.vm,
                &mut *self.host,
                &mut *self.hooks,
                scope,
                &id.stx.name,
              )?
              .unwrap_or(Value::Undefined)
          }
          _ => self.eval_expr(scope, &expr.argument)?,
        };
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

              let mut iter = iterator::get_iterator(
                self.vm,
                &mut *self.host,
                &mut *self.hooks,
                &mut new_scope,
                spread_value,
              )?;
              new_scope.push_root(iter.iterator)?;
              new_scope.push_root(iter.next_method)?;

              while let Some(value) = iterator::iterator_step_value(
                self.vm,
                &mut *self.host,
                &mut *self.hooks,
                &mut new_scope,
                &mut iter,
              )? {
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
        match self.construct(&mut new_scope, callee, &args, callee) {
          Ok(v) => Ok(v),
          Err(VmError::NotConstructable) => Err(throw_type_error(
            self.vm,
            &mut new_scope,
            "Value is not a constructor",
          )?),
          Err(err) => Err(err),
        }
      }
      _ => Err(VmError::Unimplemented("unary operator")),
    }
  }

  fn eval_unary_postfix(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &UnaryPostfixExpr,
  ) -> Result<Value, VmError> {
    match expr.operator {
      OperatorName::PostfixIncrement => {
        self.eval_update_expression(scope, &expr.argument, 1, false)
      }
      OperatorName::PostfixDecrement => {
        self.eval_update_expression(scope, &expr.argument, -1, false)
      }
      _ => Err(VmError::Unimplemented("postfix unary operator")),
    }
  }

  fn eval_update_expression(
    &mut self,
    scope: &mut Scope<'_>,
    argument: &Node<Expr>,
    delta: i8,
    prefix: bool,
  ) -> Result<Value, VmError> {
    let reference = self.eval_reference(scope, argument)?;
    let mut update_scope = scope.reborrow();
    self.root_reference(&mut update_scope, &reference)?;

    let old_value = self.get_value_from_reference(&mut update_scope, &reference)?;
    update_scope.push_root(old_value)?;

    let old_numeric = self.to_numeric(&mut update_scope, old_value)?;
    let delta_bigint = if delta >= 0 {
      JsBigInt::from_u128(delta as u128)
    } else {
      JsBigInt::from_u128((-delta) as u128).negate()
    };

    let (old_out, new_value) = match old_numeric {
      NumericValue::Number(n) => {
        let new_n = n + f64::from(delta);
        (Value::Number(n), Value::Number(new_n))
      }
      NumericValue::BigInt(b) => {
        let Some(out) = b.checked_add(delta_bigint) else {
          return Err(VmError::Unimplemented(
            "BigInt increment/decrement overflow",
          ));
        };
        (Value::BigInt(b), Value::BigInt(out))
      }
    };

    update_scope.push_root(new_value)?;
    self.put_value_to_reference(&mut update_scope, &reference, new_value)?;
    if prefix {
      Ok(new_value)
    } else {
      Ok(old_out)
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
        Expr::Super(_) => return self.eval_super_call(scope, expr),
        _ => {}
      }
    } else if matches!(&*expr.callee.stx, Expr::Super(_)) {
      // `super?.(...)` — SuperCall then optional-chain short-circuit on a nullish result.
      let value = self.eval_super_call(scope, expr)?;
      if is_nullish(value) {
        return Ok(Value::Undefined);
      }
      return Ok(value);
    }

    // Evaluate the callee and compute the `this` value for the call.
    //
    // A `MemberExpression`/`CallExpression` callee that is part of a `?.` chain never reaches here
    // — `eval_expr` routes whole optional chains to `eval_optional_chain`. What *can* reach here is
    // a parenthesized optional member callee such as `(a?.b)()`, where the short-circuit does not
    // propagate out of the parentheses (§13.3.9): if `a?.b` is nullish the callee is simply
    // `undefined` and the call throws "not callable" (handled by `call_with_host_and_hooks`).
    let (callee_value, this_value) = match &*expr.callee.stx {
      Expr::Member(member) if matches!(&*member.stx.left.stx, Expr::Super(_)) => {
        let key_s = scope.alloc_string(&member.stx.right)?;
        let key = PropertyKey::from_string(key_s);
        self.eval_super_property(scope, key)?
      }
      Expr::ComputedMember(member) if matches!(&*member.stx.object.stx, Expr::Super(_)) => {
        let member_value = self.eval_expr(scope, &member.stx.member)?;
        scope.push_root(member_value)?;
        let key = self.to_property_key_operator(scope, member_value)?;
        self.eval_super_property(scope, key)?
      }
      Expr::Member(member) => {
        let base = self.eval_expr(scope, &member.stx.left)?;
        if member.stx.optional_chaining && is_nullish(base) {
          (Value::Undefined, Value::Undefined)
        } else {
          let mut key_scope = scope.reborrow();
          key_scope.push_root(base)?;
          let key_s = key_scope.alloc_string(&member.stx.right)?;
          let key = PropertyKey::from_string(key_s);
          // `this` binds to the base value itself, which may be a primitive (§13.3.3): method calls
          // on primitives (e.g. `"abc".charAt(1)`) pass the primitive as the receiver.
          let callee_value = self.get_v(&mut key_scope, base, key)?;
          (callee_value, base)
        }
      }
      Expr::ComputedMember(member) => {
        let base = self.eval_expr(scope, &member.stx.object)?;
        if member.stx.optional_chaining && is_nullish(base) {
          (Value::Undefined, Value::Undefined)
        } else {
          let mut key_scope = scope.reborrow();
          key_scope.push_root(base)?;
          let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
          key_scope.push_root(member_value)?;
          let key = self.to_property_key_operator(&mut key_scope, member_value)?;
          let callee_value = self.get_v(&mut key_scope, base, key)?;
          (callee_value, base)
        }
      }
      Expr::Id(_) | Expr::IdPat(_) => {
        let reference = self.eval_reference(scope, &expr.callee)?;
        let mut callee_scope = scope.reborrow();
        self.root_reference(&mut callee_scope, &reference)?;
        let callee_value = self.get_value_from_reference(&mut callee_scope, &reference)?;
        (callee_value, Value::Undefined)
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

    self.eval_call_with_callee(scope, expr, callee_value, this_value)
  }

  /// GetThisBinding — throws ReferenceError when `this` is uninitialized (derived ctor pre-`super`).
  fn get_this_binding(&mut self, scope: &mut Scope<'_>) -> Result<Value, VmError> {
    if self.this_uninitialized {
      return Err(throw_reference_error(
        self.vm,
        scope,
        "Must call super constructor in derived class before accessing 'this'",
      )?);
    }
    Ok(self.this)
  }

  /// SuperCall evaluation (ECMA-262 §13.3.7.1): Construct(GetSuperConstructor(), args, newTarget)
  /// then BindThisValue.
  fn eval_super_call(&mut self, scope: &mut Scope<'_>, expr: &CallExpr) -> Result<Value, VmError> {
    let active = self
      .active_function
      .ok_or(VmError::Unimplemented("super() outside of function"))?;
    scope.push_root(Value::Object(active))?;

    if matches!(self.new_target, Value::Undefined) {
      return Err(throw_reference_error(
        self.vm,
        scope,
        "super() is only valid in a derived class constructor",
      )?);
    }

    // GetSuperConstructor: activeFunction.[[GetPrototypeOf]]().
    let super_ctor = match scope.heap().object_prototype(active)? {
      Some(o) => o,
      None => {
        return Err(throw_type_error(
          self.vm,
          scope,
          "Super constructor is nullish",
        )?);
      }
    };
    if !scope.heap().is_constructor(Value::Object(super_ctor))? {
      return Err(throw_type_error(
        self.vm,
        scope,
        "Super expression must evaluate to a constructor",
      )?);
    }
    scope.push_root(Value::Object(super_ctor))?;

    let mut call_scope = scope.reborrow();
    let mut args: Vec<Value> = Vec::new();
    args
      .try_reserve_exact(expr.arguments.len())
      .map_err(|_| VmError::OutOfMemory)?;
    for arg in &expr.arguments {
      if arg.stx.spread {
        let spread_value = self.eval_expr(&mut call_scope, &arg.stx.value)?;
        call_scope.push_root(spread_value)?;
        let mut iter = iterator::get_iterator(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut call_scope,
          spread_value,
        )?;
        call_scope.push_roots(&[iter.iterator, iter.next_method])?;
        while let Some(value) = iterator::iterator_step_value(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut call_scope,
          &mut iter,
        )? {
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

    let result = self.construct(
      &mut call_scope,
      Value::Object(super_ctor),
      &args,
      self.new_target,
    )?;
    // BindThisValue
    self.this = result;
    self.this_uninitialized = false;
    // InitializeInstanceElements(this, activeFunction) after super() in derived constructors.
    if let Value::Object(this_obj) = result {
      call_scope.push_root(Value::Object(this_obj))?;
      call_scope.push_root(Value::Object(active))?;
      call_scope
        .heap_mut()
        .initialize_instance_private_elements(this_obj, active)?;
    }
    Ok(result)
  }

  /// SuperProperty get: `[[Get]](GetSuperBase(), key)` with receiver = GetThisBinding().
  /// Returns `(property_value, this_binding)` so call sites can bind `this` to the instance.
  fn eval_super_property(
    &mut self,
    scope: &mut Scope<'_>,
    key: PropertyKey,
  ) -> Result<(Value, Value), VmError> {
    let actual_this = self.get_this_binding(scope)?;
    scope.push_root(actual_this)?;
    match key {
      PropertyKey::String(s) => scope.push_root(Value::String(s))?,
      PropertyKey::Symbol(s) => scope.push_root(Value::Symbol(s))?,
    };

    let active = self
      .active_function
      .ok_or(VmError::Unimplemented("super property outside of method"))?;
    scope.push_root(Value::Object(active))?;
    let home = match scope.heap().get_function_home_object(active)? {
      Some(h) => h,
      None => {
        return Err(throw_type_error(
          self.vm,
          scope,
          "super property used in a non-method",
        )?);
      }
    };
    scope.push_root(Value::Object(home))?;

    // GetSuperBase = home.[[GetPrototypeOf]]()
    let base_obj = match scope.heap().object_prototype(home)? {
      Some(o) => o,
      None => {
        return Err(throw_type_error(
          self.vm,
          scope,
          "Cannot read super property of null",
        )?);
      }
    };
    scope.push_root(Value::Object(base_obj))?;

    let mut get_scope = scope.reborrow();
    get_scope.push_root(actual_this)?;
    get_scope.push_root(Value::Object(base_obj))?;
    match key {
      PropertyKey::String(s) => get_scope.push_root(Value::String(s))?,
      PropertyKey::Symbol(s) => get_scope.push_root(Value::Symbol(s))?,
    };
    let value = get_scope.ordinary_get_with_host_and_hooks(
      self.vm,
      &mut *self.host,
      &mut *self.hooks,
      base_obj,
      key,
      actual_this,
    )?;
    Ok((value, actual_this))
  }

  /// Evaluates a call's argument list (left-to-right, including spreads) and performs the call with
  /// the already-computed `callee` and `this`. Shared by `eval_call` and optional-chain evaluation.
  fn eval_call_with_callee(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &CallExpr,
    callee_value: Value,
    this_value: Value,
  ) -> Result<Value, VmError> {
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

        let mut iter = iterator::get_iterator(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut call_scope,
          spread_value,
        )?;
        call_scope.push_roots(&[iter.iterator, iter.next_method])?;

        while let Some(value) = iterator::iterator_step_value(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut call_scope,
          &mut iter,
        )? {
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

    // Global `%eval%` (including `eval?.(...)` and `otherGlobal.eval(...)`): PerformEval with
    // direct=false. Identifier `eval(...)` is handled earlier as direct eval and never reaches here.
    // Cross-realm: match any registered realm's `%eval%` and run in that realm.
    if let Value::Object(obj) = callee_value {
      if let Some((global, lex, intr, _)) = self.vm.realm_for_eval_intrinsic(obj) {
        let arg0 = args.first().copied().unwrap_or(Value::Undefined);
        return match arg0 {
          Value::String(s) => {
            self.eval_perform_eval_string(&mut call_scope, s, false, Some((global, lex, intr)))
          }
          other => Ok(other),
        };
      }
    }

    match self.vm.call_with_host_and_hooks(
      &mut *self.host,
      &mut call_scope,
      &mut *self.hooks,
      callee_value,
      this_value,
      &args,
    ) {
      Err(VmError::NotCallable) => Err(throw_type_error(
        self.vm,
        &mut call_scope,
        "value is not callable",
      )?),
      other => other,
    }
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

        let mut iter = iterator::get_iterator(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut call_scope,
          spread_value,
        )?;
        call_scope.push_roots(&[iter.iterator, iter.next_method])?;

        while let Some(value) = iterator::iterator_step_value(
          self.vm,
          &mut *self.host,
          &mut *self.hooks,
          &mut call_scope,
          &mut iter,
        )? {
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
      Value::String(s) => self.eval_perform_eval_string(&mut call_scope, s, true, None),
      other => Ok(other),
    }
  }

  /// `PerformEval` (§19.2.1.1): `direct` selects the caller's lexical env vs the realm global env.
  ///
  /// `foreign_realm` (when set) switches the active intrinsics / global object for the duration of
  /// the eval — used by `otherGlobal.eval(...)` after `$262.createRealm()`.
  fn eval_perform_eval_string(
    &mut self,
    scope: &mut Scope<'_>,
    source_string: GcString,
    direct: bool,
    foreign_realm: Option<(GcObject, GcEnv, crate::Intrinsics)>,
  ) -> Result<Value, VmError> {
    let source = scope.heap().get_string(source_string)?.to_utf8_lossy();

    let source = Arc::new(SourceText::new("<eval>", source));
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };
    // Eval parse failures are runtime `SyntaxError` throws (catchable), not host
    // `VmError::Syntax` that aborts the caller as a parse-phase failure
    // (test262 `break/S12.8_A7`, `continue/S12.7_A7`).
    let top = match parse_with_options(&source.text, opts) {
      Ok(top) => top,
      Err(err) => {
        return Err(throw_syntax_error(self.vm, scope, &err.to_string())?);
      }
    };
    // Indirect eval ignores the caller's strictness for the *callerRealm* strictCaller
    // flag; only the eval script's own `"use strict"` applies.
    let strict = if direct {
      self.strict || detect_use_strict_directive(&top.stx.body)
    } else {
      detect_use_strict_directive(&top.stx.body)
    };
    let program = Arc::new(ParsedProgram { top });

    // Save and restore the runtime's source and lexical environment while running eval code. This
    // keeps nested function source spans aligned with the eval input.
    let prev_source = self.env.source();
    let prev_base_offset = self.env.base_offset();
    let prev_prefix_len = self.env.prefix_len();
    let prev_lexical_env = self.env.lexical_env;
    let prev_var_env = self.env.var_env;
    let prev_strict = self.strict;
    let prev_global = self.env.global_object();
    let prev_global_lex = self.env.global_lexical_env();
    let prev_this = self.this;
    let prev_intrinsics = self.vm.intrinsics();

    if let Some((global, lex, intr)) = foreign_realm {
      // Cross-realm indirect eval must not be "direct".
      debug_assert!(!direct);
      self.env.set_realm_globals(global, lex);
      self.vm.set_intrinsics(intr);
      self.this = Value::Object(global);
    }

    self.env.set_source_info(source.clone(), 0, 0);
    let outer_lex = if direct {
      prev_lexical_env
    } else {
      self.env.global_lexical_env()
    };
    let eval_lex = scope.env_create(Some(outer_lex))?;
    self.env.set_lexical_env(scope.heap_mut(), eval_lex);
    if !direct {
      // Indirect eval var bindings go on the global object (§19.2.1.1 / §9.1.1.4).
      self.env.var_env = VarEnv::GlobalObject;
    }
    self.strict = strict;
    self.vm.push_program(program.clone());

    let result = (|| {
      // EvalDeclarationInstantiation (§19.2.1.3) step 5: in sloppy direct eval, var names
      // must not collide with lexical bindings on the chain from lexEnv down to (but not
      // including) varEnv — catches `let x; eval('var x')` and `a = eval('var a')` defaults.
      if direct && !strict {
        let mut var_names = HashSet::<String>::new();
        for stmt in &program.top.stx.body {
          self.collect_var_names(&stmt.stx, &mut var_names)?;
        }
        if !var_names.is_empty() {
          let var_env_id = match self.env.var_env {
            VarEnv::Env(e) => Some(e),
            VarEnv::GlobalObject => None,
          };
          let mut this_lex = Some(eval_lex);
          while let Some(env) = this_lex {
            if var_env_id == Some(env) {
              break;
            }
            // Object Environment Records (with) are skipped by the spec.
            if matches!(
              scope.heap().env_record_kind(env)?,
              crate::env::EnvRecordKind::Declarative
            ) {
              for name in &var_names {
                if scope.heap().env_has_binding(env, name)? {
                  return Err(throw_syntax_error(
                    self.vm,
                    scope,
                    &format!("Identifier '{name}' has already been declared"),
                  )?);
                }
              }
            }
            this_lex = scope.heap().env_outer(env)?;
          }
        }
      }

      self.instantiate_script(scope, &program.top.stx.body)?;

      let completion = self.eval_stmt_list(scope, &program.top.stx.body)?;
      match completion {
        Completion::Normal(v) => Ok(v.unwrap_or(Value::Undefined)),
        Completion::Throw(thrown) => Err(VmError::ThrowWithStack {
          value: thrown.value,
          stack: thrown.stack,
        }),
        Completion::Return(_) => Err(VmError::Unimplemented("return in eval")),
        Completion::Break(..) => Err(VmError::Unimplemented("break in eval")),
        Completion::Continue(..) => Err(VmError::Unimplemented("continue in eval")),
      }
    })();

    self.vm.pop_program();
    self.strict = prev_strict;
    self.env.var_env = prev_var_env;
    self.env.set_lexical_env(scope.heap_mut(), prev_lexical_env);
    self
      .env
      .set_source_info(prev_source, prev_base_offset, prev_prefix_len);
    // Cross-realm indirect eval must restore the caller's realm globals/intrinsics/`this`.
    if foreign_realm.is_some() {
      self.env.set_realm_globals(prev_global, prev_global_lex);
      self.this = prev_this;
      if let Some(intr) = prev_intrinsics {
        self.vm.set_intrinsics(intr);
      }
    }

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

  fn assignment_to_binary_op(op: OperatorName) -> Option<OperatorName> {
    Some(match op {
      OperatorName::AssignmentAddition => OperatorName::Addition,
      OperatorName::AssignmentSubtraction => OperatorName::Subtraction,
      OperatorName::AssignmentMultiplication => OperatorName::Multiplication,
      OperatorName::AssignmentDivision => OperatorName::Division,
      OperatorName::AssignmentRemainder => OperatorName::Remainder,
      OperatorName::AssignmentExponentiation => OperatorName::Exponentiation,
      OperatorName::AssignmentBitwiseAnd => OperatorName::BitwiseAnd,
      OperatorName::AssignmentBitwiseOr => OperatorName::BitwiseOr,
      OperatorName::AssignmentBitwiseXor => OperatorName::BitwiseXor,
      OperatorName::AssignmentBitwiseLeftShift => OperatorName::BitwiseLeftShift,
      OperatorName::AssignmentBitwiseRightShift => OperatorName::BitwiseRightShift,
      OperatorName::AssignmentBitwiseUnsignedRightShift => OperatorName::BitwiseUnsignedRightShift,
      _ => return None,
    })
  }

  fn eval_compound_assignment(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &BinaryExpr,
  ) -> Result<Value, VmError> {
    let Some(bin_op) = Self::assignment_to_binary_op(expr.operator) else {
      return Err(VmError::Unimplemented("compound assignment operator"));
    };
    if matches!(&*expr.left.stx, Expr::ObjPat(_) | Expr::ArrPat(_)) {
      return Err(VmError::Unimplemented(
        "compound assignment to destructuring patterns",
      ));
    }
    let reference = self.eval_reference(scope, &expr.left)?;
    let mut op_scope = scope.reborrow();
    self.root_reference(&mut op_scope, &reference)?;

    let left = self.get_value_from_reference(&mut op_scope, &reference)?;
    op_scope.push_root(left)?;
    let right = self.eval_expr(&mut op_scope, &expr.right)?;
    op_scope.push_root(right)?;

    let value = if bin_op == OperatorName::Addition {
      self.addition_operator(&mut op_scope, left, right)?
    } else {
      self.apply_numeric_binary(&mut op_scope, bin_op, left, right)?
    };
    op_scope.push_root(value)?;
    self.put_value_to_reference(&mut op_scope, &reference, value)?;
    Ok(value)
  }

  fn eval_logical_assignment(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &BinaryExpr,
  ) -> Result<Value, VmError> {
    if matches!(&*expr.left.stx, Expr::ObjPat(_) | Expr::ArrPat(_)) {
      return Err(VmError::Unimplemented(
        "logical assignment to destructuring patterns",
      ));
    }
    let reference = self.eval_reference(scope, &expr.left)?;
    let mut op_scope = scope.reborrow();
    self.root_reference(&mut op_scope, &reference)?;
    let left = self.get_value_from_reference(&mut op_scope, &reference)?;
    op_scope.push_root(left)?;

    let assign = match expr.operator {
      OperatorName::AssignmentLogicalAnd => to_boolean(op_scope.heap(), left)?,
      OperatorName::AssignmentLogicalOr => !to_boolean(op_scope.heap(), left)?,
      OperatorName::AssignmentNullishCoalescing => is_nullish(left),
      _ => {
        return Err(VmError::Unimplemented("logical assignment operator"));
      }
    };
    if !assign {
      return Ok(left);
    }
    let right = self.eval_expr(&mut op_scope, &expr.right)?;
    op_scope.push_root(right)?;
    self.put_value_to_reference(&mut op_scope, &reference, right)?;
    Ok(right)
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
              &mut *self.host,
              &mut *self.hooks,
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
            // NamedEvaluation (§13.15.2 / §8.4.5): anonymous function/class/generator/
            // async forms assigned to an identifier get SetFunctionName from the LHS.
            let value = if let Reference::Binding(name) = reference {
              if is_anonymous_function_definition_node(&expr.right) {
                let name_owned = name.to_string();
                let v = if let Expr::Class(class) = &*expr.right.stx {
                  self.eval_class_expr(&mut rhs_scope, class, Some(&name_owned))?
                } else {
                  self.eval_expr(&mut rhs_scope, &expr.right)?
                };
                rhs_scope.push_root(v)?;
                if let Value::Object(func) = v {
                  if rhs_scope.heap().is_callable(v)? {
                    let name_s = rhs_scope.alloc_string(&name_owned)?;
                    crate::function_properties::set_function_name(
                      &mut rhs_scope,
                      func,
                      PropertyKey::from_string(name_s),
                      None,
                    )?;
                  }
                }
                v
              } else {
                self.eval_expr(&mut rhs_scope, &expr.right)?
              }
            } else {
              self.eval_expr(&mut rhs_scope, &expr.right)?
            };
            rhs_scope.push_root(value)?;
            self.put_value_to_reference(&mut rhs_scope, &reference, value)?;
            Ok(value)
          }
        }
      }
      // Compound assignment: `x op= y` ⇒ `x = x op y` (with a single LeftHandSide evaluation).
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
      | OperatorName::AssignmentBitwiseUnsignedRightShift => {
        self.eval_compound_assignment(scope, expr)
      }
      // Logical assignment short-circuits and does not evaluate the RHS / PutValue when the
      // LHS already determines the result (`&&=` / `||=` / `??=`).
      OperatorName::AssignmentLogicalAnd
      | OperatorName::AssignmentLogicalOr
      | OperatorName::AssignmentNullishCoalescing => self.eval_logical_assignment(scope, expr),
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
      OperatorName::Comma => {
        // ECMA-262 §13.16: evaluate the left operand for its side effects and
        // discard it (GetValue is applied but the value is not used), then
        // evaluate and return the right operand.
        let _ = self.eval_expr(scope, &expr.left)?;
        self.eval_expr(scope, &expr.right)
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
        rhs_scope.push_root(right)?;
        // §7.2.14: Object==Object is reference equality. Only when *exactly one* side is an
        // Object do we `ToPrimitive` (hint default) so wrappers' `valueOf` runs — the heap
        // `abstract_equality` stub cannot invoke methods.
        let (left, right) = match (left, right) {
          (Value::Object(_), Value::Object(_)) => (left, right),
          (Value::Object(_), _) => (
            self.to_primitive(&mut rhs_scope, left, ToPrimitiveHint::Default)?,
            right,
          ),
          (_, Value::Object(_)) => (
            left,
            self.to_primitive(&mut rhs_scope, right, ToPrimitiveHint::Default)?,
          ),
          _ => (left, right),
        };
        Ok(Value::Bool(abstract_equality(
          rhs_scope.heap_mut(),
          left,
          right,
        )?))
      }
      OperatorName::Inequality => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        rhs_scope.push_root(right)?;
        let (left, right) = match (left, right) {
          (Value::Object(_), Value::Object(_)) => (left, right),
          (Value::Object(_), _) => (
            self.to_primitive(&mut rhs_scope, left, ToPrimitiveHint::Default)?,
            right,
          ),
          (_, Value::Object(_)) => (
            left,
            self.to_primitive(&mut rhs_scope, right, ToPrimitiveHint::Default)?,
          ),
          _ => (left, right),
        };
        Ok(Value::Bool(!abstract_equality(
          rhs_scope.heap_mut(),
          left,
          right,
        )?))
      }
      OperatorName::In => {
        // `#PrivateName in ShiftExpression` — left is a PrivateIdentifier, not a value expression.
        if let Some(private_name) = private_in_identifier(expr) {
          let right = self.eval_expr(scope, &expr.right)?;
          return self.eval_private_in(scope, private_name, right);
        }
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        let Value::Object(obj) = right else {
          return Err(throw_type_error(
            self.vm,
            &mut rhs_scope,
            "Right-hand side of 'in' should be an object",
          )?);
        };

        // Root the RHS object across `ToPropertyKey`, which may allocate and trigger GC.
        rhs_scope.push_root(Value::Object(obj))?;
        let key = self.to_property_key_operator(&mut rhs_scope, left)?;
        Ok(Value::Bool(rhs_scope.ordinary_has_property(obj, key)?))
      }
      OperatorName::Instanceof => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        rhs_scope.push_root(right)?;
        Ok(Value::Bool(self.instanceof_operator(
          &mut rhs_scope,
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
      OperatorName::Multiplication
      | OperatorName::Subtraction
      | OperatorName::Division
      | OperatorName::Remainder
      | OperatorName::Exponentiation
      | OperatorName::BitwiseAnd
      | OperatorName::BitwiseOr
      | OperatorName::BitwiseXor
      | OperatorName::BitwiseLeftShift
      | OperatorName::BitwiseRightShift
      | OperatorName::BitwiseUnsignedRightShift => {
        let left = self.eval_expr(scope, &expr.left)?;
        // Root `left` across evaluation of `right` in case the RHS allocates and triggers GC.
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        self.apply_numeric_binary(&mut rhs_scope, expr.operator, left, right)
      }
      OperatorName::LessThan => {
        let left = self.eval_expr(scope, &expr.left)?;
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        // ECMA-262 §13.10.1: `x < y` is `IsLessThan(x, y, true)`; undefined → false.
        Ok(Value::Bool(
          self
            .is_less_than(&mut rhs_scope, left, right, true)?
            .unwrap_or(false),
        ))
      }
      OperatorName::GreaterThan => {
        let left = self.eval_expr(scope, &expr.left)?;
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        // ECMA-262 §13.10.1: `x > y` is `IsLessThan(y, x, false)`; undefined → false.
        Ok(Value::Bool(
          self
            .is_less_than(&mut rhs_scope, right, left, false)?
            .unwrap_or(false),
        ))
      }
      OperatorName::LessThanOrEqual => {
        let left = self.eval_expr(scope, &expr.left)?;
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        // ECMA-262 §13.10.1: `x <= y` is true unless `IsLessThan(y, x, false)` is
        // true or undefined.
        Ok(Value::Bool(
          self.is_less_than(&mut rhs_scope, right, left, false)? == Some(false),
        ))
      }
      OperatorName::GreaterThanOrEqual => {
        let left = self.eval_expr(scope, &expr.left)?;
        let mut rhs_scope = scope.reborrow();
        rhs_scope.push_root(left)?;
        let right = self.eval_expr(&mut rhs_scope, &expr.right)?;
        // ECMA-262 §13.10.1: `x >= y` is true unless `IsLessThan(x, y, true)` is
        // true or undefined.
        Ok(Value::Bool(
          self.is_less_than(&mut rhs_scope, left, right, true)? == Some(false),
        ))
      }
      _ => Err(VmError::Unimplemented("binary operator")),
    }
  }

  fn instanceof_operator(
    &mut self,
    scope: &mut Scope<'_>,
    object: Value,
    constructor: Value,
  ) -> Result<bool, VmError> {
    // Root inputs for the duration of the operation: `instanceof` may allocate when performing
    // `GetMethod`/`Get`/`Call`.
    let mut scope = scope.reborrow();
    scope.push_root(object)?;
    scope.push_root(constructor)?;

    // InstanceofOperator (ECMA-262 §13.10.2):
    // 1. If Type(target) is not Object, throw a TypeError exception.
    let Value::Object(constructor_obj) = constructor else {
      return Err(throw_type_error(
        self.vm,
        &mut scope,
        "Right-hand side of 'instanceof' is not an object",
      )?);
    };

    // 2. Let instOfHandler be ? GetMethod(target, @@hasInstance).
    let has_instance_sym = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?
      .well_known_symbols()
      .has_instance;
    let has_instance_key = PropertyKey::from_symbol(has_instance_sym);
    let method = match self
      .vm
      .get_method(&mut scope, constructor, has_instance_key)
    {
      Ok(method) => method,
      Err(VmError::TypeError(_) | VmError::NotCallable) => {
        return Err(throw_type_error(
          self.vm,
          &mut scope,
          "@@hasInstance is not callable",
        )?);
      }
      Err(err) => return Err(err),
    };

    // 3. If instOfHandler is not undefined, return ToBoolean(? Call(instOfHandler, target, « V »)).
    if let Some(method) = method {
      let result = self.call(
        &mut scope,
        method,
        Value::Object(constructor_obj),
        &[object],
      )?;
      return Ok(to_boolean(scope.heap(), result)?);
    }

    // 4. If IsCallable(target) is false, throw a TypeError exception.
    if !scope.heap().is_callable(constructor)? {
      return Err(throw_type_error(
        self.vm,
        &mut scope,
        "Right-hand side of 'instanceof' is not callable",
      )?);
    }

    // 5. Return ? OrdinaryHasInstance(target, V).
    self.ordinary_has_instance(&mut scope, object, constructor_obj)
  }

  fn ordinary_has_instance(
    &mut self,
    scope: &mut Scope<'_>,
    object: Value,
    constructor: GcObject,
  ) -> Result<bool, VmError> {
    // Bound functions delegate `instanceof` checks to their target.
    if let Ok(func) = scope.heap().get_function(constructor) {
      if let Some(bound_target) = func.bound_target {
        return self.instanceof_operator(scope, object, Value::Object(bound_target));
      }
    }

    // If the LHS is not an object, `instanceof` is `false` without further observable actions.
    let Value::Object(object) = object else {
      return Ok(false);
    };

    // P = Get(C, "prototype").
    let prototype_s = scope.alloc_string("prototype")?;
    scope.push_root(Value::String(prototype_s))?;
    let prototype = self
      .vm
      .get(scope, constructor, PropertyKey::from_string(prototype_s))?;

    let Value::Object(prototype) = prototype else {
      return Err(throw_type_error(
        self.vm,
        scope,
        "Function has non-object prototype in instanceof check",
      )?);
    };

    // Walk `object`'s prototype chain until we find `prototype` or reach the end.
    let mut current = scope.heap().object_prototype(object)?;
    let mut steps = 0usize;
    let mut visited: HashSet<GcObject> = HashSet::new();
    while let Some(obj) = current {
      if steps >= crate::MAX_PROTOTYPE_CHAIN {
        return Err(VmError::PrototypeChainTooDeep);
      }
      steps += 1;

      if !visited.insert(obj) {
        return Err(VmError::PrototypeCycle);
      }

      if obj == prototype {
        return Ok(true);
      }
      current = scope.heap().object_prototype(obj)?;
    }

    Ok(false)
  }

  fn is_primitive_value(&self, value: Value) -> bool {
    !matches!(value, Value::Object(_))
  }

  /// Whether §7.2.14 may apply `ToPrimitive` to an Object compared with `other`.
  ///
  /// Only String / Number / BigInt / Symbol / Boolean counterparts trigger conversion.
  /// `null` / `undefined` / Object do not (Object↔Object is reference equality; converting
  /// `{valueOf:()=>null} == null` would wrongly yield true).
  fn abstract_equality_needs_to_primitive(other: Value) -> bool {
    matches!(
      other,
      Value::String(_) | Value::Number(_) | Value::BigInt(_) | Value::Symbol(_) | Value::Bool(_)
    )
  }

  /// Prepare operands for Abstract Equality Comparison (§7.2.14) when the heap
  /// `abstract_equality` helper cannot invoke methods: if exactly one side is an
  /// Object and the other is a convertible primitive, convert the Object via
  /// `ToPrimitive` (hint default) so wrappers' `valueOf` / `toString` run.
  fn abstract_equality_prepare_primitives(
    &mut self,
    scope: &mut Scope<'_>,
    left: Value,
    right: Value,
  ) -> Result<(Value, Value), VmError> {
    match (left, right) {
      (Value::Object(_), Value::Object(_)) => Ok((left, right)),
      (Value::Object(_), other) if Self::abstract_equality_needs_to_primitive(other) => {
        scope.push_root(other)?;
        let left = self.to_primitive(scope, left, ToPrimitiveHint::Default)?;
        scope.push_root(left)?;
        Ok((left, other))
      }
      (other, Value::Object(_)) if Self::abstract_equality_needs_to_primitive(other) => {
        scope.push_root(other)?;
        let right = self.to_primitive(scope, right, ToPrimitiveHint::Default)?;
        scope.push_root(right)?;
        Ok((other, right))
      }
      _ => Ok((left, right)),
    }
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
    let exotic = prim_scope.ordinary_get_with_host_and_hooks(
      self.vm,
      &mut *self.host,
      &mut *self.hooks,
      obj,
      to_prim_key,
      Value::Object(obj),
    )?;

    if !matches!(exotic, Value::Undefined | Value::Null) {
      if !prim_scope.heap().is_callable(exotic)? {
        return Err(throw_type_error(
          self.vm,
          &mut prim_scope,
          "@@toPrimitive is not callable",
        )?);
      }

      let hint_s = prim_scope.alloc_string(hint.as_str())?;
      prim_scope.push_root(Value::String(hint_s))?;
      let out = self.call(
        &mut prim_scope,
        exotic,
        Value::Object(obj),
        &[Value::String(hint_s)],
      )?;
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
      let method = scope.ordinary_get_with_host_and_hooks(
        self.vm,
        &mut *self.host,
        &mut *self.hooks,
        obj,
        key,
        Value::Object(obj),
      )?;

      if matches!(method, Value::Undefined | Value::Null) {
        continue;
      }
      if !scope.heap().is_callable(method)? {
        continue;
      }

      let result = self.call(scope, method, Value::Object(obj), &[])?;
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
    debug_assert!(
      self.is_primitive_value(prim),
      "to_primitive returned object"
    );

    match string_scope.heap_mut().to_string(prim) {
      Ok(s) => Ok(s),
      Err(VmError::TypeError(msg)) => Err(throw_type_error(self.vm, &mut string_scope, msg)?),
      Err(err) => Err(err),
    }
  }

  fn to_property_key_operator(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
  ) -> Result<PropertyKey, VmError> {
    match value {
      Value::String(s) => Ok(PropertyKey::String(s)),
      Value::Symbol(s) => Ok(PropertyKey::Symbol(s)),
      other => {
        let mut key_scope = scope.reborrow();
        key_scope.push_root(other)?;
        let prim = self.to_primitive(&mut key_scope, other, ToPrimitiveHint::String)?;
        key_scope.push_root(prim)?;
        match prim {
          Value::Symbol(s) => Ok(PropertyKey::Symbol(s)),
          _ => Ok(PropertyKey::String(
            self.to_string_operator(&mut key_scope, prim)?,
          )),
        }
      }
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
        _ => {
          return Err(throw_type_error(
            self.vm,
            &mut add_scope,
            "Cannot mix BigInt and other types",
          )?)
        }
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

  /// ECMA-262 `ApplyStringOrNumericBinaryOperator` numeric branch (§13.15.3),
  /// covering `-`, `*`, `/`, `%`, `**`, `&`, `|`, `^`, `<<`, `>>`, and `>>>`.
  /// (`+` has its own string-aware path in `addition_operator`.)
  fn apply_numeric_binary(
    &mut self,
    scope: &mut Scope<'_>,
    operator: OperatorName,
    left: Value,
    right: Value,
  ) -> Result<Value, VmError> {
    // Root both operands: `ToNumeric` may run user code (`valueOf`/`toString`) and allocate.
    let mut op_scope = scope.reborrow();
    op_scope.push_root(left)?;
    op_scope.push_root(right)?;

    let left_num = self.to_numeric(&mut op_scope, left)?;
    let right_num = self.to_numeric(&mut op_scope, right)?;
    match (left_num, right_num) {
      (NumericValue::Number(a), NumericValue::Number(b)) => {
        Ok(Value::Number(number_binary_op(operator, a, b)))
      }
      (NumericValue::BigInt(a), NumericValue::BigInt(b)) => {
        self.bigint_binary_op(&mut op_scope, operator, a, b)
      }
      // ECMA-262 forbids mixing BigInt with other numeric types in these operators.
      _ => Err(throw_type_error(
        self.vm,
        &mut op_scope,
        "Cannot mix BigInt and other types, use explicit conversions",
      )?),
    }
  }

  /// ECMA-262 `BigInt::*` numeric-operator dispatch (§6.1.6.2). Bitwise `& | ^`
  /// and shifts `<< >>` use hybrid `JsBigInt` (inline ≤128-bit magnitude,
  /// `num_bigint` beyond). `>>>` on BigInts always throws a `TypeError`
  /// (BigInts are not fixed-width).
  fn bigint_binary_op(
    &mut self,
    scope: &mut Scope<'_>,
    operator: OperatorName,
    a: JsBigInt,
    b: JsBigInt,
  ) -> Result<Value, VmError> {
    let checked = match operator {
      OperatorName::Subtraction => a.checked_sub(b),
      OperatorName::Multiplication => a.checked_mul(b),
      OperatorName::Division => {
        if b.is_zero() {
          return Err(throw_range_error(self.vm, scope, "Division by zero")?);
        }
        a.checked_div(b)
      }
      OperatorName::Remainder => {
        if b.is_zero() {
          return Err(throw_range_error(self.vm, scope, "Division by zero")?);
        }
        a.checked_rem(b)
      }
      OperatorName::Exponentiation => {
        if b.is_negative() {
          return Err(throw_range_error(
            self.vm,
            scope,
            "Exponent must be non-negative",
          )?);
        }
        a.checked_pow(b)
      }
      OperatorName::BitwiseAnd => a.checked_bit_and(b),
      OperatorName::BitwiseOr => a.checked_bit_or(b),
      OperatorName::BitwiseXor => a.checked_bit_xor(b),
      OperatorName::BitwiseLeftShift => a.checked_shift_left(b),
      OperatorName::BitwiseRightShift => a.checked_shift_right(b),
      OperatorName::BitwiseUnsignedRightShift => {
        return Err(throw_type_error(
          self.vm,
          scope,
          "BigInts have no unsigned right shift, use >> instead",
        )?);
      }
      _ => return Err(VmError::Unimplemented("BigInt bitwise/shift operator")),
    };
    match checked {
      Some(out) => Ok(Value::BigInt(out)),
      None => Err(VmError::Unimplemented("BigInt arithmetic overflow")),
    }
  }

  /// ECMA-262 `IsLessThan(x, y, LeftFirst)` (§7.2.15). Returns `None` for the
  /// spec's `undefined` result (a `NaN` operand); callers map that per operator.
  fn is_less_than(
    &mut self,
    scope: &mut Scope<'_>,
    left: Value,
    right: Value,
    left_first: bool,
  ) -> Result<Option<bool>, VmError> {
    let mut cmp_scope = scope.reborrow();
    cmp_scope.push_root(left)?;
    cmp_scope.push_root(right)?;

    // ToPrimitive (hint Number) in the order dictated by LeftFirst so observable
    // side effects (valueOf/toString) happen left-to-right for `<`/`>=` and
    // right-to-left for `>`/`<=`.
    let (px, py) = if left_first {
      let px = self.to_primitive(&mut cmp_scope, left, ToPrimitiveHint::Number)?;
      cmp_scope.push_root(px)?;
      let py = self.to_primitive(&mut cmp_scope, right, ToPrimitiveHint::Number)?;
      cmp_scope.push_root(py)?;
      (px, py)
    } else {
      let py = self.to_primitive(&mut cmp_scope, right, ToPrimitiveHint::Number)?;
      cmp_scope.push_root(py)?;
      let px = self.to_primitive(&mut cmp_scope, left, ToPrimitiveHint::Number)?;
      cmp_scope.push_root(px)?;
      (px, py)
    };

    // Both primitives are strings: compare by UTF-16 code units (§7.2.15 step 3.a).
    if let (Value::String(sx), Value::String(sy)) = (px, py) {
      let a: Vec<u16> = cmp_scope.heap().get_string(sx)?.as_code_units().to_vec();
      let b = cmp_scope.heap().get_string(sy)?;
      return Ok(Some(a.as_slice() < b.as_code_units()));
    }

    // BigInt ↔ String via StringToBigInt (§7.2.15). Must not ToNumber the string:
    // non-integer forms (`"0."`) are unordered, and values past 2^53 must stay exact.
    match (px, py) {
      (Value::BigInt(px), Value::String(sy)) => {
        let text = cmp_scope.heap().get_string(sy)?.to_utf8_lossy();
        return Ok(match JsBigInt::from_string_integer_literal(&text) {
          Some(ny) => Some(px.less_than(ny)),
          None => None,
        });
      }
      (Value::String(sx), Value::BigInt(py)) => {
        let text = cmp_scope.heap().get_string(sx)?.to_utf8_lossy();
        return Ok(match JsBigInt::from_string_integer_literal(&text) {
          Some(nx) => Some(nx.less_than(py)),
          None => None,
        });
      }
      _ => {}
    }

    // Otherwise ToNumeric both and compare (§7.2.15). Mixed BigInt/Number
    // relational comparison is permitted (unlike arithmetic).
    let nx = self.to_numeric(&mut cmp_scope, px)?;
    let ny = self.to_numeric(&mut cmp_scope, py)?;
    Ok(match (nx, ny) {
      (NumericValue::Number(a), NumericValue::Number(b)) => {
        if a.is_nan() || b.is_nan() {
          None
        } else {
          Some(a < b)
        }
      }
      (NumericValue::BigInt(a), NumericValue::BigInt(b)) => Some(a.less_than(b)),
      (NumericValue::BigInt(a), NumericValue::Number(b)) => a.less_than_number(b),
      (NumericValue::Number(a), NumericValue::BigInt(b)) => match b.less_than_number(a) {
        None => None,
        Some(true) => Some(false),
        Some(false) => Some(!b.mathematically_equal_to_number(a)),
      },
    })
  }
}

/// ECMA-262 `ToUint32` (§7.1.7).
pub(crate) fn number_to_uint32(n: f64) -> u32 {
  if !n.is_finite() || n == 0.0 {
    return 0;
  }
  // 2^32; `rem_euclid` yields a value in `[0, 2^32)` so the `as u32` cast is exact.
  let m = n.trunc().rem_euclid(4_294_967_296.0);
  m as u32
}

/// ECMA-262 `ToInt32` (§7.1.6): the two's-complement reinterpretation of `ToUint32`.
pub(crate) fn number_to_int32(n: f64) -> i32 {
  number_to_uint32(n) as i32
}

/// ECMA-262 `Number::exponentiate` (§6.1.6.1.3). Differs from IEEE-754 `pow`
/// in that `1 ** NaN`, `(-1) ** ±Infinity`, and `1 ** ±Infinity` are all `NaN`.
pub(crate) fn number_exponentiate(base: f64, exponent: f64) -> f64 {
  if exponent.is_nan() {
    return f64::NAN;
  }
  if exponent == 0.0 {
    // Includes -0; anything (even NaN) to the zeroth power is 1.
    return 1.0;
  }
  if base.is_nan() {
    return f64::NAN;
  }
  if base.abs() == 1.0 && exponent.is_infinite() {
    return f64::NAN;
  }
  base.powf(exponent)
}

/// ECMA-262 `Number::*` numeric-operator dispatch for `-`, `*`, `/`, `%`, `**`,
/// and the bitwise/shift operators (§6.1.6.1). `+` is handled separately by
/// `addition_operator` because of its string-concatenation branch.
fn number_binary_op(operator: OperatorName, a: f64, b: f64) -> f64 {
  match operator {
    OperatorName::Subtraction => a - b,
    OperatorName::Multiplication => a * b,
    OperatorName::Division => a / b,
    // Rust's `f64::%` is `fmod` (result takes the sign of the dividend), which
    // matches `Number::remainder`.
    OperatorName::Remainder => a % b,
    OperatorName::Exponentiation => number_exponentiate(a, b),
    OperatorName::BitwiseAnd => (number_to_int32(a) & number_to_int32(b)) as f64,
    OperatorName::BitwiseOr => (number_to_int32(a) | number_to_int32(b)) as f64,
    OperatorName::BitwiseXor => (number_to_int32(a) ^ number_to_int32(b)) as f64,
    OperatorName::BitwiseLeftShift => {
      let shift = number_to_uint32(b) & 31;
      number_to_int32(a).wrapping_shl(shift) as f64
    }
    OperatorName::BitwiseRightShift => {
      // Arithmetic (sign-propagating) shift on the signed 32-bit value.
      let shift = number_to_uint32(b) & 31;
      (number_to_int32(a) >> shift) as f64
    }
    OperatorName::BitwiseUnsignedRightShift => {
      // Logical (zero-filling) shift on the unsigned 32-bit value.
      let shift = number_to_uint32(b) & 31;
      (number_to_uint32(a) >> shift) as f64
    }
    _ => {
      debug_assert!(false, "number_binary_op called with non-numeric operator");
      f64::NAN
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

/// ECMA-262 `IsSimpleParameterList` for FunctionDeclarationInstantiation's
/// mapped-arguments decision: no rest, defaults, or binding patterns.
fn is_simple_parameter_list(func: &parse_js::ast::func::Func) -> bool {
  func.parameters.iter().all(|p| {
    !p.stx.rest
      && p.stx.default_value.is_none()
      && matches!(&*p.stx.pattern.stx.pat.stx, Pat::Id(_))
  })
}

/// Result of running an ECMAScript function/constructor body.
pub(crate) struct EcmaBodyResult {
  pub value: Value,
  pub this: Value,
  pub this_initialized: bool,
}

pub(crate) fn run_ecma_function(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  env: &mut RuntimeEnv,
  source: Arc<SourceText>,
  base_offset: u32,
  prefix_len: u32,
  strict: bool,
  this: Value,
  this_uninitialized: bool,
  new_target: Value,
  active_function: Option<GcObject>,
  func: &Node<Func>,
  args: &[Value],
) -> Result<EcmaBodyResult, VmError> {
  if func.stx.async_ || func.stx.generator {
    return Err(VmError::Unimplemented("async/generator functions"));
  }
  env.set_source_info(source, base_offset, prefix_len);

  let Some(body) = &func.stx.body else {
    return Err(VmError::Unimplemented("function without body"));
  };

  let mut evaluator = Evaluator {
    vm,
    host,
    hooks,
    env,
    strict,
    this,
    this_uninitialized,
    new_target,
    active_function,
  };
  evaluator.instantiate_function(scope, func, args)?;

  let value = match body {
    FuncBody::Expression(expr) => match evaluator.eval_expr(scope, expr) {
      Ok(v) => v,
      Err(VmError::Throw(value)) => {
        // Capture stack + annotate the top frame with the expression start location. Expression-body
        // arrow functions do not go through `eval_stmt`, so this is the best central capture point.
        let source = evaluator.env.source();
        let rel_start = expr
          .loc
          .start_u32()
          .saturating_sub(evaluator.env.prefix_len());
        let abs_offset = evaluator.env.base_offset().saturating_add(rel_start);
        let (line, col) = source.line_col(abs_offset);

        let mut stack = evaluator.vm.capture_stack();
        if let Some(top) = stack.first_mut() {
          top.source = source.name.clone();
          top.line = line;
          top.col = col;
        } else {
          stack.push(StackFrame {
            function: None,
            source: source.name.clone(),
            line,
            col,
          });
        }

        return Err(VmError::ThrowWithStack { value, stack });
      }
      Err(other) => return Err(other),
    },
    FuncBody::Block(stmts) => {
      let completion = evaluator.eval_stmt_list(scope, stmts)?;
      match completion {
        Completion::Normal(_) => Value::Undefined,
        Completion::Return(v) => v,
        Completion::Throw(thrown) => {
          return Err(VmError::ThrowWithStack {
            value: thrown.value,
            stack: thrown.stack,
          })
        }
        Completion::Break(..) => return Err(VmError::Unimplemented("break outside of loop")),
        Completion::Continue(..) => return Err(VmError::Unimplemented("continue outside of loop")),
      }
    }
  };
  Ok(EcmaBodyResult {
    value,
    this: evaluator.this,
    this_initialized: !evaluator.this_uninitialized,
  })
}

pub(crate) fn eval_expr(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  env: &mut RuntimeEnv,
  strict: bool,
  this: Value,
  scope: &mut Scope<'_>,
  expr: &Node<Expr>,
) -> Result<Value, VmError> {
  let mut evaluator = Evaluator {
    vm,
    host,
    hooks,
    env,
    strict,
    this,
    this_uninitialized: false,
    new_target: Value::Undefined,
    active_function: None,
  };
  evaluator.eval_expr(scope, expr)
}

/// NamedEvaluation for anonymous class expressions (class name applied during definition so
/// `static name()` can overwrite afterwards).
pub(crate) fn eval_class_expr_named(
  vm: &mut Vm,
  host: &mut dyn VmHost,
  hooks: &mut dyn VmHostHooks,
  env: &mut RuntimeEnv,
  strict: bool,
  this: Value,
  scope: &mut Scope<'_>,
  expr: &Node<ClassExpr>,
  name: &str,
) -> Result<Value, VmError> {
  let mut evaluator = Evaluator {
    vm,
    host,
    hooks,
    env,
    strict,
    this,
    this_uninitialized: false,
    new_target: Value::Undefined,
    active_function: None,
  };
  evaluator.eval_class_expr(scope, expr, Some(name))
}

fn is_class_constructor_method(member: &ClassMember) -> bool {
  if member.static_ {
    return false;
  }
  match &member.key {
    ClassOrObjKey::Direct(direct) => {
      direct.stx.tt != TT::PrivateMember && direct.stx.key == "constructor"
    }
    ClassOrObjKey::Computed(_) => false,
  }
}

fn class_member_is_private(member: &ClassMember) -> bool {
  matches!(&member.key, ClassOrObjKey::Direct(d) if d.stx.tt == TT::PrivateMember)
}

fn private_member_name(member: &ClassMember) -> Option<&str> {
  match &member.key {
    ClassOrObjKey::Direct(d) if d.stx.tt == TT::PrivateMember => Some(d.stx.key.as_str()),
    _ => None,
  }
}

/// `#PrivateIdentifier in …` — left is an IdExpr whose name starts with `#`.
fn private_in_identifier(expr: &BinaryExpr) -> Option<&str> {
  if expr.operator != OperatorName::In {
    return None;
  }
  match &*expr.left.stx {
    Expr::Id(id) if id.stx.name.starts_with('#') => Some(id.stx.name.as_str()),
    _ => None,
  }
}

// ===========================================================================
// Resumable-body (generator / async function) support
// ===========================================================================
//
// These wrappers expose the recursive evaluator's internals to `crate::resumable` (the frame
// machine driving suspendable bodies) and `crate::generator` (generator-object semantics).
// They are deliberately thin: semantics live in the existing private methods.

/// Which body-execution flavor a function uses.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum FunctionFlavor {
  Normal,
  Generator,
  Async,
  AsyncGenerator,
}

impl FunctionFlavor {
  pub(crate) fn of(func: &Func) -> Result<Self, VmError> {
    match (func.async_, func.generator) {
      (false, false) => Ok(Self::Normal),
      (false, true) => Ok(Self::Generator),
      (true, false) => Ok(Self::Async),
      (true, true) => Ok(Self::AsyncGenerator),
    }
  }
}

/// Ordinary `function` declaration (Annex B.3.2 eligible). Generators / async forms are always
/// lexically scoped to their enclosing block / CaseBlock and must not receive a var binding.
fn is_ordinary_function_decl(decl: &FuncDecl) -> bool {
  let func = &decl.function.stx;
  !func.async_ && !func.generator
}

/// A reference resolved ahead of time for the resumable evaluator (assignment targets).
///
/// Unlike the borrow-based [`Reference`], keys/names are owned so the reference can live inside a
/// suspended frame across GC points and resumes.
#[derive(Clone, Debug)]
pub(crate) enum OwnedReference {
  Binding(String),
  Property { base: Value, key: PropertyKey },
}

impl crate::heap::Trace for OwnedReference {
  fn trace(&self, tracer: &mut crate::heap::Tracer<'_>) {
    match self {
      OwnedReference::Binding(_) => {}
      OwnedReference::Property { base, key } => {
        tracer.trace_value(*base);
        match key {
          PropertyKey::String(s) => tracer.trace_value(Value::String(*s)),
          PropertyKey::Symbol(s) => tracer.trace_value(Value::Symbol(*s)),
        }
      }
    }
  }
}

impl<'a> Evaluator<'a> {
  /// Constructs an evaluator for driving a resumable body (generator / async function resume).
  pub(crate) fn new_resumable(
    vm: &'a mut Vm,
    host: &'a mut dyn VmHost,
    hooks: &'a mut dyn VmHostHooks,
    env: &'a mut RuntimeEnv,
    strict: bool,
    this: Value,
  ) -> Self {
    Self {
      vm,
      host,
      hooks,
      env,
      strict,
      this,
      this_uninitialized: false,
      new_target: Value::Undefined,
      active_function: None,
    }
  }

  /// Applies generator/async-specific fixups to a freshly created function object:
  /// `[[Prototype]]` and (for generators) the `.prototype` object.
  fn apply_function_flavor(
    &mut self,
    scope: &mut Scope<'_>,
    func_obj: GcObject,
    flavor: FunctionFlavor,
  ) -> Result<(), VmError> {
    if flavor == FunctionFlavor::Normal {
      return Ok(());
    }
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    match flavor {
      FunctionFlavor::Generator => {
        let gen_fn_proto = intr.generator_function_prototype();
        let gen_proto = intr.generator_prototype();
        scope
          .heap_mut()
          .object_set_prototype(func_obj, Some(gen_fn_proto))?;
        // OrdinaryObjectCreate(%GeneratorFunction.prototype.prototype%) as the function's
        // `.prototype` (writable, non-enumerable, non-configurable; §27.3.2.1 note).
        let mut ps = scope.reborrow();
        ps.push_root(Value::Object(func_obj))?;
        let proto_obj = ps.alloc_object_with_prototype(Some(gen_proto))?;
        ps.push_root(Value::Object(proto_obj))?;
        let key_s = ps.alloc_string("prototype")?;
        ps.push_root(Value::String(key_s))?;
        ps.define_property(
          func_obj,
          PropertyKey::from_string(key_s),
          PropertyDescriptor {
            enumerable: false,
            configurable: false,
            kind: PropertyKind::Data {
              value: Value::Object(proto_obj),
              writable: true,
            },
          },
        )?;
      }
      FunctionFlavor::AsyncGenerator => {
        let ag_fn_proto = intr.async_generator_function_prototype();
        let ag_proto = intr.async_generator_prototype();
        scope
          .heap_mut()
          .object_set_prototype(func_obj, Some(ag_fn_proto))?;
        let mut ps = scope.reborrow();
        ps.push_root(Value::Object(func_obj))?;
        let proto_obj = ps.alloc_object_with_prototype(Some(ag_proto))?;
        ps.push_root(Value::Object(proto_obj))?;
        let key_s = ps.alloc_string("prototype")?;
        ps.push_root(Value::String(key_s))?;
        ps.define_property(
          func_obj,
          PropertyKey::from_string(key_s),
          PropertyDescriptor {
            enumerable: false,
            configurable: false,
            kind: PropertyKind::Data {
              value: Value::Object(proto_obj),
              writable: true,
            },
          },
        )?;
      }
      FunctionFlavor::Async => {
        scope
          .heap_mut()
          .object_set_prototype(func_obj, Some(intr.async_function_prototype()))?;
      }
      FunctionFlavor::Normal => unreachable!(),
    }
    Ok(())
  }

  #[inline]
  pub(crate) fn tick_pub(&mut self) -> Result<(), VmError> {
    self.tick()
  }

  pub(crate) fn lexical_env_pub(&self) -> GcEnv {
    self.env.lexical_env
  }

  pub(crate) fn set_lexical_env_pub(&mut self, scope: &mut Scope<'_>, env: GcEnv) {
    self.env.set_lexical_env(scope.heap_mut(), env);
  }

  pub(crate) fn global_object_pub(&self) -> GcObject {
    self.env.global_object
  }

  pub(crate) fn eval_expr_pub(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<Expr>,
  ) -> Result<Value, VmError> {
    self.eval_expr(scope, expr)
  }

  pub(crate) fn eval_stmt_labelled_pub(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &Node<Stmt>,
    label_set: &[String],
  ) -> Result<Completion, VmError> {
    self.eval_stmt_labelled(scope, stmt, label_set)
  }

  pub(crate) fn eval_var_decl_pub(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &VarDecl,
  ) -> Result<(), VmError> {
    self.eval_var_decl(scope, decl).map(|_| ())
  }

  pub(crate) fn loop_continues_pub(completion: &Completion, label_set: &[String]) -> bool {
    Self::loop_continues(completion, label_set)
  }

  pub(crate) fn to_boolean_pub(&self, scope: &Scope<'_>, value: Value) -> Result<bool, VmError> {
    to_boolean(scope.heap(), value)
  }

  pub(crate) fn thrown_from_value_pub(&mut self, value: Value) -> Thrown {
    Thrown {
      value,
      stack: self.vm.capture_stack(),
    }
  }

  /// Converts a `VmError` from a performed action into a catchable [`Thrown`], or returns the
  /// error unchanged when it is not a JS-level throw (host errors, limits, ICEs).
  pub(crate) fn error_to_thrown(
    &mut self,
    _scope: &mut Scope<'_>,
    err: VmError,
  ) -> Result<Thrown, VmError> {
    match err {
      VmError::Throw(value) => Ok(Thrown {
        value,
        stack: self.vm.capture_stack(),
      }),
      VmError::ThrowWithStack { value, stack } => Ok(Thrown { value, stack }),
      other => Err(other),
    }
  }

  /// Enters a fresh block environment for `stmts` (instantiating lexical declarations), returning
  /// the previous lexical environment.
  pub(crate) fn enter_block_env_pub(
    &mut self,
    scope: &mut Scope<'_>,
    stmts: &[Node<Stmt>],
  ) -> Result<GcEnv, VmError> {
    let outer = self.env.lexical_env;
    let block_env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), block_env);
    if let Err(err) = self.instantiate_block_decls_in_stmt_list(scope, block_env, stmts) {
      self.env.set_lexical_env(scope.heap_mut(), outer);
      return Err(err);
    }
    Ok(outer)
  }

  /// Enters a fresh (declaration-less) child environment, returning the previous one.
  pub(crate) fn enter_plain_env_pub(&mut self, scope: &mut Scope<'_>) -> Result<GcEnv, VmError> {
    let outer = self.env.lexical_env;
    let env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), env);
    Ok(outer)
  }

  /// `ToObject` + NewObjectEnvironment(`withEnvironment=true`) for a resumable `with` frame.
  /// Returns the previous lexical environment.
  pub(crate) fn enter_with_env_pub(
    &mut self,
    scope: &mut Scope<'_>,
    object: Value,
  ) -> Result<GcEnv, VmError> {
    let binding_object = self.to_object(scope, object)?;
    let outer = self.env.lexical_env;
    let mut with_scope = scope.reborrow();
    with_scope.push_root(Value::Object(binding_object))?;
    with_scope.push_env_root(outer)?;
    let with_env = with_scope.alloc_object_env_record(binding_object, Some(outer), true)?;
    self.env.set_lexical_env(with_scope.heap_mut(), with_env);
    Ok(outer)
  }

  /// Resumable driver entry for ECMA-262 `CreatePerIterationEnvironment`.
  pub(crate) fn create_per_iteration_environment_pub(
    &mut self,
    scope: &mut Scope<'_>,
    per_iteration_names: &[String],
  ) -> Result<(), VmError> {
    self.create_per_iteration_environment(scope, per_iteration_names)
  }

  pub(crate) fn collect_for_triple_per_iteration_names_pub(decl: &VarDecl) -> Vec<String> {
    Self::collect_for_triple_per_iteration_names(decl)
  }

  /// Enters the catch scope for `catch`, binding its parameter to `thrown`. Returns the previous
  /// lexical environment. Mirrors [`Evaluator::eval_catch`]'s environment discipline.
  pub(crate) fn enter_catch_env_pub(
    &mut self,
    scope: &mut Scope<'_>,
    catch: &CatchBlock,
    thrown: Value,
  ) -> Result<GcEnv, VmError> {
    // Same rooting window as `eval_catch`: root before `env_create` may GC.
    scope.push_root(thrown)?;

    let outer = self.env.lexical_env;
    let catch_env = scope.env_create(Some(outer))?;
    self.env.set_lexical_env(scope.heap_mut(), catch_env);

    let result = (|| -> Result<(), VmError> {
      let mut catch_scope = scope.reborrow();
      self.instantiate_block_decls_in_stmt_list(&mut catch_scope, catch_env, &catch.body)?;
      if let Some(param) = &catch.parameter {
        self.bind_catch_param(&mut catch_scope, &param.stx, thrown, catch_env)?;
      }
      Ok(())
    })();

    match result {
      Ok(()) => Ok(outer),
      Err(err) => {
        self.env.set_lexical_env(scope.heap_mut(), outer);
        Err(err)
      }
    }
  }

  /// Binds a for-of / for-await LHS to the next iteration value.
  ///
  /// Lexical (`let`/`const`) declarations get a fresh per-iteration environment (same emulation
  /// as `for-in`); the previous lexical env is returned so the frame machine can restore it after
  /// the body. `var` and assignment LHSes bind in place and return `None`.
  pub(crate) fn bind_for_of_lhs_pub(
    &mut self,
    scope: &mut Scope<'_>,
    stmt: &ForOfStmt,
    value: Value,
  ) -> Result<Option<GcEnv>, VmError> {
    let mut bind_scope = scope.reborrow();
    bind_scope.push_root(value)?;

    let mut restore: Option<GcEnv> = None;
    if let ForInOfLhs::Decl((mode, _)) = &stmt.lhs {
      if *mode == VarDeclMode::Let || *mode == VarDeclMode::Const {
        let outer = self.env.lexical_env;
        let env = bind_scope.env_create(Some(outer))?;
        self.env.set_lexical_env(bind_scope.heap_mut(), env);
        restore = Some(outer);
      }
    }

    let bind_res = match &stmt.lhs {
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
          &mut *self.host,
          &mut *self.hooks,
          &mut bind_scope,
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
        &mut *self.host,
        &mut *self.hooks,
        &mut bind_scope,
        self.env,
        &pat.stx,
        value,
        BindingKind::Assignment,
        self.strict,
        self.this,
      ),
    };

    if let Err(err) = bind_res {
      if let Some(outer) = restore {
        self.env.set_lexical_env(bind_scope.heap_mut(), outer);
      }
      return Err(err);
    }
    Ok(restore)
  }

  /// Binds declarator `idx` of `decl` to `value` (resumable var-decl path; the initializer has
  /// already been evaluated by the frame machine).
  pub(crate) fn bind_var_declarator_pub(
    &mut self,
    scope: &mut Scope<'_>,
    decl: &VarDecl,
    idx: usize,
    value: Value,
  ) -> Result<(), VmError> {
    let declarator = decl
      .declarators
      .get(idx)
      .ok_or(VmError::InvariantViolation("declarator index out of range"))?;
    // `let x;` (no initializer) still creates+initializes the binding to undefined; `var x;` was
    // already hoisted and must NOT be reset. Mirrors `eval_var_decl`.
    if declarator.initializer.is_none() && decl.mode == VarDeclMode::Var {
      return Ok(());
    }
    let kind = match decl.mode {
      VarDeclMode::Var => BindingKind::Var,
      VarDeclMode::Let => BindingKind::Let,
      VarDeclMode::Const => BindingKind::Const,
      _ => return Err(VmError::Unimplemented("variable declaration kind")),
    };
    let mut bind_scope = scope.reborrow();
    bind_scope.push_root(value)?;
    bind_pattern(
      self.vm,
      &mut *self.host,
      &mut *self.hooks,
      &mut bind_scope,
      self.env,
      &declarator.pattern.stx.pat.stx,
      value,
      kind,
      self.strict,
      self.this,
    )
  }

  /// Applies a binary *value* operator (both operands already evaluated). Assignment and
  /// short-circuit operators are handled by the frame machine, not here.
  pub(crate) fn eval_private_in_pub(
    &mut self,
    scope: &mut Scope<'_>,
    private_name: &str,
    right: Value,
  ) -> Result<Value, VmError> {
    self.eval_private_in(scope, private_name, right)
  }

  pub(crate) fn binary_value_op_pub(
    &mut self,
    scope: &mut Scope<'_>,
    op: OperatorName,
    left: Value,
    right: Value,
  ) -> Result<Value, VmError> {
    let mut s = scope.reborrow();
    s.push_roots(&[left, right])?;
    match op {
      OperatorName::Addition => self.addition_operator(&mut s, left, right),
      OperatorName::Multiplication
      | OperatorName::Subtraction
      | OperatorName::Division
      | OperatorName::Remainder
      | OperatorName::Exponentiation
      | OperatorName::BitwiseAnd
      | OperatorName::BitwiseOr
      | OperatorName::BitwiseXor
      | OperatorName::BitwiseLeftShift
      | OperatorName::BitwiseRightShift
      | OperatorName::BitwiseUnsignedRightShift => {
        self.apply_numeric_binary(&mut s, op, left, right)
      }
      OperatorName::StrictEquality => Ok(Value::Bool(strict_equal(s.heap(), left, right)?)),
      OperatorName::StrictInequality => Ok(Value::Bool(!strict_equal(s.heap(), left, right)?)),
      OperatorName::Equality => {
        let (left, right) = self.abstract_equality_prepare_primitives(&mut s, left, right)?;
        Ok(Value::Bool(abstract_equality(s.heap_mut(), left, right)?))
      }
      OperatorName::Inequality => {
        let (left, right) = self.abstract_equality_prepare_primitives(&mut s, left, right)?;
        Ok(Value::Bool(!abstract_equality(s.heap_mut(), left, right)?))
      }
      OperatorName::LessThan => Ok(Value::Bool(
        self
          .is_less_than(&mut s, left, right, true)?
          .unwrap_or(false),
      )),
      OperatorName::GreaterThan => Ok(Value::Bool(
        self
          .is_less_than(&mut s, right, left, false)?
          .unwrap_or(false),
      )),
      OperatorName::LessThanOrEqual => Ok(Value::Bool(
        self.is_less_than(&mut s, right, left, false)? == Some(false),
      )),
      OperatorName::GreaterThanOrEqual => Ok(Value::Bool(
        self.is_less_than(&mut s, left, right, true)? == Some(false),
      )),
      OperatorName::Instanceof => Ok(Value::Bool(self.instanceof_operator(&mut s, left, right)?)),
      OperatorName::In => {
        let Value::Object(obj) = right else {
          return Err(throw_type_error(
            self.vm,
            &mut s,
            "Right-hand side of 'in' should be an object",
          )?);
        };
        s.push_root(Value::Object(obj))?;
        let key = self.to_property_key_operator(&mut s, left)?;
        Ok(Value::Bool(s.ordinary_has_property(obj, key)?))
      }
      _ => Err(VmError::Unimplemented("binary operator on values")),
    }
  }

  /// Applies a unary *value* operator (operand already evaluated).
  pub(crate) fn unary_value_op_pub(
    &mut self,
    scope: &mut Scope<'_>,
    op: OperatorName,
    value: Value,
  ) -> Result<Value, VmError> {
    let mut s = scope.reborrow();
    s.push_root(value)?;
    match op {
      OperatorName::LogicalNot => Ok(Value::Bool(!to_boolean(s.heap(), value)?)),
      OperatorName::Void => Ok(Value::Undefined),
      OperatorName::Typeof => {
        let t = typeof_name(s.heap(), value)?;
        let out = s.alloc_string(t)?;
        Ok(Value::String(out))
      }
      OperatorName::UnaryPlus => {
        let n = self.to_number_operator(&mut s, value)?;
        Ok(Value::Number(n))
      }
      OperatorName::UnaryNegation => Ok(match self.to_numeric(&mut s, value)? {
        NumericValue::Number(n) => Value::Number(-n),
        NumericValue::BigInt(b) => Value::BigInt(b.negate()),
      }),
      OperatorName::BitwiseNot => Ok(match self.to_numeric(&mut s, value)? {
        NumericValue::Number(n) => Value::Number(!number_to_int32(n) as f64),
        NumericValue::BigInt(b) => {
          let neg_one = JsBigInt::from_u128(1).negate();
          let out = b
            .negate()
            .checked_add(neg_one)
            .ok_or(VmError::OutOfMemory)?;
          Value::BigInt(out)
        }
      }),
      _ => Err(VmError::Unimplemented("unary operator on values")),
    }
  }

  /// Resolves a simple assignment target to an owned reference (evaluating any object/key
  /// sub-expressions, which must be suspend-free).
  pub(crate) fn resolve_owned_reference_pub(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<Expr>,
  ) -> Result<OwnedReference, VmError> {
    let reference = self.eval_reference(scope, expr)?;
    Ok(match reference {
      Reference::Binding(name) => OwnedReference::Binding(name.to_string()),
      Reference::Property { base, key } => OwnedReference::Property { base, key },
    })
  }

  pub(crate) fn owned_reference_get_pub(
    &mut self,
    scope: &mut Scope<'_>,
    reference: &OwnedReference,
  ) -> Result<Value, VmError> {
    match reference {
      OwnedReference::Binding(name) => {
        let borrowed = Reference::Binding(name.as_str());
        self.get_value_from_reference(scope, &borrowed)
      }
      OwnedReference::Property { base, key } => {
        let borrowed = Reference::Property {
          base: *base,
          key: *key,
        };
        self.get_value_from_reference(scope, &borrowed)
      }
    }
  }

  pub(crate) fn owned_reference_put_pub(
    &mut self,
    scope: &mut Scope<'_>,
    reference: &OwnedReference,
    value: Value,
  ) -> Result<(), VmError> {
    let mut s = scope.reborrow();
    s.push_root(value)?;
    match reference {
      OwnedReference::Binding(name) => {
        let borrowed = Reference::Binding(name.as_str());
        self.put_value_to_reference(&mut s, &borrowed, value)
      }
      OwnedReference::Property { base, key } => {
        let borrowed = Reference::Property {
          base: *base,
          key: *key,
        };
        self.root_reference(&mut s, &borrowed)?;
        self.put_value_to_reference(&mut s, &borrowed, value)
      }
    }
  }

  /// Evaluates a call callee, producing `(function, this)`. Mirrors `eval_call`'s callee logic
  /// (member/computed-member receivers bind `this`; plain expressions get `undefined`).
  ///
  /// Note: direct `eval(...)` is NOT special-cased here (a suspend point inside direct-eval
  /// arguments is out of scope for resumable bodies).
  pub(crate) fn eval_callee_pub(
    &mut self,
    scope: &mut Scope<'_>,
    callee: &Node<Expr>,
  ) -> Result<(Value, Value), VmError> {
    match &*callee.stx {
      Expr::Member(member) if !member.stx.optional_chaining => {
        let base = self.eval_expr(scope, &member.stx.left)?;
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let key_s = key_scope.alloc_string(&member.stx.right)?;
        let key = PropertyKey::from_string(key_s);
        let callee_value = self.get_v(&mut key_scope, base, key)?;
        Ok((callee_value, base))
      }
      Expr::ComputedMember(member) if !member.stx.optional_chaining => {
        let base = self.eval_expr(scope, &member.stx.object)?;
        let mut key_scope = scope.reborrow();
        key_scope.push_root(base)?;
        let member_value = self.eval_expr(&mut key_scope, &member.stx.member)?;
        key_scope.push_root(member_value)?;
        let key = self.to_property_key_operator(&mut key_scope, member_value)?;
        let callee_value = self.get_v(&mut key_scope, base, key)?;
        Ok((callee_value, base))
      }
      Expr::Id(_) | Expr::IdPat(_) => {
        let reference = self.eval_reference(scope, callee)?;
        let mut callee_scope = scope.reborrow();
        self.root_reference(&mut callee_scope, &reference)?;
        let callee_value = self.get_value_from_reference(&mut callee_scope, &reference)?;
        Ok((callee_value, Value::Undefined))
      }
      _ => {
        let callee_value = self.eval_expr(scope, callee)?;
        Ok((callee_value, Value::Undefined))
      }
    }
  }

  /// Calls `func` with `this` and `args` (all pre-evaluated), rooting them across the call.
  pub(crate) fn call_function_value_pub(
    &mut self,
    scope: &mut Scope<'_>,
    func: Value,
    this: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let mut call_scope = scope.reborrow();
    call_scope.push_root(func)?;
    call_scope.push_root(this)?;
    for arg in args {
      call_scope.push_root(*arg)?;
    }
    self.call(&mut call_scope, func, this, args)
  }

  pub(crate) fn get_iterator_pub(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
  ) -> Result<iterator::IteratorRecord, VmError> {
    let mut s = scope.reborrow();
    s.push_root(value)?;
    iterator::get_iterator(self.vm, &mut *self.host, &mut *self.hooks, &mut s, value)
  }

  pub(crate) fn get_async_iterator_pub(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
  ) -> Result<iterator::IteratorRecord, VmError> {
    let mut s = scope.reborrow();
    s.push_root(value)?;
    iterator::get_async_iterator(self.vm, &mut *self.host, &mut *self.hooks, &mut s, value)
  }

  pub(crate) fn iterator_next_pub(
    &mut self,
    scope: &mut Scope<'_>,
    record: &iterator::IteratorRecord,
  ) -> Result<Value, VmError> {
    let mut s = scope.reborrow();
    s.push_roots(&[record.iterator, record.next_method])?;
    iterator::iterator_next(self.vm, &mut *self.host, &mut *self.hooks, &mut s, record)
  }

  pub(crate) fn iterator_step_value_pub(
    &mut self,
    scope: &mut Scope<'_>,
    record: &mut iterator::IteratorRecord,
  ) -> Result<Option<Value>, VmError> {
    let mut s = scope.reborrow();
    s.push_roots(&[record.iterator, record.next_method])?;
    iterator::iterator_step_value(self.vm, &mut *self.host, &mut *self.hooks, &mut s, record)
  }

  /// IteratorClose on an abrupt path: errors from `return()` are swallowed (the original abrupt
  /// completion wins), mirroring the recursive evaluator's abrupt-exit handling.
  pub(crate) fn iterator_close_quiet_pub(
    &mut self,
    scope: &mut Scope<'_>,
    record: &iterator::IteratorRecord,
  ) {
    let mut s = scope.reborrow();
    if s
      .push_roots(&[record.iterator, record.next_method])
      .is_err()
    {
      return;
    }
    let _ = iterator::iterator_close(self.vm, &mut *self.host, &mut *self.hooks, &mut s, record);
  }

  /// Extracts `(value, done)` from an iterator result object (spec `IteratorComplete` +
  /// `IteratorValue`). Non-object results throw a TypeError (§7.4.3).
  pub(crate) fn iterator_result_parts_pub(
    &mut self,
    scope: &mut Scope<'_>,
    result: Value,
  ) -> Result<(Value, bool), VmError> {
    let mut s = scope.reborrow();
    s.push_root(result)?;
    if !matches!(result, Value::Object(_)) {
      return Err(throw_type_error(
        self.vm,
        &mut s,
        "Iterator result is not an object",
      )?);
    }
    let done_key = PropertyKey::from_string(s.alloc_string("done")?);
    let done_v = self.get_v(&mut s, result, done_key)?;
    let done = to_boolean(s.heap(), done_v)?;
    let value_key = PropertyKey::from_string(s.alloc_string("value")?);
    let value = self.get_v(&mut s, result, value_key)?;
    Ok((value, done))
  }

  /// Spec `GetMethod(V, P)`: `undefined`/`null` → `Undefined`; non-callable → TypeError.
  pub(crate) fn get_method_pub(
    &mut self,
    scope: &mut Scope<'_>,
    value: Value,
    name: &str,
  ) -> Result<Value, VmError> {
    let mut s = scope.reborrow();
    s.push_root(value)?;
    let key = PropertyKey::from_string(s.alloc_string(name)?);
    let method = self.get_v(&mut s, value, key)?;
    match method {
      Value::Undefined | Value::Null => Ok(Value::Undefined),
      Value::Object(obj) if s.heap().get_function(obj).is_ok() => Ok(method),
      _ => Err(throw_type_error(
        self.vm,
        &mut s,
        "Property is not a method",
      )?),
    }
  }

  /// Creates (and returns as a `VmError::Throw`) a TypeError value.
  pub(crate) fn make_type_error_pub(
    &mut self,
    scope: &mut Scope<'_>,
    message: &str,
  ) -> Result<VmError, VmError> {
    throw_type_error(self.vm, scope, message)
  }

  /// Allocates the array-literal backing object (empty, `%Array.prototype%`).
  pub(crate) fn array_literal_new_pub(
    &mut self,
    scope: &mut Scope<'_>,
  ) -> Result<GcObject, VmError> {
    let mut s = scope.reborrow();
    let arr = s.alloc_array(0)?;
    s.push_root(Value::Object(arr))?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    s.heap_mut()
      .object_set_prototype(arr, Some(intr.array_prototype()))?;
    Ok(arr)
  }

  pub(crate) fn array_literal_define_pub(
    &mut self,
    scope: &mut Scope<'_>,
    arr: GcObject,
    index: u32,
    value: Value,
  ) -> Result<(), VmError> {
    let mut s = scope.reborrow();
    s.push_root(Value::Object(arr))?;
    s.push_root(value)?;
    let key_s = s.alloc_string(&index.to_string())?;
    s.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);
    let ok = s.create_data_property(arr, key, value)?;
    if !ok {
      return Err(VmError::Unimplemented("CreateDataProperty returned false"));
    }
    Ok(())
  }

  pub(crate) fn array_literal_finalize_pub(
    &mut self,
    scope: &mut Scope<'_>,
    arr: GcObject,
    length: u32,
  ) -> Result<(), VmError> {
    let mut s = scope.reborrow();
    s.push_root(Value::Object(arr))?;
    let length_key_s = s.alloc_string("length")?;
    let length_desc = PropertyDescriptor {
      enumerable: false,
      configurable: false,
      kind: PropertyKind::Data {
        value: Value::Number(length as f64),
        writable: true,
      },
    };
    s.define_property(arr, PropertyKey::from_string(length_key_s), length_desc)?;
    Ok(())
  }

  /// Allocates the object-literal backing object (empty, `%Object.prototype%`).
  pub(crate) fn object_literal_new_pub(
    &mut self,
    scope: &mut Scope<'_>,
  ) -> Result<GcObject, VmError> {
    let mut s = scope.reborrow();
    let obj = s.alloc_object()?;
    s.push_root(Value::Object(obj))?;
    let intr = self
      .vm
      .intrinsics()
      .ok_or(VmError::Unimplemented("intrinsics not initialized"))?;
    s.heap_mut()
      .object_set_prototype(obj, Some(intr.object_prototype()))?;
    Ok(obj)
  }

  /// Applies one suspend-free object-literal member onto `obj` (same semantics as `eval_lit_obj`).
  pub(crate) fn object_literal_apply_member_pub(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    expr: &LitObjExpr,
    member_idx: usize,
  ) -> Result<(), VmError> {
    let member = expr
      .members
      .get(member_idx)
      .ok_or(VmError::Unimplemented("object literal member index"))?;
    self.apply_lit_obj_member(scope, obj, &member.stx.typ)
  }

  /// `CreateDataProperty(obj, ToPropertyKey(key), value)`.
  pub(crate) fn object_literal_define_pub(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    key_value: Value,
    value: Value,
  ) -> Result<(), VmError> {
    let mut s = scope.reborrow();
    s.push_root(Value::Object(obj))?;
    s.push_root(key_value)?;
    s.push_root(value)?;
    let key = self.to_property_key_operator(&mut s, key_value)?;
    match key {
      PropertyKey::String(ks) => s.push_root(Value::String(ks))?,
      PropertyKey::Symbol(ks) => s.push_root(Value::Symbol(ks))?,
    };
    let ok = s.create_data_property(obj, key, value)?;
    if !ok {
      return Err(VmError::Unimplemented("CreateDataProperty returned false"));
    }
    Ok(())
  }

  /// Resolves a Direct object-literal key and `CreateDataProperty(obj, key, value)`.
  pub(crate) fn object_literal_define_direct_pub(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    expr: &LitObjExpr,
    member_idx: usize,
    value: Value,
  ) -> Result<(), VmError> {
    let member = expr
      .members
      .get(member_idx)
      .ok_or(VmError::Unimplemented("object literal member index"))?;
    let ObjMemberType::Valued {
      key: ClassOrObjKey::Direct(direct),
      ..
    } = &member.stx.typ
    else {
      return Err(VmError::Unimplemented("object literal direct key member"));
    };
    let mut s = scope.reborrow();
    s.push_root(Value::Object(obj))?;
    s.push_root(value)?;
    let key_s = if let Some(units) = literal_string_code_units(&direct.assoc) {
      s.alloc_string_from_code_units(units)?
    } else if direct.stx.tt == TT::LiteralNumber {
      let n = direct
        .stx
        .key
        .parse::<f64>()
        .map_err(|_| VmError::Unimplemented("numeric literal property name parse"))?;
      s.heap_mut().to_string(Value::Number(n))?
    } else {
      s.alloc_string(&direct.stx.key)?
    };
    s.push_root(Value::String(key_s))?;
    let key = PropertyKey::from_string(key_s);
    let ok = s.create_data_property(obj, key, value)?;
    if !ok {
      return Err(VmError::Unimplemented("CreateDataProperty returned false"));
    }
    Ok(())
  }

  /// CopyDataProperties-style object spread onto `obj` from `source` (null/undefined → no-op).
  pub(crate) fn object_literal_spread_pub(
    &mut self,
    scope: &mut Scope<'_>,
    obj: GcObject,
    source: Value,
  ) -> Result<(), VmError> {
    let mut s = scope.reborrow();
    s.push_root(Value::Object(obj))?;
    s.push_root(source)?;
    let src_obj = match source {
      Value::Undefined | Value::Null => return Ok(()),
      Value::Object(o) => o,
      _ => return Err(VmError::Unimplemented("object spread source type")),
    };
    let keys = s.ordinary_own_property_keys(src_obj)?;
    for key in keys {
      let mut key_scope = s.reborrow();
      key_scope.push_root(Value::Object(src_obj))?;
      match key {
        PropertyKey::String(ks) => key_scope.push_root(Value::String(ks))?,
        PropertyKey::Symbol(ks) => key_scope.push_root(Value::Symbol(ks))?,
      };
      let Some(desc) = key_scope.ordinary_get_own_property(src_obj, key)? else {
        continue;
      };
      if !desc.enumerable {
        continue;
      }
      let value = key_scope.ordinary_get_with_host_and_hooks(
        self.vm,
        &mut *self.host,
        &mut *self.hooks,
        src_obj,
        key,
        Value::Object(src_obj),
      )?;
      key_scope.push_root(value)?;
      let ok = key_scope.create_data_property(obj, key, value)?;
      if !ok {
        return Err(VmError::Unimplemented("CreateDataProperty returned false"));
      }
    }
    Ok(())
  }

  /// `GetV(base, ToPropertyKey(key_value))` for resumable computed member access.
  pub(crate) fn get_computed_pub(
    &mut self,
    scope: &mut Scope<'_>,
    base: Value,
    key_value: Value,
  ) -> Result<Value, VmError> {
    let mut s = scope.reborrow();
    s.push_root(base)?;
    s.push_root(key_value)?;
    let key = self.to_property_key_operator(&mut s, key_value)?;
    self.get_v(&mut s, base, key)
  }

  /// Evaluates an optional-chain spine. `None` means short-circuit (§13.3.9).
  pub(crate) fn eval_chain_pub(
    &mut self,
    scope: &mut Scope<'_>,
    expr: &Node<Expr>,
  ) -> Result<Option<Value>, VmError> {
    match self.eval_chain(scope, expr)? {
      ChainVal::ShortCircuit => Ok(None),
      ChainVal::Value { value, .. } => Ok(Some(value)),
    }
  }

  /// Runs `FunctionDeclarationInstantiation` for a suspendable call (parameter binding, hoisting)
  /// in the current environments. Exposed for `crate::generator`.
  pub(crate) fn instantiate_function_pub(
    &mut self,
    scope: &mut Scope<'_>,
    func: &Node<Func>,
    args: &[Value],
  ) -> Result<(), VmError> {
    self.instantiate_function(scope, func, args)
  }
}

fn is_nullish(value: Value) -> bool {
  matches!(value, Value::Undefined | Value::Null)
}

/// Returns whether `expr` is (the root of) an `OptionalExpression` — i.e. it contains a `?.` link
/// within its own chain (ECMA-262 §13.3.9). Parenthesization ends a sub-chain: an optional link
/// inside a parenthesized sub-expression belongs to a *separate* chain, so we do not recurse into
/// a parenthesized base (that is exactly why `(a?.b).c` throws instead of short-circuiting).
pub(crate) fn expr_contains_optional_link(expr: &Node<Expr>) -> bool {
  contains_optional_link(expr)
}

fn contains_optional_link(expr: &Node<Expr>) -> bool {
  fn recurse_base(base: &Node<Expr>) -> bool {
    if base.assoc.get::<ParenthesizedExpr>().is_some() {
      return false;
    }
    contains_optional_link(base)
  }
  match &*expr.stx {
    Expr::Member(m) => m.stx.optional_chaining || recurse_base(&m.stx.left),
    Expr::ComputedMember(m) => m.stx.optional_chaining || recurse_base(&m.stx.object),
    Expr::Call(c) => c.stx.optional_chaining || recurse_base(&c.stx.callee),
    _ => false,
  }
}

/// Parses `s` as a canonical non-negative array index (ECMA-262 `CanonicalNumericIndexString`
/// restricted to integer indices), returning `None` unless `s` is exactly the shortest decimal
/// representation of the integer (no leading zeros, no sign, no other characters).
fn canonical_array_index(s: &str) -> Option<usize> {
  if s.is_empty() {
    return None;
  }
  if s == "0" {
    return Some(0);
  }
  // Reject leading zeros ("01"), signs, and non-digit characters.
  if s.as_bytes()[0] == b'0' || !s.bytes().all(|b| b.is_ascii_digit()) {
    return None;
  }
  s.parse::<usize>().ok()
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
