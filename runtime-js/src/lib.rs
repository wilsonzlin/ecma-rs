//! Minimal JavaScript interpreter/runtime for `ecma-rs`.
//!
//! This crate is intentionally small: it is only meant to execute the initial
//! curated `test262-semantic` suite and provide a spec-shaped foundation that
//! can grow into a full runtime.

use diagnostics::FileId;
use parse_js::ast::expr::pat::IdPat;
use parse_js::ast::expr::BinaryExpr;
use parse_js::ast::expr::CallExpr;
use parse_js::ast::expr::ComputedMemberExpr;
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::FuncExpr;
use parse_js::ast::expr::IdExpr;
use parse_js::ast::expr::MemberExpr;
use parse_js::ast::expr::UnaryExpr;
use parse_js::ast::func::Func;
use parse_js::ast::func::FuncBody;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::FuncDecl;
use parse_js::ast::stmt::decl::VarDecl;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::Dialect;
use parse_js::ParseOptions;
use parse_js::SourceType;
use vm_js::Budget;
use vm_js::GcObject;
use vm_js::GcString;
use vm_js::GcSymbol;
use vm_js::Heap;
use vm_js::HeapLimits;
use vm_js::PropertyDescriptor;
use vm_js::PropertyKey;
use vm_js::PropertyKind;
use vm_js::Scope;
use vm_js::Value;
use vm_js::Vm;
use vm_js::VmError;
use vm_js::VmOptions;

/// Execute a classic script.
///
/// Success is `Ok(())`. Failures are returned as [`VmError`] variants:
/// - [`VmError::Syntax`] for parse errors.
/// - [`VmError::Throw`] for uncaught JS throws.
/// - [`VmError::Termination`] / [`VmError::OutOfMemory`] for non-catchable termination.
pub fn execute_script(source: &str, heap_limits: HeapLimits, budget: Budget) -> Result<(), VmError> {
  execute_script_named("<script>", source, heap_limits, budget)
}

/// Execute a classic script with an explicit source name.
pub fn execute_script_named(
  _name: &str,
  source: &str,
  heap_limits: HeapLimits,
  budget: Budget,
) -> Result<(), VmError> {
  let ast = parse_js::parse_with_options(
    source,
    ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    },
  )
  .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;

  let mut heap = Heap::new(heap_limits);
  let mut engine: Engine<'_> = Engine::new(&mut heap, budget)?;
  let mut scope = heap.scope();
  engine.run(&mut scope, &ast)
}

#[derive(Clone, Copy, Debug)]
struct ExecCtx {
  env: GcObject,
  this: Value,
}

#[derive(Clone, Copy, Debug)]
enum Control {
  Normal,
  Return(Value),
}

struct Engine<'a> {
  vm: Vm,

  // Global objects / built-ins.
  global_env: GcObject,
  global_this: GcObject,
  object_prototype: GcObject,

  // Common strings.
  key_prototype: GcString,
  key_constructor: GcString,
  key_name: GcString,

  // Internal slots.
  sym_function_id: GcSymbol,
  sym_function_env: GcSymbol,

  // Pre-allocated throw values for common errors.
  type_error: Value,

  functions: Vec<FunctionData<'a>>,
}

enum FunctionKind<'a> {
  User { func: &'a Node<Func> },
  NativeObject,
}

struct FunctionData<'a> {
  kind: FunctionKind<'a>,
}

impl<'a> Engine<'a> {
  fn new(heap: &mut Heap, budget: Budget) -> Result<Self, VmError> {
    let mut vm = Vm::new(VmOptions::default());
    vm.set_budget(budget);

    let (
      global_env,
      global_this,
      object_prototype,
      key_prototype,
      key_constructor,
      key_name,
      sym_function_id,
      sym_function_env,
      type_error_str,
      functions,
    ) = {
      let mut scope = heap.scope();

      let key_prototype = scope.alloc_string("prototype")?;
      let key_constructor = scope.alloc_string("constructor")?;
      let key_name = scope.alloc_string("name")?;
      let key_object = scope.alloc_string("Object")?;
      let key_undefined = scope.alloc_string("undefined")?;

      let sym_function_id = scope.alloc_symbol(Some("[[FunctionId]]"))?;
      let sym_function_env = scope.alloc_symbol(Some("[[FunctionEnv]]"))?;

      // Pre-allocate "TypeError" for cheap throw paths (we don't implement real Error objects yet).
      let type_error_str = scope.alloc_string("TypeError")?;

      // Object.prototype: ordinary object with null internal prototype.
      let object_prototype = scope.alloc_object()?;

      // Global object environment record: modelled as the global object itself (sloppy script
      // semantics), whose internal prototype is `Object.prototype`.
      let global_this = scope.alloc_object_with_prototype(Some(object_prototype))?;
      let global_env = global_this;

      // Install the built-in Object constructor.
      let (object_ctor, functions) = Self::init_object_constructor(
        &mut scope,
        sym_function_id,
        sym_function_env,
        global_env,
        object_prototype,
        key_prototype,
        key_constructor,
        key_name,
        key_object,
      )?;

      // Global bindings.
      Self::define_data_property(
        &mut scope,
        global_env,
        PropertyKey::from_string(key_object),
        Value::Object(object_ctor),
      )?;
      Self::define_data_property(
        &mut scope,
        global_env,
        PropertyKey::from_string(key_undefined),
        Value::Undefined,
      )?;

      // Keep core handles alive regardless of what JS code does.
      let heap_mut = scope.heap_mut();
      heap_mut.add_root(Value::Object(global_env));
      heap_mut.add_root(Value::Object(global_this));
      heap_mut.add_root(Value::Object(object_prototype));
      heap_mut.add_root(Value::String(key_prototype));
      heap_mut.add_root(Value::String(key_constructor));
      heap_mut.add_root(Value::String(key_name));
      heap_mut.add_root(Value::String(key_object));
      heap_mut.add_root(Value::String(key_undefined));
      heap_mut.add_root(Value::Symbol(sym_function_id));
      heap_mut.add_root(Value::Symbol(sym_function_env));
      heap_mut.add_root(Value::String(type_error_str));
      heap_mut.add_root(Value::Object(object_ctor));

      (
        global_env,
        global_this,
        object_prototype,
        key_prototype,
        key_constructor,
        key_name,
        sym_function_id,
        sym_function_env,
        type_error_str,
        functions,
      )
    };

    Ok(Self {
      vm,
      global_env,
      global_this,
      object_prototype,
      key_prototype,
      key_constructor,
      key_name,
      sym_function_id,
      sym_function_env,
      type_error: Value::String(type_error_str),
      functions,
    })
  }

  fn init_object_constructor(
    scope: &mut Scope<'_>,
    sym_function_id: GcSymbol,
    sym_function_env: GcSymbol,
    global_env: GcObject,
    object_prototype: GcObject,
    key_prototype: GcString,
    key_constructor: GcString,
    key_name: GcString,
    key_object: GcString,
  ) -> Result<(GcObject, Vec<FunctionData<'a>>), VmError> {
    let mut functions: Vec<FunctionData<'a>> = Vec::new();
    functions.push(FunctionData {
      kind: FunctionKind::NativeObject,
    });
    let fn_id = 0u64;

    let object_ctor = scope.alloc_object()?;
    // [[FunctionId]]
    Self::define_data_property(
      scope,
      object_ctor,
      PropertyKey::from_symbol(sym_function_id),
      Value::Number(fn_id as f64),
    )?;
    // [[FunctionEnv]]
    Self::define_data_property(
      scope,
      object_ctor,
      PropertyKey::from_symbol(sym_function_env),
      Value::Object(global_env),
    )?;

    // Object.prototype
    Self::define_data_property(
      scope,
      object_ctor,
      PropertyKey::from_string(key_prototype),
      Value::Object(object_prototype),
    )?;

    // Object.prototype.constructor = Object
    Self::define_data_property(
      scope,
      object_prototype,
      PropertyKey::from_string(key_constructor),
      Value::Object(object_ctor),
    )?;

    // Object.name = "Object"
    Self::define_data_property(
      scope,
      object_ctor,
      PropertyKey::from_string(key_name),
      Value::String(key_object),
    )?;

    Ok((object_ctor, functions))
  }

  fn define_data_property(
    scope: &mut Scope<'_>,
    obj: GcObject,
    key: PropertyKey,
    value: Value,
  ) -> Result<(), VmError> {
    scope.define_property(
      obj,
      key,
      PropertyDescriptor {
        enumerable: true,
        configurable: true,
        kind: PropertyKind::Data {
          value,
          writable: true,
        },
      },
    )
  }

  fn get_property(heap: &Heap, obj: GcObject, key: &PropertyKey) -> Result<Value, VmError> {
    let mut cur = Some(obj);
    while let Some(o) = cur {
      if let Some(v) = heap.object_get_own_data_property_value(o, key)? {
        return Ok(v);
      }
      cur = heap.object_prototype(o)?;
    }
    Ok(Value::Undefined)
  }

  fn run(&mut self, scope: &mut Scope<'_>, ast: &'a Node<TopLevel>) -> Result<(), VmError> {
    let ctx = ExecCtx {
      env: self.global_env,
      this: Value::Object(self.global_this),
    };

    for stmt in ast.stx.body.iter() {
      match self.exec_stmt(scope, ctx, stmt)? {
        Control::Normal => {}
        Control::Return(_) => {
          return Err(VmError::Unimplemented(
            "top-level return is not valid in scripts",
          ))
        }
      }
    }

    Ok(())
  }

  fn exec_stmt(&mut self, scope: &mut Scope<'_>, ctx: ExecCtx, stmt: &'a Node<Stmt>) -> Result<Control, VmError> {
    self.vm.tick()?;

    match stmt.stx.as_ref() {
      Stmt::Block(block) => {
        for inner in block.stx.body.iter() {
          match self.exec_stmt(scope, ctx, inner)? {
            Control::Normal => {}
            r @ Control::Return(_) => return Ok(r),
          }
        }
        Ok(Control::Normal)
      }
      Stmt::Expr(expr_stmt) => {
        let _ = self.eval_expr(scope, ctx, &expr_stmt.stx.expr)?;
        Ok(Control::Normal)
      }
      Stmt::If(if_stmt) => {
        let test = self.eval_expr(scope, ctx, &if_stmt.stx.test)?;
        if scope.heap().to_boolean(test)? {
          self.exec_stmt(scope, ctx, &if_stmt.stx.consequent)
        } else if let Some(alt) = &if_stmt.stx.alternate {
          self.exec_stmt(scope, ctx, alt)
        } else {
          Ok(Control::Normal)
        }
      }
      Stmt::While(while_stmt) => {
        loop {
          let cond = self.eval_expr(scope, ctx, &while_stmt.stx.condition)?;
          if !scope.heap().to_boolean(cond)? {
            break;
          }
          match self.exec_stmt(scope, ctx, &while_stmt.stx.body)? {
            Control::Normal => {}
            r @ Control::Return(_) => return Ok(r),
          }
        }
        Ok(Control::Normal)
      }
      Stmt::Return(ret) => {
        let value = match &ret.stx.value {
          Some(expr) => self.eval_expr(scope, ctx, expr)?,
          None => Value::Undefined,
        };
        Ok(Control::Return(value))
      }
      Stmt::Throw(thr) => {
        let value = self.eval_expr(scope, ctx, &thr.stx.value)?;
        Err(VmError::Throw(value))
      }
      Stmt::VarDecl(var) => self.exec_var_decl(scope, ctx, var),
      Stmt::FunctionDecl(func) => self.exec_function_decl(scope, ctx, func),

      _ => Err(VmError::Unimplemented("unsupported statement kind")),
    }
  }

  fn exec_var_decl(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    var: &'a Node<VarDecl>,
  ) -> Result<Control, VmError> {
    match var.stx.mode {
      VarDeclMode::Var => {}
      _ => return Err(VmError::Unimplemented("only `var` declarations are supported")),
    }

    for decl in var.stx.declarators.iter() {
      let pat = &decl.pattern.stx.pat;
      let name = match pat.stx.as_ref() {
        parse_js::ast::expr::pat::Pat::Id(id) => id.stx.name.as_str(),
        _ => return Err(VmError::Unimplemented("only `var x` is supported")),
      };

      let value = match &decl.initializer {
        Some(expr) => self.eval_expr(scope, ctx, expr)?,
        None => Value::Undefined,
      };
      self.declare_in_env(scope, ctx.env, name, value)?;
    }

    Ok(Control::Normal)
  }

  fn exec_function_decl(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    func: &'a Node<FuncDecl>,
  ) -> Result<Control, VmError> {
    let name = func
      .stx
      .name
      .as_ref()
      .ok_or(VmError::Unimplemented("anonymous function declarations"))?
      .stx
      .name
      .as_str();

    let fn_obj = self.new_user_function(scope, ctx, Some(name), &func.stx.function)?;
    self.declare_in_env(scope, ctx.env, name, Value::Object(fn_obj))?;
    Ok(Control::Normal)
  }

  fn eval_expr(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    expr: &'a Node<Expr>,
  ) -> Result<Value, VmError> {
    self.vm.tick()?;

    match expr.stx.as_ref() {
      Expr::Id(id) => self.get_identifier(scope, ctx.env, &id.stx),
      Expr::This(_) => Ok(ctx.this),

      Expr::LitNum(n) => Ok(Value::Number(n.stx.value.0)),
      Expr::LitBool(b) => Ok(Value::Bool(b.stx.value)),
      Expr::LitNull(_n) => Ok(Value::Null),
      Expr::LitStr(s) => Ok(Value::String(scope.alloc_string(&s.stx.value)?)),

      Expr::Member(member) => self.eval_member(scope, ctx, &member.stx),
      Expr::ComputedMember(member) => self.eval_computed_member(scope, ctx, &member.stx),

      Expr::Binary(binary) => self.eval_binary(scope, ctx, &binary.stx),
      Expr::Call(call) => self.eval_call(scope, ctx, &call.stx),
      Expr::Unary(unary) => self.eval_unary(scope, ctx, &unary.stx),

      Expr::Func(func) => self.eval_func_expr(scope, ctx, &func.stx),

      // Patterns are not expressions (except as assignment targets, handled elsewhere).
      Expr::IdPat(_) | Expr::ArrPat(_) | Expr::ObjPat(_) => {
        Err(VmError::Unimplemented("pattern expression in value position"))
      }

      _ => Err(VmError::Unimplemented("unsupported expression kind")),
    }
  }

  fn eval_member(&mut self, scope: &mut Scope<'_>, ctx: ExecCtx, member: &'a MemberExpr) -> Result<Value, VmError> {
    if member.optional_chaining {
      return Err(VmError::Unimplemented("optional chaining"));
    }

    let obj = self.eval_expr(scope, ctx, &member.left)?;
    let Value::Object(obj) = obj else {
      return Err(VmError::Throw(self.type_error));
    };

    // Member access does not allocate; allocate the key eagerly anyway for simplicity.
    let key = scope.alloc_string(&member.right)?;
    Self::get_property(scope.heap(), obj, &PropertyKey::from_string(key))
  }

  fn eval_computed_member(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    member: &'a ComputedMemberExpr,
  ) -> Result<Value, VmError> {
    if member.optional_chaining {
      return Err(VmError::Unimplemented("optional chaining"));
    }

    let obj = self.eval_expr(scope, ctx, &member.object)?;
    let Value::Object(obj) = obj else {
      return Err(VmError::Throw(self.type_error));
    };

    // Evaluate key and convert through `ToPropertyKey`.
    let key_value = self.eval_expr(scope, ctx, &member.member)?;
    let key = scope.heap_mut().to_property_key(key_value)?;
    Self::get_property(scope.heap(), obj, &key)
  }

  fn eval_binary(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    binary: &'a BinaryExpr,
  ) -> Result<Value, VmError> {
    use OperatorName::*;

    match binary.operator {
      Assignment => {
        let rhs = self.eval_expr(scope, ctx, &binary.right)?;
        self.eval_assign(scope, ctx, &binary.left, rhs)
      }
      LogicalOr => {
        let left = self.eval_expr(scope, ctx, &binary.left)?;
        if scope.heap().to_boolean(left)? {
          Ok(left)
        } else {
          self.eval_expr(scope, ctx, &binary.right)
        }
      }
      Addition => {
        let left = self.eval_expr(scope, ctx, &binary.left)?;
        let right = self.eval_expr(scope, ctx, &binary.right)?;
        self.op_add(scope, left, right)
      }
      Multiplication => {
        let left = self.eval_expr(scope, ctx, &binary.left)?;
        let right = self.eval_expr(scope, ctx, &binary.right)?;
        self.op_mul(scope, left, right)
      }
      StrictEquality => {
        let left = self.eval_expr(scope, ctx, &binary.left)?;
        let right = self.eval_expr(scope, ctx, &binary.right)?;
        Ok(Value::Bool(self.strict_eq(scope.heap(), left, right)?))
      }
      StrictInequality => {
        let left = self.eval_expr(scope, ctx, &binary.left)?;
        let right = self.eval_expr(scope, ctx, &binary.right)?;
        Ok(Value::Bool(!self.strict_eq(scope.heap(), left, right)?))
      }
      _ => Err(VmError::Unimplemented("unsupported binary operator")),
    }
  }

  fn eval_assign(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    target: &'a Node<Expr>,
    value: Value,
  ) -> Result<Value, VmError> {
    match target.stx.as_ref() {
      Expr::IdPat(id) => {
        self.set_identifier(scope, ctx.env, &id.stx, value)?;
        Ok(value)
      }
      Expr::Id(id) => {
        // (Shouldn't happen in strict ECMAScript parse mode, but accept anyway.)
        self.set_identifier(scope, ctx.env, &IdPat { name: id.stx.name.clone() }, value)?;
        Ok(value)
      }
      Expr::Member(member) => {
        if member.stx.optional_chaining {
          return Err(VmError::Unimplemented("optional chaining assignment"));
        }
        let obj = self.eval_expr(scope, ctx, &member.stx.left)?;
        let Value::Object(obj) = obj else {
          return Err(VmError::Throw(self.type_error));
        };
        let key = scope.alloc_string(&member.stx.right)?;
        Self::define_data_property(
          scope,
          obj,
          PropertyKey::from_string(key),
          value,
        )?;
        Ok(value)
      }
      Expr::ComputedMember(member) => {
        if member.stx.optional_chaining {
          return Err(VmError::Unimplemented("optional chaining assignment"));
        }
        let obj = self.eval_expr(scope, ctx, &member.stx.object)?;
        let Value::Object(obj) = obj else {
          return Err(VmError::Throw(self.type_error));
        };
        let key_value = self.eval_expr(scope, ctx, &member.stx.member)?;
        let key = scope.heap_mut().to_property_key(key_value)?;
        Self::define_data_property(scope, obj, key, value)?;
        Ok(value)
      }
      _ => Err(VmError::Unimplemented("invalid assignment target")),
    }
  }

  fn eval_call(&mut self, scope: &mut Scope<'_>, ctx: ExecCtx, call: &'a CallExpr) -> Result<Value, VmError> {
    if call.optional_chaining {
      return Err(VmError::Unimplemented("optional chaining call"));
    }

    // Determine callee + this binding.
    let (callee, this_arg) = match call.callee.stx.as_ref() {
      Expr::Member(member) => {
        if member.stx.optional_chaining {
          return Err(VmError::Unimplemented("optional chaining call"));
        }
        let obj_value = self.eval_expr(scope, ctx, &member.stx.left)?;
        let Value::Object(obj) = obj_value else {
          return Err(VmError::Throw(self.type_error));
        };
        let key = scope.alloc_string(&member.stx.right)?;
        let callee = Self::get_property(scope.heap(), obj, &PropertyKey::from_string(key))?;
        (callee, Value::Object(obj))
      }
      _ => (self.eval_expr(scope, ctx, &call.callee)?, Value::Object(self.global_this)),
    };

    let mut args: Vec<Value> = Vec::new();
    args
      .try_reserve(call.arguments.len())
      .map_err(|_| VmError::OutOfMemory)?;
    for arg in call.arguments.iter() {
      if arg.stx.spread {
        return Err(VmError::Unimplemented("spread in call arguments"));
      }
      args.push(self.eval_expr(scope, ctx, &arg.stx.value)?);
    }

    self.call_function(scope, callee, this_arg, &args)
  }

  fn eval_unary(&mut self, scope: &mut Scope<'_>, ctx: ExecCtx, unary: &'a UnaryExpr) -> Result<Value, VmError> {
    match unary.operator {
      OperatorName::New => self.eval_new(scope, ctx, &unary.argument),
      _ => Err(VmError::Unimplemented("unsupported unary operator")),
    }
  }

  fn eval_new(&mut self, scope: &mut Scope<'_>, ctx: ExecCtx, arg: &'a Node<Expr>) -> Result<Value, VmError> {
    // `new` binds more tightly than call in the parse-js AST: `new Foo(x)` is
    // represented as `Unary(New, Call(Foo, [x]))`.
    let (ctor_expr, args_exprs): (&Node<Expr>, Option<&[Node<parse_js::ast::expr::CallArg>]>) =
      match arg.stx.as_ref() {
        Expr::Call(call) => (&call.stx.callee, Some(call.stx.arguments.as_slice())),
        _ => (arg, None),
      };

    let ctor_value = self.eval_expr(scope, ctx, ctor_expr)?;
    let Value::Object(ctor_obj) = ctor_value else {
      return Err(VmError::Throw(self.type_error));
    };

    let mut args: Vec<Value> = Vec::new();
    if let Some(args_exprs) = args_exprs {
      args
        .try_reserve(args_exprs.len())
        .map_err(|_| VmError::OutOfMemory)?;
      for arg in args_exprs {
        if arg.stx.spread {
          return Err(VmError::Unimplemented("spread in constructor arguments"));
        }
        args.push(self.eval_expr(scope, ctx, &arg.stx.value)?);
      }
    }

    self.construct(scope, ctor_obj, &args)
  }

  fn eval_func_expr(&mut self, scope: &mut Scope<'_>, ctx: ExecCtx, func: &'a FuncExpr) -> Result<Value, VmError> {
    let name = func.name.as_ref().map(|n| n.stx.name.as_str());
    let obj = self.new_user_function(scope, ctx, name, &func.func)?;
    Ok(Value::Object(obj))
  }

  fn new_user_function(
    &mut self,
    scope: &mut Scope<'_>,
    ctx: ExecCtx,
    name: Option<&str>,
    func: &'a Node<Func>,
  ) -> Result<GcObject, VmError> {
    // Allocate the function object + its default `prototype` object.
    let fn_obj = scope.alloc_object()?;
    let proto_obj = scope.alloc_object_with_prototype(Some(self.object_prototype))?;

    // Store function metadata.
    let fn_name = match name {
      Some(n) => Some(scope.alloc_string(n)?),
      None => None,
    };

    let id = self.functions.len() as u64;
    self.functions.push(FunctionData {
      kind: FunctionKind::User { func },
    });

    Self::define_data_property(
      scope,
      fn_obj,
      PropertyKey::from_symbol(self.sym_function_id),
      Value::Number(id as f64),
    )?;
    Self::define_data_property(
      scope,
      fn_obj,
      PropertyKey::from_symbol(self.sym_function_env),
      Value::Object(ctx.env),
    )?;

    // fn.prototype = proto_obj
    Self::define_data_property(
      scope,
      fn_obj,
      PropertyKey::from_string(self.key_prototype),
      Value::Object(proto_obj),
    )?;

    // proto_obj.constructor = fn_obj
    Self::define_data_property(
      scope,
      proto_obj,
      PropertyKey::from_string(self.key_constructor),
      Value::Object(fn_obj),
    )?;

    // fn.name = "<name>"
    if let Some(fn_name) = fn_name {
      Self::define_data_property(
        scope,
        fn_obj,
        PropertyKey::from_string(self.key_name),
        Value::String(fn_name),
      )?;
    }

    Ok(fn_obj)
  }

  fn get_identifier(&mut self, scope: &mut Scope<'_>, env: GcObject, id: &'a IdExpr) -> Result<Value, VmError> {
    let key = scope.alloc_string(&id.name)?;
    Ok(Self::get_property(
      scope.heap(),
      env,
      &PropertyKey::from_string(key),
    )?)
  }

  fn set_identifier(&mut self, scope: &mut Scope<'_>, env: GcObject, id: &IdPat, value: Value) -> Result<(), VmError> {
    let key = scope.alloc_string(&id.name)?;
    let key = PropertyKey::from_string(key);

    // Find the environment record that already defines this binding.
    let mut cur = Some(env);
    while let Some(o) = cur {
      if scope.heap().object_get_own_property(o, &key)?.is_some() {
        return Self::define_data_property(scope, o, key, value);
      }
      cur = scope.heap().object_prototype(o)?;
    }

    // Sloppy-mode fallback: create a global binding.
    Self::define_data_property(scope, self.global_env, key, value)
  }

  fn declare_in_env(
    &mut self,
    scope: &mut Scope<'_>,
    env: GcObject,
    name: &str,
    value: Value,
  ) -> Result<(), VmError> {
    let key = scope.alloc_string(name)?;
    Self::define_data_property(
      scope,
      env,
      PropertyKey::from_string(key),
      value,
    )
  }

  fn call_function(
    &mut self,
    scope: &mut Scope<'_>,
    callee: Value,
    this_arg: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    let Value::Object(fn_obj) = callee else {
      return Err(VmError::Throw(self.type_error));
    };

    let id_desc = scope
      .heap()
      .object_get_own_property(fn_obj, &PropertyKey::from_symbol(self.sym_function_id))?
      .ok_or_else(|| VmError::Throw(self.type_error))?;
    let id = match id_desc.kind {
      vm_js::PropertyKind::Data { value, .. } => match value {
        Value::Number(n) => n as usize,
        _ => return Err(VmError::Throw(self.type_error)),
      },
      _ => return Err(VmError::Throw(self.type_error)),
    };

    let Some(func) = self.functions.get(id) else {
      return Err(VmError::Throw(self.type_error));
    };

    match &func.kind {
      FunctionKind::NativeObject => {
        // `Object(...)` behaves like `new Object()` for our current needs.
        if !args.is_empty() {
          // TODO: `Object(value)` should box primitives; we don't need it yet.
        }
        Ok(Value::Object(
          scope.alloc_object_with_prototype(Some(self.object_prototype))?,
        ))
      }
      FunctionKind::User { func } => self.call_user_function(scope, fn_obj, func, this_arg, args),
    }
  }

  fn call_user_function(
    &mut self,
    scope: &mut Scope<'_>,
    fn_obj: GcObject,
    func: &'a Node<Func>,
    this_arg: Value,
    args: &[Value],
  ) -> Result<Value, VmError> {
    if func.stx.arrow || func.stx.async_ || func.stx.generator {
      return Err(VmError::Unimplemented(
        "arrow/async/generator functions are not supported",
      ));
    }

    // Resolve the function's captured environment.
    let env_desc = scope
      .heap()
      .object_get_own_property(fn_obj, &PropertyKey::from_symbol(self.sym_function_env))?
      .ok_or_else(|| VmError::Throw(self.type_error))?;
    let captured_env = match env_desc.kind {
      vm_js::PropertyKind::Data { value, .. } => match value {
        Value::Object(o) => o,
        _ => return Err(VmError::Throw(self.type_error)),
      },
      _ => return Err(VmError::Throw(self.type_error)),
    };

    let local_env = scope.alloc_object_with_prototype(Some(captured_env))?;

    // Root the new environment + this for the duration of the call.
    let mut call_scope = scope.reborrow();
    call_scope.push_root(Value::Object(local_env));
    call_scope.push_root(this_arg);

    // Bind parameters.
    for (idx, param) in func.stx.parameters.iter().enumerate() {
      if param.stx.rest {
        return Err(VmError::Unimplemented("rest parameters"));
      }
      let pat = &param.stx.pattern.stx.pat;
      let name = match pat.stx.as_ref() {
        parse_js::ast::expr::pat::Pat::Id(id) => id.stx.name.as_str(),
        _ => return Err(VmError::Unimplemented("non-identifier parameters")),
      };
      let value = args.get(idx).copied().unwrap_or(Value::Undefined);
      self.declare_in_env(&mut call_scope, local_env, name, value)?;
    }

    let ctx = ExecCtx {
      env: local_env,
      this: this_arg,
    };

    let body = func
      .stx
      .body
      .as_ref()
      .ok_or(VmError::Unimplemented("function without body"))?;

    match body {
      FuncBody::Block(stmts) => {
        for stmt in stmts.iter() {
          match self.exec_stmt(&mut call_scope, ctx, stmt)? {
            Control::Normal => {}
            Control::Return(v) => return Ok(v),
          }
        }
        Ok(Value::Undefined)
      }
      FuncBody::Expression(expr) => self.eval_expr(&mut call_scope, ctx, expr),
    }
  }

  fn construct(&mut self, scope: &mut Scope<'_>, ctor_obj: GcObject, args: &[Value]) -> Result<Value, VmError> {
    // Built-in Object: allocate and return directly.
    if self.is_native_object_ctor(scope.heap(), ctor_obj)? {
      return Ok(Value::Object(
        scope.alloc_object_with_prototype(Some(self.object_prototype))?,
      ));
    }

    // Determine prototype to install.
    let proto_val =
      Self::get_property(scope.heap(), ctor_obj, &PropertyKey::from_string(self.key_prototype))?;
    let proto = match proto_val {
      Value::Object(o) => o,
      _ => self.object_prototype,
    };

    let instance = scope.alloc_object_with_prototype(Some(proto))?;

    // Call constructor with `this = instance`.
    let ret = self.call_function(scope, Value::Object(ctor_obj), Value::Object(instance), args)?;

    // Return value overrides `this` only when it's an object.
    match ret {
      Value::Object(_) => Ok(ret),
      _ => Ok(Value::Object(instance)),
    }
  }

  fn is_native_object_ctor(&self, heap: &Heap, obj: GcObject) -> Result<bool, VmError> {
    let Some(desc) = heap
      .object_get_own_property(obj, &PropertyKey::from_symbol(self.sym_function_id))?
    else {
      return Ok(false);
    };
    let vm_js::PropertyKind::Data { value, .. } = desc.kind else {
      return Ok(false);
    };
    match value {
      Value::Number(n) => Ok(n as u64 == 0),
      _ => Ok(false),
    }
  }

  fn strict_eq(&self, heap: &Heap, a: Value, b: Value) -> Result<bool, VmError> {
    Ok(match (a, b) {
      (Value::Undefined, Value::Undefined) | (Value::Null, Value::Null) => true,
      (Value::Bool(a), Value::Bool(b)) => a == b,
      (Value::Number(a), Value::Number(b)) => a == b,
      (Value::String(a), Value::String(b)) => heap.get_string(a)?.as_code_units() == heap.get_string(b)?.as_code_units(),
      (Value::Symbol(a), Value::Symbol(b)) => a == b,
      (Value::Object(a), Value::Object(b)) => a == b,
      _ => false,
    })
  }

  fn op_add(&mut self, scope: &mut Scope<'_>, a: Value, b: Value) -> Result<Value, VmError> {
    // If either operand is a string, do string concatenation using ToString.
    if matches!(a, Value::String(_)) || matches!(b, Value::String(_)) {
      let a = scope.heap_mut().to_string(a)?;
      let b = scope.heap_mut().to_string(b)?;

      let a_units = scope.heap().get_string(a)?.as_code_units();
      let b_units = scope.heap().get_string(b)?.as_code_units();
      let mut units: Vec<u16> = Vec::new();
      units
        .try_reserve_exact(a_units.len() + b_units.len())
        .map_err(|_| VmError::OutOfMemory)?;
      units.extend_from_slice(a_units);
      units.extend_from_slice(b_units);
      let s = scope.alloc_string_from_u16_vec(units)?;
      return Ok(Value::String(s));
    }

    Ok(Value::Number(self.to_number(scope, a)? + self.to_number(scope, b)?))
  }

  fn op_mul(&mut self, scope: &mut Scope<'_>, a: Value, b: Value) -> Result<Value, VmError> {
    Ok(Value::Number(self.to_number(scope, a)? * self.to_number(scope, b)?))
  }

  fn to_number(&mut self, scope: &mut Scope<'_>, v: Value) -> Result<f64, VmError> {
    Ok(match v {
      Value::Number(n) => n,
      Value::Bool(true) => 1.0,
      Value::Bool(false) => 0.0,
      Value::Null => 0.0,
      Value::Undefined => f64::NAN,
      Value::String(s) => scope
        .heap()
        .get_string(s)?
        .to_utf8_lossy()
        .trim()
        .parse::<f64>()
        .unwrap_or(f64::NAN),
      Value::Symbol(_) | Value::Object(_) => {
        return Err(VmError::Unimplemented("ToNumber(object)"));
      }
    })
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use vm_js::TerminationReason;
  use vm_js::Termination;

  #[test]
  fn new_object_and_property_set_get() {
    let src = r#"
      var o = new Object();
      o.x = 42;
      if (o.x === 42) {
        // ok
      } else {
        throw "bad";
      }
    "#;

    let limits = HeapLimits::new(1024 * 1024, 1024 * 1024);
    let budget = Budget::unlimited(100);
    execute_script(src, limits, budget).unwrap();
  }

  #[test]
  fn sta_js_snippet_executes() {
    let src = include_str!("../../test262-semantic/data/harness/sta.js");
    let limits = HeapLimits::new(4 * 1024 * 1024, 4 * 1024 * 1024);
    let budget = Budget::unlimited(100);
    execute_script(src, limits, budget).unwrap();
  }

  #[test]
  fn while_true_is_interruptible_by_fuel() {
    let src = "while (true) {}";
    let limits = HeapLimits::new(1024 * 1024, 1024 * 1024);
    let budget = Budget {
      fuel: Some(10),
      deadline: None,
      check_time_every: 100,
    };

    let err = execute_script(src, limits, budget).unwrap_err();
    match err {
      VmError::Termination(Termination { reason, .. }) => assert_eq!(reason, TerminationReason::OutOfFuel),
      other => panic!("expected termination, got {other:?}"),
    }
  }
}
