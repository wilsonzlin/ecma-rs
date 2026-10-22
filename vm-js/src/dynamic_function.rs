//! `CreateDynamicFunction` (ECMA-262 §20.2.1.1.1) — `Function` / `GeneratorFunction` /
//! `AsyncFunction` constructors.

use crate::error_object::new_syntax_error_object;
use crate::function::ThisMode;
use crate::property::{PropertyDescriptor, PropertyKey, PropertyKind};
use crate::source::SourceText;
use crate::spec_ops::get_prototype_from_constructor;
use crate::vm::{EcmaFunctionKind, ParsedProgram};
use crate::{GcObject, Scope, Value, Vm, VmError, VmHostHooks};
use parse_js::ast::expr::Expr;
use parse_js::ast::func::{Func, FuncBody};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::sync::Arc;

/// Kind of dynamic function created by `CreateDynamicFunction`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[allow(dead_code)] // Generator/Async ready for GeneratorFunction / AsyncFunction constructors.
pub(crate) enum DynamicFunctionKind {
  Normal,
  Generator,
  Async,
}

/// `CreateDynamicFunction(ctor, newTarget, kind, parameterArgs, bodyArg)` (partial).
///
/// Implements the high-value path used by `%Function%`:
/// - `ToString` on parameter/body arguments (via `ToPrimitive` for objects)
/// - parse as a parenthesized `FunctionExpression` / `GeneratorExpression` / `AsyncFunctionExpression`
/// - `OrdinaryFunctionCreate` + `SetFunctionName("anonymous")` + `MakeConstructor` (normal)
/// - `[[Environment]]` is empty (lookups fall through to the global object; matches GlobalEnv for
///   the manifested corpus)
///
/// Note: the spec parses FormalParameters and FunctionBody separately before the full expression
/// (so e.g. `new Function("/*", "*/ ) {")` is a SyntaxError). This implementation currently relies
/// on a single full-expression parse, which covers the common cases in the language-core suites.
pub(crate) fn create_dynamic_function(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _hooks: &mut dyn VmHostHooks,
  ctor: GcObject,
  new_target: Value,
  kind: DynamicFunctionKind,
  args: &[Value],
) -> Result<Value, VmError> {
  let intr = vm.intrinsics().ok_or(VmError::Unimplemented(
    "CreateDynamicFunction requires intrinsics",
  ))?;

  let new_target = match new_target {
    Value::Undefined => Value::Object(ctor),
    other => other,
  };

  // Split trailing bodyArg from preceding parameterArgs (§20.2.1.1).
  let (param_args, body_arg) = if args.is_empty() {
    (&[][..], Value::String(scope.alloc_string("")?))
  } else {
    let last = args.len() - 1;
    (&args[..last], args[last])
  };

  let mut param_strings: Vec<String> = Vec::new();
  param_strings
    .try_reserve_exact(param_args.len())
    .map_err(|_| VmError::OutOfMemory)?;
  for &arg in param_args {
    let s = value_to_string_for_source(vm, scope, arg)?;
    let utf8 = scope.heap().get_string(s)?.to_utf8_lossy();
    param_strings.push(utf8);
  }
  let body_s = value_to_string_for_source(vm, scope, body_arg)?;
  let body_string = scope.heap().get_string(body_s)?.to_utf8_lossy();

  let param_string = param_strings.join(",");
  let body_parse_string = format!("\n{body_string}\n");

  let (prefix, fallback_proto) = match kind {
    DynamicFunctionKind::Normal => ("function", intr.function_prototype()),
    DynamicFunctionKind::Generator => ("function*", intr.generator_function_prototype()),
    DynamicFunctionKind::Async => ("async function", intr.async_function_prototype()),
  };

  // Spec sourceText (without the parentheses we add for expression context):
  //   prefix + " anonymous(" + P + "\n) {" + bodyParseString + "}"
  let inner = format!("{prefix} anonymous({param_string}\n) {{{body_parse_string}}}");
  // Parenthesize so `function …` parses as a FunctionExpression, not a declaration.
  let source_text = format!("({inner})");

  let source = Arc::new(SourceText::new("<Function>", source_text.clone()));
  let opts = ParseOptions {
    dialect: Dialect::Ecma,
    source_type: SourceType::Script,
  };
  let top = match parse_with_options(&source.text, opts) {
    Ok(top) => top,
    Err(err) => {
      let msg = err.to_string();
      let err_val = new_syntax_error_object(scope, &intr, &msg)?;
      return Err(VmError::Throw(err_val));
    }
  };

  let program = Arc::new(ParsedProgram { top });

  // Validate flavor flags and collect metadata before moving `program` onto the VM stack.
  let (span_start, span_end, is_strict, length) = {
    let func_node =
      extract_function_expr(&program.top.stx.body).ok_or_else(|| match new_syntax_error_object(
        scope,
        &intr,
        "Function constructor produced invalid syntax",
      ) {
        Ok(v) => VmError::Throw(v),
        Err(e) => e,
      })?;

    match kind {
      DynamicFunctionKind::Normal if func_node.stx.async_ || func_node.stx.generator => {
        let err_val = new_syntax_error_object(scope, &intr, "Function constructor kind mismatch")?;
        return Err(VmError::Throw(err_val));
      }
      DynamicFunctionKind::Generator if !func_node.stx.generator || func_node.stx.async_ => {
        let err_val = new_syntax_error_object(scope, &intr, "GeneratorFunction kind mismatch")?;
        return Err(VmError::Throw(err_val));
      }
      DynamicFunctionKind::Async if !func_node.stx.async_ || func_node.stx.generator => {
        let err_val = new_syntax_error_object(scope, &intr, "AsyncFunction kind mismatch")?;
        return Err(VmError::Throw(err_val));
      }
      _ => {}
    }

    let is_strict = match &func_node.stx.body {
      Some(FuncBody::Block(stmts)) => detect_use_strict_directive(stmts),
      Some(FuncBody::Expression(_)) => false,
      None => {
        let err_val = new_syntax_error_object(scope, &intr, "Function without body")?;
        return Err(VmError::Throw(err_val));
      }
    };
    (
      func_node.loc.start_u32(),
      func_node.loc.end_u32(),
      is_strict,
      function_length(&func_node.stx),
    )
  };

  let func_proto = get_prototype_from_constructor(vm, scope, new_target, fallback_proto)?;
  let this_mode = if is_strict {
    ThisMode::Strict
  } else {
    ThisMode::Global
  };

  let name_s = scope.alloc_string("anonymous")?;
  scope.push_root(Value::String(name_s))?;
  scope.push_root(Value::Object(func_proto))?;

  vm.push_program(program.clone());
  let code_id = {
    let func_node = extract_function_expr(&program.top.stx.body).expect("validated above");
    match vm.register_ecma_function(
      source,
      span_start,
      span_end,
      EcmaFunctionKind::Expr,
      func_node,
    ) {
      Ok(id) => id,
      Err(err) => {
        vm.pop_program();
        return Err(err);
      }
    }
  };
  // Keep the program alive via EcmaFunctionCode; drop the stack entry.
  vm.pop_program();

  let is_constructable = matches!(kind, DynamicFunctionKind::Normal);
  let object_prototype = if is_constructable {
    Some(intr.object_prototype())
  } else {
    None
  };
  let func_obj = scope.alloc_ecma_function(
    code_id,
    is_constructable,
    name_s,
    length,
    this_mode,
    is_strict,
    // GlobalEnv: empty outer env; identifier lookup falls through to the global object.
    None,
    object_prototype,
  )?;
  scope.push_root(Value::Object(func_obj))?;

  scope
    .heap_mut()
    .object_set_prototype(func_obj, Some(func_proto))?;

  // Prefer the constructor's [[Realm]] (set on `%Function%` at realm init); fall back to looking
  // up `globalThis` is unnecessary once that is wired.
  if let Some(realm) = scope.heap().get_function_realm(ctor)? {
    scope.heap_mut().set_function_realm(func_obj, realm)?;
  }
  let job_realm = scope
    .heap()
    .get_function_job_realm(ctor)
    .or(vm.current_realm());
  if let Some(job_realm) = job_realm {
    scope
      .heap_mut()
      .set_function_job_realm(func_obj, job_realm)?;
  }

  match kind {
    DynamicFunctionKind::Normal => {}
    DynamicFunctionKind::Generator => {
      // Replace MakeConstructor-shaped `.prototype` with a GeneratorPrototype-based one.
      let gen_proto = intr.generator_prototype();
      let proto_obj = scope.alloc_object_with_prototype(Some(gen_proto))?;
      scope.push_root(Value::Object(proto_obj))?;
      let key_s = scope.alloc_string("prototype")?;
      scope.define_property(
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
    DynamicFunctionKind::Async => {
      // Async functions are not constructors and must not have a "prototype" property.
      // `alloc_ecma_function` with `is_constructable=false` already skips MakeConstructor.
    }
  }

  Ok(Value::Object(func_obj))
}

fn value_to_string_for_source(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  value: Value,
) -> Result<crate::GcString, VmError> {
  crate::spec_ops::to_string(vm, scope, value)
}

fn extract_function_expr(body: &[Node<Stmt>]) -> Option<&Node<Func>> {
  let stmt = body.first()?;
  let Stmt::Expr(expr_stmt) = &*stmt.stx else {
    return None;
  };
  match &*expr_stmt.stx.expr.stx {
    Expr::Func(func_expr) => Some(&func_expr.stx.func),
    _ => None,
  }
}

fn detect_use_strict_directive(stmts: &[Node<Stmt>]) -> bool {
  for stmt in stmts {
    let Stmt::Expr(expr_stmt) = &*stmt.stx else {
      break;
    };
    let Expr::LitStr(lit) = &*expr_stmt.stx.expr.stx else {
      break;
    };
    if lit.stx.value == "use strict" {
      return true;
    }
  }
  false
}

fn function_length(func: &Func) -> u32 {
  let mut len: u32 = 0;
  for param in func.parameters.iter() {
    if param.stx.rest || param.stx.default_value.is_some() {
      break;
    }
    len = len.saturating_add(1);
  }
  len
}
