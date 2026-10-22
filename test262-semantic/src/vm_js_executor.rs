use crate::executor::{ExecError, ExecPhase, ExecResult, Executor, JsError};
use crate::report::{ExpectedOutcome, Variant};
use crate::runner::TestCase;
use diagnostics::render::render_diagnostic;
use diagnostics::{FileId, SimpleFiles};
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use semantic_js::js::{bind_js_for_runtime, TopLevelMode};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use vm_js::format_stack_trace;
use vm_js::{
  GcObject, Heap, HeapLimits, JsRuntime, NativeFunctionId, PropertyDescriptor, PropertyKey,
  PropertyKind, Scope, SourceText, StackFrame, TerminationReason, Value, Vm, VmError, VmHost,
  VmHostHooks, VmOptions,
};

const DEFAULT_HEAP_MAX_BYTES: usize = 64 * 1024 * 1024;
const DEFAULT_HEAP_GC_THRESHOLD_BYTES: usize = 32 * 1024 * 1024;

const ASYNC_TEST_COMPLETE: &str = "Test262:AsyncTestComplete";
const ASYNC_TEST_FAILURE_PREFIX: &str = "Test262:AsyncTestFailure:";

/// Captures `print(...)` messages used by test262 `flags: [async]` / `doneprintHandle.js`.
#[derive(Debug, Default)]
struct AsyncPrintState {
  message: Option<String>,
}

/// A `test262-semantic` executor backed by the `vm-js` interpreter.
#[derive(Debug, Clone, Copy)]
pub struct VmJsExecutor {
  heap_limits: HeapLimits,
}

impl Default for VmJsExecutor {
  fn default() -> Self {
    Self {
      heap_limits: HeapLimits::new(DEFAULT_HEAP_MAX_BYTES, DEFAULT_HEAP_GC_THRESHOLD_BYTES),
    }
  }
}

impl Executor for VmJsExecutor {
  fn execute(&self, case: &TestCase, source: &str, cancel: &Arc<AtomicBool>) -> ExecResult {
    if cancel.load(Ordering::Relaxed) {
      return Err(ExecError::Cancelled);
    }

    if case.variant == Variant::Module {
      // Full module evaluation is still unsupported, but negative `phase: parse`
      // tests only need Module-grammar / binder early errors (`await` reserved,
      // etc.). Run parse+bind and stop — never execute.
      let is_negative_parse = matches!(
        &case.expected,
        ExpectedOutcome::Negative { phase, .. } if phase.eq_ignore_ascii_case("parse")
      );
      if !is_negative_parse {
        return Err(ExecError::Skipped("modules not supported".to_string()));
      }
      if let Err(err) = early_bind_syntax_errors(case, source) {
        return Err(err);
      }
      // Parsed+bound cleanly: negative test mismatches as an unexpected pass.
      return Ok(());
    }

    let is_async = case.metadata.flags.iter().any(|f| f == "async");

    let mut vm = Vm::new(VmOptions {
      interrupt_flag: Some(Arc::clone(cancel)),
      ..VmOptions::default()
    });
    // Always install the print sink; sync tests never call it. Async tests communicate
    // completion via `doneprintHandle.js` → `print('Test262:AsyncTestComplete'|Failure:…)`.
    vm.set_user_data(AsyncPrintState::default());

    let heap = Heap::new(self.heap_limits);
    let mut runtime = match vm_js::JsRuntime::new(vm, heap) {
      Ok(runtime) => runtime,
      Err(err) => {
        return Err(ExecError::Js(JsError::new(
          ExecPhase::Runtime,
          None,
          err.to_string(),
        )));
      }
    };

    if let Err(err) = runtime.register_global_native_function("print", host_print, 1) {
      return Err(ExecError::Js(JsError::new(
        ExecPhase::Runtime,
        None,
        format!("failed to install print: {err}"),
      )));
    }

    // test262 host API: `$262.createRealm` / `$262.global` (INTERPRETING.md).
    if let Err(err) = install_dollar_262(&mut runtime) {
      return Err(ExecError::Js(JsError::new(
        ExecPhase::Runtime,
        None,
        format!("failed to install $262: {err}"),
      )));
    }

    // Give the VM a useful/stable source name for stack traces.
    let file_name = if case.id.is_empty() {
      "<test262>".to_string()
    } else {
      case.id.clone()
    };

    // Parse-phase early errors (ECMA-262 static semantics) are owned by
    // `semantic-js` JS-mode binding. Negative `phase: parse` tests use
    // `$DONOTEVALUATE()`, so runtime CaseBlock instantiation never runs —
    // binder diagnostics must surface here as parse SyntaxError.
    if let Err(err) = early_bind_syntax_errors(case, source) {
      return Err(err);
    }

    let source_text = Arc::new(SourceText::new(file_name, source));

    let result = runtime.exec_script_source(source_text);

    // Cancellation should win over any other outcome (including parse/runtime errors).
    if cancel.load(Ordering::Relaxed) {
      return Err(ExecError::Cancelled);
    }

    if let Err(err) = result {
      return Err(map_vm_error(case, source, cancel, &mut runtime, err));
    }

    // Drain promise jobs enqueued by the script. For sync tests the queue is typically empty
    // (no-op). For `flags: [async]` this is what settles `asyncTest` / `$DONE` continuations.
    if let Err(err) = runtime.vm.perform_microtask_checkpoint(&mut runtime.heap) {
      if cancel.load(Ordering::Relaxed) {
        return Err(ExecError::Cancelled);
      }
      return Err(map_vm_error(case, source, cancel, &mut runtime, err));
    }

    if cancel.load(Ordering::Relaxed) {
      return Err(ExecError::Cancelled);
    }

    if !is_async {
      return Ok(());
    }

    match runtime.vm.take_user_data::<AsyncPrintState>() {
      Some(AsyncPrintState { message: Some(msg) }) if msg == ASYNC_TEST_COMPLETE => Ok(()),
      Some(AsyncPrintState { message: Some(msg) })
        if msg.starts_with(ASYNC_TEST_FAILURE_PREFIX) =>
      {
        let detail = msg[ASYNC_TEST_FAILURE_PREFIX.len()..].to_string();
        Err(ExecError::Js(JsError::new(
          ExecPhase::Runtime,
          None,
          detail,
        )))
      }
      Some(AsyncPrintState { message: Some(msg) }) => Err(ExecError::Js(JsError::new(
        ExecPhase::Runtime,
        None,
        format!("async test print: unexpected message: {msg}"),
      ))),
      _ => {
        // No `$DONE` / print after the microtask checkpoint: treat as failure. The runner's
        // per-test timeout already covers the "never settles" hang case while jobs remain.
        Err(ExecError::Js(JsError::new(
          ExecPhase::Runtime,
          None,
          "async test completed without calling $DONE / print".to_string(),
        )))
      }
    }
  }
}

fn host_print(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  args: &[Value],
) -> Result<Value, VmError> {
  let raw = args.first().copied().unwrap_or(Value::Undefined);
  // Root across ToString allocation.
  scope.push_root(raw)?;
  let s = scope.heap_mut().to_string(raw)?;
  let msg = scope.heap().get_string(s)?.to_utf8_lossy();
  if let Some(state) = vm.user_data_mut::<AsyncPrintState>() {
    state.message = Some(msg);
  }
  Ok(Value::Undefined)
}

fn host_data_desc(value: Value) -> PropertyDescriptor {
  PropertyDescriptor {
    enumerable: false,
    configurable: true,
    kind: PropertyKind::Data {
      value,
      writable: true,
    },
  }
}

/// Install `$262` on `runtime`'s primary global (`createRealm` + `global`).
fn install_dollar_262(runtime: &mut JsRuntime) -> Result<(), VmError> {
  let create_id = runtime.vm.register_native_call(host_create_realm)?;
  let global = runtime.realm().global_object();
  let mut scope = runtime.heap.scope();
  define_dollar_262_on_global(&mut runtime.vm, &mut scope, global, create_id)?;
  Ok(())
}

/// Define `$262 = { createRealm, global }` on `global` and return the `$262` object.
fn define_dollar_262_on_global(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  global: GcObject,
  create_id: NativeFunctionId,
) -> Result<GcObject, VmError> {
  scope.push_root(Value::Object(global))?;

  let dollar = scope.alloc_object()?;
  scope.push_root(Value::Object(dollar))?;
  if let Some(intr) = vm.intrinsics_for_global(global) {
    scope
      .heap_mut()
      .object_set_prototype(dollar, Some(intr.object_prototype()))?;
  }

  let create_name = scope.alloc_string("createRealm")?;
  scope.push_root(Value::String(create_name))?;
  let create_fn = scope.alloc_native_function(create_id, None, create_name, 0)?;
  scope.push_root(Value::Object(create_fn))?;

  let create_key = PropertyKey::from_string(scope.alloc_string("createRealm")?);
  scope.define_property(dollar, create_key, host_data_desc(Value::Object(create_fn)))?;

  let global_key = PropertyKey::from_string(scope.alloc_string("global")?);
  scope.define_property(dollar, global_key, host_data_desc(Value::Object(global)))?;

  let dollar_key = PropertyKey::from_string(scope.alloc_string("$262")?);
  scope.define_property(global, dollar_key, host_data_desc(Value::Object(dollar)))?;

  Ok(dollar)
}

/// `$262.createRealm()` — new realm, install `$262` on its global, return that `$262`.
fn host_create_realm(
  vm: &mut Vm,
  scope: &mut Scope<'_>,
  _host: &mut dyn VmHost,
  _hooks: &mut dyn VmHostHooks,
  _callee: GcObject,
  _this: Value,
  _args: &[Value],
) -> Result<Value, VmError> {
  let new_global = vm.create_realm(scope.heap_mut())?;
  scope.push_root(Value::Object(new_global))?;
  // Fresh call id so each realm's `createRealm` is independently dispatchable.
  let create_id = vm.register_native_call(host_create_realm)?;
  let dollar = define_dollar_262_on_global(vm, scope, new_global, create_id)?;
  Ok(Value::Object(dollar))
}

/// Runs `semantic-js` JS-mode binding and maps true early-error diagnostics to a
/// parse-phase `SyntaxError` (matching test262 `negative.phase: parse`).
///
/// Uses [`bind_js_for_runtime`] so TDZ (`BIND0003`) stays a runtime concern.
fn early_bind_syntax_errors(case: &TestCase, source: &str) -> ExecResult {
  let is_module = case.variant == Variant::Module;
  let opts = ParseOptions {
    dialect: Dialect::Ecma,
    source_type: if is_module {
      SourceType::Module
    } else {
      SourceType::Script
    },
  };
  let mut ast = match parse_with_options(source, opts) {
    Ok(ast) => ast,
    Err(err) => {
      if is_module {
        // Module execution is unsupported, so own Module parse failures here
        // (script path still defers to `vm-js` for identical Dialect/SourceType).
        let file_name = if case.id.is_empty() {
          "<test262>".to_string()
        } else {
          case.id.clone()
        };
        let mut files = SimpleFiles::new();
        let _ = files.add(file_name, source);
        let diag = err.to_diagnostic(FileId(0));
        let message = render_diagnostic(&files, &diag).trim_end().to_string();
        return Err(ExecError::Js(JsError::new(
          ExecPhase::Parse,
          Some("SyntaxError".to_string()),
          message,
        )));
      }
      // Let `vm-js` own pure script parse failures (same Dialect/SourceType) so
      // diagnostic rendering stays consistent with the execution path.
      let _ = err;
      return Ok(());
    }
  };

  let mode = if is_module {
    TopLevelMode::Module
  } else {
    TopLevelMode::Script
  };
  let (_sem, mut diags) = bind_js_for_runtime(&mut ast, mode, FileId(0));
  diags.retain(|d| d.code.as_str() != "BIND0003");
  if diags.is_empty() {
    return Ok(());
  }
  diagnostics::sort_diagnostics(&mut diags);

  let file_name = if case.id.is_empty() {
    "<test262>".to_string()
  } else {
    case.id.clone()
  };
  let mut files = SimpleFiles::new();
  let _ = files.add(file_name, source);
  let message = diags
    .iter()
    .map(|d| render_diagnostic(&files, d).trim_end().to_string())
    .collect::<Vec<_>>()
    .join("\n\n");

  Err(ExecError::Js(JsError::new(
    ExecPhase::Parse,
    Some("SyntaxError".to_string()),
    message,
  )))
}

fn map_vm_error(
  case: &TestCase,
  source: &str,
  cancel: &Arc<AtomicBool>,
  runtime: &mut vm_js::JsRuntime,
  err: VmError,
) -> ExecError {
  if cancel.load(Ordering::Relaxed) {
    return ExecError::Cancelled;
  }

  match err {
    VmError::Syntax(mut diags) => {
      diagnostics::sort_diagnostics(&mut diags);

      let file_name = if case.id.is_empty() {
        "<test262>".to_string()
      } else {
        case.id.clone()
      };
      let mut files = SimpleFiles::new();
      let _ = files.add(file_name, source);

      let message = diags
        .iter()
        .map(|d| render_diagnostic(&files, d).trim_end().to_string())
        .collect::<Vec<_>>()
        .join("\n\n");

      ExecError::Js(JsError::new(
        ExecPhase::Parse,
        Some("SyntaxError".to_string()),
        message,
      ))
    }

    VmError::Throw(thrown) => {
      let (typ, message) = describe_thrown_value(runtime, thrown);
      let stack = stack_from_frames(runtime.vm.capture_stack());
      ExecError::Js(JsError {
        phase: ExecPhase::Runtime,
        typ,
        message,
        stack,
      })
    }

    VmError::ThrowWithStack {
      value: thrown,
      stack,
    } => {
      let (typ, message) = describe_thrown_value(runtime, thrown);
      let stack = stack_from_frames(stack);
      ExecError::Js(JsError {
        phase: ExecPhase::Runtime,
        typ,
        message,
        stack,
      })
    }

    VmError::Termination(term) => match term.reason {
      TerminationReason::Interrupted
      | TerminationReason::DeadlineExceeded
      | TerminationReason::OutOfFuel => ExecError::Cancelled,

      TerminationReason::StackOverflow => ExecError::Js(JsError {
        phase: ExecPhase::Runtime,
        typ: Some("RangeError".to_string()),
        message: term.to_string(),
        stack: stack_from_frames(term.stack),
      }),

      // Chosen mapping: treat OOM as a `RangeError` (resource exhaustion), which
      // is also where we classify stack overflow.
      TerminationReason::OutOfMemory => ExecError::Js(JsError {
        phase: ExecPhase::Runtime,
        typ: Some("RangeError".to_string()),
        message: term.to_string(),
        stack: stack_from_frames(term.stack),
      }),
    },

    VmError::NotCallable
    | VmError::NotConstructable
    | VmError::PrototypeCycle
    | VmError::PropertyNotData
    | VmError::PropertyNotFound
    | VmError::TypeError(_) => ExecError::Js(JsError {
      phase: ExecPhase::Runtime,
      typ: Some("TypeError".to_string()),
      message: err.to_string(),
      stack: stack_from_frames(runtime.vm.capture_stack()),
    }),

    VmError::PrototypeChainTooDeep => ExecError::Js(JsError {
      phase: ExecPhase::Runtime,
      typ: Some("RangeError".to_string()),
      message: err.to_string(),
      stack: stack_from_frames(runtime.vm.capture_stack()),
    }),

    // Chosen mapping: treat OOM as a `RangeError` (resource exhaustion), which
    // is also where we classify stack overflow.
    VmError::OutOfMemory => ExecError::Js(JsError {
      phase: ExecPhase::Runtime,
      typ: Some("RangeError".to_string()),
      message: err.to_string(),
      stack: stack_from_frames(runtime.vm.capture_stack()),
    }),

    VmError::Unimplemented(_) => ExecError::Js(JsError {
      phase: ExecPhase::Runtime,
      typ: None,
      message: err.to_string(),
      stack: stack_from_frames(runtime.vm.capture_stack()),
    }),

    other => ExecError::Js(JsError {
      phase: ExecPhase::Runtime,
      typ: None,
      message: other.to_string(),
      stack: stack_from_frames(runtime.vm.capture_stack()),
    }),
  }
}

fn describe_thrown_value(runtime: &mut vm_js::JsRuntime, value: Value) -> (Option<String>, String) {
  // Root the thrown value while we allocate property keys so GC cannot collect
  // it out from under us.
  let mut scope = runtime.heap.scope();
  let _ = scope.push_root(value);

  match value {
    Value::Object(obj) => {
      let typ = get_object_string_data_property(&mut scope, obj, "name");
      let message = get_object_string_data_property(&mut scope, obj, "message")
        .or_else(|| typ.clone())
        .unwrap_or_else(|| "<object>".to_string());
      (typ, message)
    }

    Value::Undefined => (None, "undefined".to_string()),
    Value::Null => (None, "null".to_string()),
    Value::Bool(b) => (None, b.to_string()),
    Value::Number(n) => (None, format_js_number(n)),
    Value::BigInt(b) => (None, b.to_decimal_string()),
    Value::String(s) => {
      let msg = scope
        .heap()
        .get_string(s)
        .map(|s| s.to_utf8_lossy())
        .unwrap_or_else(|_| "<string>".to_string());
      (None, msg)
    }
    Value::Symbol(sym) => {
      let msg = scope
        .heap()
        .symbol_description(sym)
        .and_then(|desc| {
          scope
            .heap()
            .get_string(desc)
            .ok()
            .map(|s| s.to_utf8_lossy())
        })
        .map(|desc| format!("Symbol({desc})"))
        .unwrap_or_else(|| "Symbol()".to_string());
      (None, msg)
    }
  }
}

fn get_object_string_data_property(
  scope: &mut vm_js::Scope<'_>,
  obj: vm_js::GcObject,
  prop: &str,
) -> Option<String> {
  let key = PropertyKey::from_string(scope.alloc_string(prop).ok()?);
  let desc = scope.heap().get_property(obj, &key).ok().flatten()?;
  match desc.kind {
    PropertyKind::Data { value, .. } => match value {
      Value::String(s) => scope.heap().get_string(s).ok().map(|s| s.to_utf8_lossy()),
      _ => None,
    },
    PropertyKind::Accessor { .. } => None,
  }
}

fn format_js_number(n: f64) -> String {
  if n.is_nan() {
    return "NaN".to_string();
  }
  if n.is_infinite() {
    return if n.is_sign_negative() {
      "-Infinity".to_string()
    } else {
      "Infinity".to_string()
    };
  }
  // Best-effort: Rust's formatting matches JS for the common cases we care
  // about (`1`, `-0`, etc).
  n.to_string()
}

fn stack_from_frames(frames: Vec<StackFrame>) -> Option<String> {
  if frames.is_empty() {
    return None;
  }
  let formatted = format_stack_trace(&frames);
  if formatted.is_empty() {
    None
  } else {
    Some(formatted)
  }
}

#[cfg(test)]
mod tests {
  use super::*;
  use crate::frontmatter::Frontmatter;
  use crate::report::ExpectedOutcome;
  use std::path::PathBuf;

  fn test_case(id: &str) -> TestCase {
    TestCase {
      id: id.to_string(),
      path: PathBuf::from(id),
      variant: Variant::NonStrict,
      expected: ExpectedOutcome::Pass,
      metadata: Frontmatter::default(),
      body: String::new(),
    }
  }

  #[test]
  fn cancellation_flag_short_circuits() {
    let exec = VmJsExecutor::default();
    let cancel = Arc::new(AtomicBool::new(true));
    let err = exec
      .execute(&test_case("cancel.js"), "1;", &cancel)
      .unwrap_err();
    assert!(matches!(err, ExecError::Cancelled));
  }

  #[test]
  fn syntax_error_maps_to_parse_syntaxerror() {
    let exec = VmJsExecutor::default();
    let cancel = Arc::new(AtomicBool::new(false));
    let err = exec
      .execute(&test_case("syntax.js"), "let =;", &cancel)
      .unwrap_err();
    let ExecError::Js(js) = err else {
      panic!("expected JS error, got {err:?}");
    };
    assert_eq!(js.phase, ExecPhase::Parse);
    assert_eq!(js.typ.as_deref(), Some("SyntaxError"));
    assert!(
      js.message.contains("syntax.js"),
      "rendered diagnostic should include file name, got: {}",
      js.message
    );
  }

  #[test]
  fn binder_caseblock_redeclaration_is_parse_syntaxerror() {
    // Mirrors test262 `language/statements/switch/syntax/redeclaration/*` —
    // `$DONOTEVALUATE()` would skip runtime instantiation, so the binder must
    // reject at parse phase.
    let exec = VmJsExecutor::default();
    let cancel = Arc::new(AtomicBool::new(false));
    let source = "switch (0) { case 1: let f; default: let f }";
    let err = exec
      .execute(&test_case("switch-redecl.js"), source, &cancel)
      .unwrap_err();
    let ExecError::Js(js) = err else {
      panic!("expected JS error, got {err:?}");
    };
    assert_eq!(js.phase, ExecPhase::Parse);
    assert_eq!(js.typ.as_deref(), Some("SyntaxError"));
    assert!(
      js.message.contains("BIND0001") || js.message.contains("already been declared"),
      "expected binder redeclaration diagnostic, got: {}",
      js.message
    );
  }

  #[test]
  fn throw_number_maps_to_runtime_error() {
    let exec = VmJsExecutor::default();
    let cancel = Arc::new(AtomicBool::new(false));
    let err = exec
      .execute(&test_case("throw.js"), "throw 1;", &cancel)
      .unwrap_err();
    let ExecError::Js(js) = err else {
      panic!("expected JS error, got {err:?}");
    };
    assert_eq!(js.phase, ExecPhase::Runtime);
    assert!(js.typ.is_none());
    assert_eq!(js.message, "1");
  }
}
