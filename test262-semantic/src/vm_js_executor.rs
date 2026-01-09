use crate::executor::{ExecError, ExecPhase, ExecResult, Executor, JsError};
use crate::report::Variant;
use crate::runner::TestCase;
use diagnostics::render::render_diagnostic;
use diagnostics::SimpleFiles;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use vm_js::format_stack_trace;
use vm_js::{Heap, HeapLimits, PropertyKey, PropertyKind, SourceText, StackFrame, TerminationReason, Value, Vm, VmError, VmOptions};
 
const DEFAULT_HEAP_MAX_BYTES: usize = 64 * 1024 * 1024;
const DEFAULT_HEAP_GC_THRESHOLD_BYTES: usize = 32 * 1024 * 1024;
 
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
      return Err(ExecError::Skipped("modules not supported".to_string()));
    }
 
    let vm = Vm::new(VmOptions {
      interrupt_flag: Some(Arc::clone(cancel)),
      ..VmOptions::default()
    });
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
 
    // Give the VM a useful/stable source name for stack traces.
    let file_name = if case.id.is_empty() {
      "<test262>".to_string()
    } else {
      case.id.clone()
    };
    let source_text = Arc::new(SourceText::new(file_name, source));
 
    let result = runtime.exec_script_source(source_text);
 
    // Cancellation should win over any other outcome (including parse/runtime errors).
    if cancel.load(Ordering::Relaxed) {
      return Err(ExecError::Cancelled);
    }
 
    match result {
      Ok(_) => Ok(()),
      Err(err) => Err(map_vm_error(case, source, cancel, &mut runtime, err)),
    }
  }
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

    VmError::ThrowWithStack { value: thrown, stack } => {
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
      TerminationReason::Interrupted | TerminationReason::DeadlineExceeded | TerminationReason::OutOfFuel => {
        ExecError::Cancelled
      }
 
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
        .and_then(|desc| scope.heap().get_string(desc).ok().map(|s| s.to_utf8_lossy()))
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
    let err = exec.execute(&test_case("cancel.js"), "1;", &cancel).unwrap_err();
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
