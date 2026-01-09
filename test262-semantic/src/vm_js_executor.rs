use crate::executor::{ExecError, ExecPhase, ExecResult, Executor, JsError};
use crate::report::Variant;
use crate::runner::TestCase;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use vm_js::format_stack_trace;
use vm_js::{Heap, HeapLimits, PropertyKey, PropertyKind, TerminationReason, Value, Vm, VmError, VmOptions};

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
      return Err(ExecError::Skipped(
        "module tests are not supported yet (vm-js executor only supports classic scripts)"
          .to_string(),
      ));
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

    match runtime.exec_script(source) {
      Ok(_) => Ok(()),
      Err(err) => Err(map_vm_error(err, &mut runtime)),
    }
  }
}

fn map_vm_error(err: VmError, runtime: &mut vm_js::JsRuntime) -> ExecError {
  match err {
    VmError::Syntax(diags) => {
      let mut message = format_diagnostics(&diags);
      if !message.starts_with("SyntaxError") {
        message = format!("SyntaxError: {message}");
      }
      ExecError::Js(JsError::new(ExecPhase::Parse, Some("SyntaxError".to_string()), message))
    }
    VmError::Throw(thrown) => ExecError::Js(map_thrown_value(runtime, thrown)),
    VmError::Termination(term) => match term.reason {
      TerminationReason::Interrupted | TerminationReason::DeadlineExceeded | TerminationReason::OutOfFuel => {
        ExecError::Cancelled
      }
      TerminationReason::OutOfMemory | TerminationReason::StackOverflow => {
        let stack = format_stack_trace(&term.stack);
        let mut js = JsError::new(ExecPhase::Runtime, None, term.to_string());
        if !stack.is_empty() {
          js.stack = Some(stack);
        }
        ExecError::Js(js)
      }
    },
    other => ExecError::Js(JsError::new(ExecPhase::Runtime, None, other.to_string())),
  }
}

fn format_diagnostics(diags: &[diagnostics::Diagnostic]) -> String {
  if diags.is_empty() {
    return "unknown syntax error".to_string();
  }
  diags
    .iter()
    .map(|d| {
      if d.code.as_str().is_empty() {
        d.message.clone()
      } else {
        format!("{}: {}", d.code.as_str(), d.message)
      }
    })
    .collect::<Vec<_>>()
    .join("\n")
}

fn map_thrown_value(runtime: &mut vm_js::JsRuntime, thrown: Value) -> JsError {
  // Root the thrown value while we inspect it; allocations for property keys can trigger GC.
  let mut scope = runtime.heap.scope();
  scope.push_root(thrown);
  let heap = scope.heap_mut();

  let (typ, message, stack) = match thrown {
    Value::Object(obj) => {
      let name = get_string_property(heap, obj, "name");
      let message = get_string_property(heap, obj, "message");
      let stack = get_string_property(heap, obj, "stack");
      let fallback = format_value(heap, thrown);
      (
        name,
        message.unwrap_or_else(|| fallback.clone()),
        stack.filter(|s| !s.is_empty()),
      )
    }
    _ => (None, format_value(heap, thrown), None),
  };

  let mut message = message;
  if let Some(typ) = typ.as_deref() {
    if !message.starts_with(typ) {
      if message.is_empty() {
        message = typ.to_string();
      } else {
        message = format!("{typ}: {message}");
      }
    }
  }

  let mut err = JsError::new(ExecPhase::Runtime, typ, message);
  if let Some(stack) = stack {
    err.stack = Some(stack);
  }
  err
}

fn get_string_property(heap: &mut Heap, obj: vm_js::GcObject, name: &str) -> Option<String> {
  let key_s = {
    let mut scope = heap.scope();
    scope.alloc_string(name).ok()?
  };
  let key = PropertyKey::from_string(key_s);
  let desc = heap.get_property(obj, &key).ok().flatten()?;
  let value = match desc.kind {
    PropertyKind::Data { value, .. } => value,
    PropertyKind::Accessor { .. } => return None,
  };
  value_as_string(heap, value)
}

fn value_as_string(heap: &Heap, value: Value) -> Option<String> {
  match value {
    Value::String(s) => heap.get_string(s).ok().map(|s| s.to_utf8_lossy()),
    _ => None,
  }
}

fn format_value(heap: &Heap, value: Value) -> String {
  match value {
    Value::Undefined => "undefined".to_string(),
    Value::Null => "null".to_string(),
    Value::Bool(b) => b.to_string(),
    Value::Number(n) => {
      // Keep this stable and close enough to JS for debugging (no exponential dance).
      if n.is_nan() {
        "NaN".to_string()
      } else if n == f64::INFINITY {
        "Infinity".to_string()
      } else if n == f64::NEG_INFINITY {
        "-Infinity".to_string()
      } else {
        n.to_string()
      }
    }
    Value::String(s) => heap
      .get_string(s)
      .map(|s| s.to_utf8_lossy())
      .unwrap_or_else(|_| "<invalid string>".to_string()),
    Value::Symbol(sym) => {
      let desc = heap
        .symbol_description(sym)
        .and_then(|s| heap.get_string(s).ok().map(|s| s.to_utf8_lossy()));
      match desc {
        Some(desc) => format!("Symbol({desc})"),
        None => "Symbol()".to_string(),
      }
    }
    Value::Object(_) => "[object Object]".to_string(),
  }
}
