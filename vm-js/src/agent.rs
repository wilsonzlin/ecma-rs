use crate::source::format_stack_trace;
use crate::{Budget, Heap, HeapLimits, JsRuntime, Realm, SourceText, Termination, Value, Vm, VmError, VmOptions};
use std::sync::Arc;

/// Host integration hooks for [`Agent`] script execution.
///
/// This is intentionally minimal today (jobs/modules are separate workstreams), but shaped so it
/// can be extended without redesign later.
pub trait HostHooks {
  /// Invoked after a script run, to allow the embedding to perform a microtask checkpoint.
  ///
  /// This mirrors the HTML event loop's
  /// ["perform a microtask checkpoint"](https://html.spec.whatwg.org/multipage/webappapis.html#perform-a-microtask-checkpoint)
  /// step that occurs after script execution.
  ///
  /// The default implementation does nothing.
  fn microtask_checkpoint(&mut self, _agent: &mut Agent) -> Result<(), VmError> {
    Ok(())
  }
}

/// A spec-shaped embedding façade that bundles a [`Vm`], [`Heap`], and at least one [`Realm`].
///
/// This is the primary entry point for host embeddings (FastRender, WebIDL adapters, etc). It
/// centralizes ownership and exposes safe entry points for script execution and host integration.
pub struct Agent {
  runtime: JsRuntime,
}

impl Agent {
  /// Creates a new [`Agent`] from an already-constructed [`Vm`] and [`Heap`], and initializes a
  /// fresh [`Realm`] on that heap.
  pub fn new(vm: Vm, heap: Heap) -> Result<Self, VmError> {
    Ok(Self {
      runtime: JsRuntime::new(vm, heap)?,
    })
  }

  /// Convenience constructor from [`VmOptions`] and [`HeapLimits`].
  pub fn with_options(vm_options: VmOptions, heap_limits: HeapLimits) -> Result<Self, VmError> {
    let vm = Vm::new(vm_options);
    let heap = Heap::new(heap_limits);
    Self::new(vm, heap)
  }

  /// Borrows the underlying [`Vm`].
  #[inline]
  pub fn vm(&self) -> &Vm {
    &self.runtime.vm
  }

  /// Borrows the underlying [`Vm`] mutably.
  #[inline]
  pub fn vm_mut(&mut self) -> &mut Vm {
    &mut self.runtime.vm
  }

  /// Borrows the underlying [`Heap`].
  #[inline]
  pub fn heap(&self) -> &Heap {
    self.runtime.heap()
  }

  /// Borrows the underlying [`Heap`] mutably.
  #[inline]
  pub fn heap_mut(&mut self) -> &mut Heap {
    self.runtime.heap_mut()
  }

  /// Borrows the primary [`Realm`].
  #[inline]
  pub fn realm(&self) -> &Realm {
    self.runtime.realm()
  }

  /// Run a classic script with a per-run [`Budget`].
  ///
  /// This:
  /// - applies `budget` for the duration of the run (restoring the previous VM budget afterwards),
  /// - executes `source_text` as a classic script, and
  /// - invokes [`HostHooks::microtask_checkpoint`] afterwards (if provided).
  pub fn run_script(
    &mut self,
    source_name: impl Into<Arc<str>>,
    source_text: impl Into<Arc<str>>,
    budget: Budget,
    mut host_hooks: Option<&mut dyn HostHooks>,
  ) -> Result<Value, VmError> {
    let source = Arc::new(SourceText::new(source_name, source_text));

    // Swap the VM budget in/out without holding a borrow across `exec_script`.
    let prev_budget = self.runtime.vm.swap_budget_state(budget);

    let mut result = self.runtime.exec_script_source(source);

    // If the script executed (successfully or with a JS `throw`), the HTML script processing model
    // performs a microtask checkpoint afterwards. For now this is a host hook placeholder.
    if matches!(result, Ok(_) | Err(VmError::Throw(_))) {
      if let Some(hooks) = host_hooks.as_mut() {
        // Root the completion value across the checkpoint so a host checkpoint implementation can
        // allocate/GC without invalidating the returned value.
        let root = match &result {
          Ok(v) => self.heap_mut().add_root(*v).ok(),
          Err(VmError::Throw(v)) => self.heap_mut().add_root(*v).ok(),
          _ => None,
        };

        // If we fail to allocate a persistent root (OOM), skip the checkpoint: running it without
        // rooting could allow GC to invalidate the completion value that we are about to return to
        // the host.
        let checkpoint_result = if root.is_some() {
          hooks.microtask_checkpoint(self)
        } else {
          Ok(())
        };

        if let Some(root) = root {
          self.heap_mut().remove_root(root);
        }

        result = match result {
          Ok(v) => checkpoint_result.map(|_| v),
          Err(err) => {
            // Preserve the original script error; checkpoint errors should be reported separately by
            // the host.
            let _ = checkpoint_result;
            Err(err)
          }
        };
      }
    }

    self.runtime.vm.restore_budget_state(prev_budget);
    result
  }

  /// Convert a JavaScript value into a host-owned string for exception reporting.
  ///
  /// This uses the VM's `ToString` implementation (via [`Heap::to_string`]).
  pub fn value_to_error_string(&mut self, value: Value) -> String {
    let s = match self.heap_mut().to_string(value) {
      Ok(s) => s,
      // If ToString itself throws, format the thrown value.
      Err(VmError::Throw(v)) => return self.value_to_error_string(v),
      Err(_) => return format!("{value:?}"),
    };

    self
      .heap()
      .get_string(s)
      .map(|js| js.to_utf8_lossy())
      .unwrap_or_else(|_| "<invalid string>".to_string())
  }

  /// Formats a VM error into a host-visible string.
  pub fn format_vm_error(&mut self, err: &VmError) -> String {
    match err {
      VmError::Throw(value) => self.value_to_error_string(*value),
      VmError::Termination(term) => format_termination(term),
      other => other.to_string(),
    }
  }
}

/// Formats a termination error into a stable, host-visible string, including stack frames.
pub fn format_termination(term: &Termination) -> String {
  if term.stack.is_empty() {
    term.to_string()
  } else {
    format!("{term}\n{stack}", stack = format_stack_trace(&term.stack))
  }
}
