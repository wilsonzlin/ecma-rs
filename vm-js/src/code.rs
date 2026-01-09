//! Stable storage for compiled JavaScript source + lowered HIR.
//!
//! A user-defined [`crate::JsFunction`] stores a [`CompiledFunctionRef`] in its `[[Call]]` handler.
//! Since `CompiledFunctionRef` contains an `Arc<CompiledScript>`, function objects keep their
//! underlying compiled source/HIR alive even after the original compilation API returns.
//!
//! Note that [`CompiledScript`] lives **outside** the GC heap. The GC's [`crate::Heap::used_bytes`]
//! accounting includes the size of the `Arc` pointer stored inside the function object, but does
//! *not* include the memory used by the compiled HIR itself.

use crate::source::SourceText;
use crate::VmError;
use diagnostics::FileId;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::sync::Arc;

/// A compiled JavaScript classic script (source text + lowered HIR).
#[derive(Debug)]
pub struct CompiledScript {
  pub source: SourceText,
  pub hir: Arc<hir_js::LowerResult>,
}

impl CompiledScript {
  /// Parse and lower a classic script (ECMAScript dialect, `SourceType::Script`).
  pub fn compile_script(
    name: impl Into<Arc<str>>,
    text: impl Into<Arc<str>>,
  ) -> Result<Arc<CompiledScript>, VmError> {
    let source = SourceText::new(name, text);
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Script,
    };

    let parsed = parse_with_options(source.text.as_ref(), opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;

    let hir = hir_js::lower_file(FileId(0), hir_js::FileKind::Js, &parsed);
    Ok(Arc::new(Self {
      source,
      hir: Arc::new(hir),
    }))
  }
}

/// A reference to a user-defined function body within a [`CompiledScript`].
///
/// This is stored inside `JsFunction` call handlers so closures can outlive the compilation API
/// without holding dangling pointers into ephemeral AST arenas.
#[derive(Debug, Clone)]
pub struct CompiledFunctionRef {
  pub script: Arc<CompiledScript>,
  pub body: hir_js::BodyId,
}

