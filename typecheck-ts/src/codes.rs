//! Registry of diagnostic codes emitted by `typecheck-ts`.
//!
//! Each [`Code`] documents the expected shape of diagnostics the checker emits:
//! the short description, where the primary span should point, and any
//! additional labels or notes that accompany the diagnostic.

use diagnostics::{sort_diagnostics, sort_labels, Diagnostic, Span};

/// Metadata describing a diagnostic code.
#[derive(Clone, Copy, Debug)]
pub struct Code {
  /// Stable string identifier, e.g. `TC0005`.
  pub id: &'static str,
  /// Short description of what the diagnostic reports.
  pub description: &'static str,
  /// Guidance for where the primary span should be anchored.
  pub primary_span: &'static str,
  /// Expected labels attached to the diagnostic (primary and secondary).
  pub labels: &'static [&'static str],
  /// Expected notes automatically added to the diagnostic.
  pub notes: &'static [&'static str],
}

impl Code {
  pub const fn new(
    id: &'static str,
    description: &'static str,
    primary_span: &'static str,
    labels: &'static [&'static str],
    notes: &'static [&'static str],
  ) -> Self {
    Code {
      id,
      description,
      primary_span,
      labels,
      notes,
    }
  }

  /// Identifier as a plain string (useful for comparisons in tests).
  pub const fn as_str(&self) -> &'static str {
    self.id
  }

  /// Construct an error diagnostic tagged with this code and its expected notes.
  pub fn error(&self, message: impl Into<String>, primary: Span) -> Diagnostic {
    let mut diagnostic = Diagnostic::error(self.id, message, primary);
    for note in self.notes {
      diagnostic.push_note(*note);
    }
    diagnostic
  }

  /// Construct a warning diagnostic tagged with this code and its expected
  /// notes.
  pub fn warning(&self, message: impl Into<String>, primary: Span) -> Diagnostic {
    let mut diagnostic = Diagnostic::warning(self.id, message, primary);
    for note in self.notes {
      diagnostic.push_note(*note);
    }
    diagnostic
  }
}

/// Sort labels inside each diagnostic and then the diagnostics themselves to
/// keep outputs deterministic regardless of traversal order.
pub fn normalize_diagnostics(diagnostics: &mut Vec<Diagnostic>) {
  for diagnostic in diagnostics.iter_mut() {
    normalize_diagnostic(diagnostic);
  }
  sort_diagnostics(diagnostics);
}

/// Canonicalize label and note ordering within a single diagnostic.
pub fn normalize_diagnostic(diagnostic: &mut Diagnostic) {
  sort_labels(&mut diagnostic.labels);
  diagnostic.notes.sort();
}

/// TC0001: No libraries were loaded.
///
/// - Primary span: zero-length span at the start of the checked file if known,
///   otherwise [`FileId(u32::MAX)`] as a placeholder.
/// - Labels: primary only.
/// - Notes: none.
pub const NO_LIBS_LOADED: Code = Code::new(
  "TC0001",
  "no default libraries loaded",
  "file start placeholder when no libs are available",
  &["primary: placeholder at start of file"],
  &[],
);

/// TC0002: Global augmentations are only partially supported by the legacy lib
/// checker.
///
/// - Primary span: zero-length span at the start of the library file that
///   contains `declare global`.
/// - Labels: primary only.
/// - Notes: none.
pub const PARTIAL_GLOBAL_AUGMENTATION: Code = Code::new(
  "TC0002",
  "global augmentations are only partially supported",
  "start of the lib file containing `declare global`",
  &["primary: start of offending lib"],
  &[],
);

/// TC0003: Unsupported global augmentation merging into an `any` global.
///
/// - Primary span: zero-length span at the start of the library file that
///   attempted the augmentation.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_GLOBAL_AUGMENTATION: Code = Code::new(
  "TC0003",
  "unsupported global augmentation",
  "start of the lib file performing the augmentation",
  &["primary: start of offending lib"],
  &[],
);

/// TC0004: A library file is not a `.d.ts` and is ignored for globals.
///
/// - Primary span: zero-length span at the start of the library file.
/// - Labels: primary only.
/// - Notes: none.
pub const NON_DTS_LIB: Code = Code::new(
  "TC0004",
  ".d.ts library expected",
  "start of the non-.d.ts library file",
  &["primary: start of non-.d.ts lib"],
  &[],
);

/// TC0005: Identifier could not be resolved.
///
/// - Primary span: the identifier token (or a zero-length placeholder for the
///   legacy lib checker which does not track offsets).
/// - Labels: primary only.
/// - Notes: none.
pub const UNKNOWN_IDENTIFIER: Code = Code::new(
  "TC0005",
  "unknown identifier",
  "identifier being resolved; legacy lib checker uses a zero-length placeholder",
  &["primary: identifier reference"],
  &[],
);

/// TC0006: Fresh object literal has an excess property not present in the
/// target type.
///
/// - Primary span: the object literal expression being assigned.
/// - Labels: primary only.
/// - Notes: none.
pub const EXCESS_PROPERTY: Code = Code::new(
  "TC0006",
  "excess property in object literal",
  "object literal being assigned to the target type",
  &["primary: object literal expression"],
  &[],
);

/// TC0007: Source type is not assignable to the target type.
///
/// - Primary span: the source expression being assigned.
/// - Labels: primary only.
/// - Notes: none.
pub const TYPE_MISMATCH: Code = Code::new(
  "TC0007",
  "type mismatch",
  "source expression being assigned",
  &["primary: source expression"],
  &[],
);

/// TC0008: Property access on a global that does not declare the property.
///
/// - Primary span: zero-length placeholder at the start of the file flagged by
///   the legacy lib checker.
/// - Labels: primary only.
/// - Notes: none.
pub const MISSING_GLOBAL_PROPERTY: Code = Code::new(
  "TC0008",
  "property does not exist on global",
  "file start placeholder when a global property is missing",
  &["primary: placeholder at start of file"],
  &[],
);

/// TC0009: Variable is used before being definitely assigned.
///
/// - Primary span: the identifier reference being read.
/// - Labels: primary only.
/// - Notes: none.
pub const USE_BEFORE_ASSIGNMENT: Code = Code::new(
  "TC0009",
  "variable used before being assigned",
  "identifier used before assignment",
  &["primary: identifier read before assignment"],
  &[],
);

/// TC1001: Module specifier could not be resolved.
///
/// - Primary span: the import/export module specifier.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_MODULE: Code = Code::new(
  "TC1001",
  "unresolved module specifier",
  "module specifier in the import/export statement",
  &["primary: module specifier span"],
  &[],
);

/// TC1002: Export refers to a symbol that is not available.
///
/// - Primary span: the named export specifier or `export * as ...` alias.
/// - Labels: primary only.
/// - Notes: none.
pub const UNKNOWN_EXPORT: Code = Code::new(
  "TC1002",
  "unknown export",
  "export specifier that could not be resolved",
  &["primary: export specifier"],
  &[],
);

/// TC1003: Destructuring import pattern is not yet supported.
///
/// - Primary span: the pattern expression used in the import clause.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_IMPORT_PATTERN: Code = Code::new(
  "TC1003",
  "unsupported import pattern",
  "import clause pattern",
  &["primary: unsupported import pattern"],
  &[],
);

/// TC1004: Binding pattern is not yet supported in this context.
///
/// - Primary span: the unsupported binding pattern (variable, export, or type-only pattern).
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_PATTERN: Code = Code::new(
  "TC1004",
  "unsupported binding pattern",
  "binding pattern in the variable declaration",
  &["primary: unsupported binding pattern"],
  &[],
);

/// TC1005: Parameter binding pattern is not yet supported.
///
/// - Primary span: the parameter pattern.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_PARAM_PATTERN: Code = Code::new(
  "TC1005",
  "unsupported parameter pattern",
  "unsupported parameter binding pattern",
  &["primary: parameter pattern"],
  &[],
);

/// TC1006: Call expression supplies an incorrect number of arguments.
///
/// - Primary span: the call expression.
/// - Labels: primary only.
/// - Notes: none.
pub const ARGUMENT_COUNT_MISMATCH: Code = Code::new(
  "TC1006",
  "argument count mismatch",
  "call expression with the wrong number of arguments",
  &["primary: call expression"],
  &[],
);

/// TC2000: Call expression has no applicable overloads or the callee is not
/// callable.
///
/// - Primary span: the call expression.
/// - Labels: primary only.
/// - Notes: may include candidate signatures and rejection reasons.
pub const NO_OVERLOAD: Code = Code::new(
  "TC2000",
  "no overload matches the call",
  "call expression with no applicable overload",
  &["primary: call expression"],
  &[],
);

/// TC2001: Multiple overloads were applicable for a call expression and the
/// checker could not select a best candidate.
///
/// - Primary span: the call expression.
/// - Labels: primary only.
/// - Notes: lists candidate signatures (truncated when many are present).
pub const AMBIGUOUS_OVERLOAD: Code = Code::new(
  "TC2001",
  "call is ambiguous",
  "call expression when multiple overloads apply",
  &["primary: call expression"],
  &[],
);

/// TC2008: Type reference could not be resolved or used incorrectly.
///
/// - Primary span: the referenced type name.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_TYPE_REFERENCE: Code = Code::new(
  "TC2008",
  "unresolved type reference",
  "type reference that could not be resolved",
  &["primary: type reference span"],
  &[],
);

/// TC2009: Qualified type reference could not be resolved or is unsupported.
///
/// - Primary span: the qualified type reference.
/// - Labels: primary only.
/// - Notes: none.
pub const UNSUPPORTED_QUALIFIED_NAME: Code = Code::new(
  "TC2009",
  "unsupported qualified type name",
  "qualified type reference that cannot be resolved",
  &["primary: qualified type reference"],
  &[],
);

/// TC2010: `import()` type could not be resolved.
///
/// - Primary span: the entire `import()` type expression.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_IMPORT_TYPE: Code = Code::new(
  "TC2010",
  "unresolved import type",
  "import() type expression that could not be resolved",
  &["primary: import() type expression"],
  &[],
);

/// TC2011: `typeof` type query could not resolve the referenced symbol.
///
/// - Primary span: the `typeof` query expression.
/// - Labels: primary only.
/// - Notes: none.
pub const UNRESOLVED_TYPE_QUERY: Code = Code::new(
  "TC2011",
  "unresolved type query",
  "typeof query that could not be resolved",
  &["primary: typeof query span"],
  &[],
);

/// HOST0001: Host environment failed to provide required input.
///
/// - Primary span: zero-length placeholder when no source span is available.
/// - Labels: primary only.
/// - Notes: may include an additional note when no span is known.
pub const HOST_ERROR: Code = Code::new(
  "HOST0001",
  "host error",
  "placeholder span when host errors are not tied to a file",
  &["primary: placeholder span"],
  &[],
);

/// ICE0001: Unexpected internal compiler error surfaced from a panic.
///
/// - Primary span: placeholder or the file referenced in [`IceContext`].
/// - Labels: primary only.
/// - Notes: includes a help note asking users to file an issue.
pub const INTERNAL_COMPILER_ERROR: Code = Code::new(
  "ICE0001",
  "internal compiler error",
  "placeholder or context-derived span when an ICE occurs",
  &["primary: placeholder span"],
  &["internal compiler error: this is a bug in the tool; please file an issue with a reproduction"],
);

/// ICE0002: Type checker expected a body but could not find one.
///
/// - Primary span: zero-length placeholder because no body span exists.
/// - Labels: primary only.
/// - Notes: none.
pub const MISSING_BODY: Code = Code::new(
  "ICE0002",
  "missing body",
  "placeholder span when a body entry is missing",
  &["primary: placeholder span"],
  &[],
);

/// CANCEL0001: Type checking was cancelled by the host.
///
/// - Primary span: zero-length placeholder span.
/// - Labels: primary only.
/// - Notes: explains that the operation was cancelled by the host.
pub const CANCELLED: Code = Code::new(
  "CANCEL0001",
  "operation cancelled",
  "placeholder span when cancellation is requested",
  &["primary: placeholder span"],
  &["operation was cancelled by the host"],
);

/// OOM0001: Checker ran out of memory while processing a program.
///
/// - Primary span: zero-length placeholder span.
/// - Labels: primary only.
/// - Notes: informs the user the checker exhausted memory.
pub const OUT_OF_MEMORY: Code = Code::new(
  "OOM0001",
  "out of memory",
  "placeholder span when the checker exhausts memory",
  &["primary: placeholder span"],
  &["the checker ran out of memory while processing this program"],
);
