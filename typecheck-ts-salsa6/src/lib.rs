#![deny(missing_docs)]

//! Public entrypoints for the TypeScript type checker.
//!
//! This is an early, query-based skeleton that wires together inputs, parsing,
//! and a resolver-driven module graph. The full checker will build on these
//! foundations.

mod db;
mod graph;
mod host;
mod options;
mod parse;
mod program;

pub use crate::db::{Database, Db};
pub use crate::graph::{ModuleEdge, ModuleGraph};
pub use crate::host::{FileId, FileKind, Host, Resolver};
pub use crate::options::{CompilerOptions, JsxMode, Target};
pub use crate::parse::ParseOutput;
pub use crate::program::Program;
pub use diagnostics_salsa6::{Diagnostic, DiagnosticCode, Severity, Span, TextRange};

#[cfg(test)]
mod tests;
