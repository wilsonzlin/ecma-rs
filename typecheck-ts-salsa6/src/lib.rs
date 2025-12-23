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

pub use crate::db::Database;
pub use crate::db::Db;
pub use crate::graph::ModuleEdge;
pub use crate::graph::ModuleGraph;
pub use crate::host::FileId;
pub use crate::host::FileKind;
pub use crate::host::Host;
pub use crate::host::Resolver;
pub use crate::options::CompilerOptions;
pub use crate::options::JsxMode;
pub use crate::options::Target;
pub use crate::parse::ParseOutput;
pub use crate::program::Program;
pub use diagnostics_salsa6::Diagnostic;
pub use diagnostics_salsa6::DiagnosticCode;
pub use diagnostics_salsa6::Severity;
pub use diagnostics_salsa6::Span;
pub use diagnostics_salsa6::TextRange;

#[cfg(test)]
mod tests;
