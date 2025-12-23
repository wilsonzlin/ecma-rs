//! TypeScript checker façade and error handling primitives.
//!
//! This crate is intentionally focused on robustness: user-facing errors are
//! reported as diagnostics and internal issues are surfaced as ICE diagnostics
//! rather than panicking the process.

mod diagnostic;
mod error;
mod program;

pub use diagnostic::{Diagnostic, DiagnosticSeverity};
pub use error::{BodyId, FatalError, FileId, HostError, Ice};
pub use program::{CheckReport, Host, Program};
