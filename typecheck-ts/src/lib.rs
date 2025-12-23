//! TypeScript checker façade and error handling primitives.
//!
//! This crate is intentionally focused on robustness: user-facing errors are
//! reported as diagnostics and internal issues are surfaced as ICE diagnostics
//! rather than panicking the process.

mod diagnostic;
mod error;
mod program;

pub use diagnostic::Diagnostic;
pub use diagnostic::DiagnosticSeverity;
pub use error::BodyId;
pub use error::FatalError;
pub use error::FileId;
pub use error::HostError;
pub use error::Ice;
pub use program::CheckReport;
pub use program::Host;
pub use program::Program;
