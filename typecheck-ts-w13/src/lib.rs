//! Lightweight TypeScript-like type checker built on top of `parse-js`.
//!
//! This crate intentionally keeps the public surface area small: callers
//! register bodies (typically parsed from source) in a [`TypeDatabase`], then
//! invoke [`check::check_body`] to obtain a [`BodyCheckResult`] containing
//! type side tables and diagnostics.

pub mod check;
pub mod db;
pub mod diagnostic;
pub mod ids;
pub mod types;

pub use check::check_body;
pub use check::BodyCheckResult;
pub use db::Body;
pub use db::BodyKind;
pub use db::TypeDatabase;
pub use diagnostic::Diagnostic;
pub use ids::BodyId;
pub use ids::ExprId;
pub use ids::PatId;
pub use types::Type;
pub use types::TypeDisplay;
pub use types::TypeId;
pub use types::TypeStore;
