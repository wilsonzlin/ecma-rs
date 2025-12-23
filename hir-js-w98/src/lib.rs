//! hir-js lowers `parse-js` AST into a stricter HIR subset used by downstream tooling.
//! See [`lower`] for the supported surface area.

pub mod lower;

pub use crate::lower::lower;
pub use crate::lower::LowerError;
pub use crate::lower::LowerResult;
pub use crate::lower::Program;
