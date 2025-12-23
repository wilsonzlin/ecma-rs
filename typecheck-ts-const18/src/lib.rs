pub mod check;
pub mod diagnostic;
pub mod expr;
pub mod types;

pub use check::Checker;
pub use diagnostic::Diagnostic;
pub use diagnostic::DiagnosticKind;
pub use diagnostic::Span;
pub use expr::Expr;
pub use expr::ObjectField;
pub use types::IndexSignature;
pub use types::ObjectType;
pub use types::Property;
pub use types::TupleType;
pub use types::Type;
