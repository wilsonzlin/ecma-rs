//! Lowering from `parse-js` AST into a simple HIR with stable IDs.

mod lower;

pub use lower::lower_top_level;
pub use lower::lower_top_level_and_attach_ids;
pub use lower::BodyId;
pub use lower::ExprId;
pub use lower::HirBody;
pub use lower::HirBodyKind;
pub use lower::HirExpr;
pub use lower::HirPat;
pub use lower::HirProgram;
pub use lower::HirStmt;
pub use lower::LowerError;
pub use lower::PatId;
pub use lower::StmtId;
