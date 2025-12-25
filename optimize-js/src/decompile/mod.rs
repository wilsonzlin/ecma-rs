pub mod foreign;
pub mod il;
pub mod top_level;

pub use foreign::{collect_foreign_bindings, ForeignBinding, ForeignBindings};
pub use il::{
  lower_function, lower_program, LoweredArg, LoweredBlock, LoweredFunction, LoweredInst,
  LoweredProgram,
};
pub use top_level::{build_top_level, foreign_var_decl, prepend_foreign_decls};
