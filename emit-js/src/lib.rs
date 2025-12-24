mod emitter;
mod escape;
mod expr;
mod expr_ts;
mod ts_type;

pub use emitter::EmitMode;
pub use emitter::EmitOptions;
pub use emitter::Emitter;
pub use escape::emit_string_literal_double_quoted;
pub use escape::emit_template_raw_segment;
pub use expr::{emit_expr, EmitError, EmitResult, ExprEmitter};
pub use ts_type::{
  emit_interface_decl,
  emit_ts_type,
  emit_type_alias_decl,
  emit_type_expr,
  ts_type_to_string,
};
