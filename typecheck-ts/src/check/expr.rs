use std::sync::Arc;

use diagnostics::Span;
use types_ts_interned::{RelateCtx, RelateTypeExpander, TypeId, TypeStore};

use super::overload::{resolve_overloads, CallResolution};

/// Resolve a call expression against a callable type.
pub fn resolve_call(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  expander: Option<&dyn RelateTypeExpander>,
  callee: TypeId,
  args: &[TypeId],
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
) -> CallResolution {
  resolve_overloads(
    store,
    relate,
    expander,
    callee,
    args,
    this_arg,
    contextual_return,
    span,
  )
}
