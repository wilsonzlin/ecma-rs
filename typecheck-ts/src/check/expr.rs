use std::sync::Arc;

use diagnostics::Span;
use types_ts_interned::{RelateCtx, RelateTypeExpander, TypeId, TypeStore};

use super::overload::{resolve_construct_overloads, resolve_overloads, CallResolution};

/// Resolve a call expression against a callable type.
pub fn resolve_call(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  callee: TypeId,
  args: &[TypeId],
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  expander: Option<&dyn RelateTypeExpander>,
) -> CallResolution {
  resolve_overloads(
    store,
    relate,
    callee,
    args,
    this_arg,
    contextual_return,
    span,
    expander,
  )
}

/// Resolve a `new` expression against a constructable type.
pub fn resolve_construct(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  callee: TypeId,
  args: &[TypeId],
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  expander: Option<&dyn RelateTypeExpander>,
) -> CallResolution {
  resolve_construct_overloads(
    store,
    relate,
    callee,
    args,
    this_arg,
    contextual_return,
    span,
    expander,
  )
}
