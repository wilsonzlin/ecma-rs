use std::sync::Arc;

use diagnostics::Span;
use types_ts_interned::{RelateCtx, TypeId, TypeStore};

use super::overload::{
  resolve_construct as resolve_construct_overloads, resolve_overloads, CallResolution,
};

/// Resolve a call expression against a callable type.
pub fn resolve_call(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  callee: TypeId,
  args: &[TypeId],
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
  context: Option<&mut dyn super::overload::OverloadContext>,
) -> CallResolution {
  resolve_overloads(
    store,
    relate,
    None,
    callee,
    args,
    this_arg,
    contextual_return,
    span,
    context,
  )
}

/// Resolve a `new` expression against construct signatures of the callee type.
pub fn resolve_construct(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  callee: TypeId,
  args: &[TypeId],
  this_arg: Option<TypeId>,
  contextual_return: Option<TypeId>,
  span: Span,
) -> CallResolution {
  resolve_construct_overloads(
    store,
    relate,
    callee,
    args,
    this_arg,
    contextual_return,
    span,
  )
}

/// Resolve a call expression against a callable type with an explicit ref expander.
pub fn resolve_call_with_expander(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  expander: Option<&dyn types_ts_interned::RelateTypeExpander>,
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
    None,
  )
}
