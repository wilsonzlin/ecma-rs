use std::sync::Arc;

use diagnostics::Span;
use types_ts_interned::{RelateCtx, TypeId, TypeStore};

use super::infer::TypeParamDecl;
use super::overload::{resolve_overloads, CallResolution};

/// Resolve a call expression against a callable type.
pub fn resolve_call(
  store: &Arc<TypeStore>,
  relate: &RelateCtx<'_>,
  callee: TypeId,
  args: &[TypeId],
  type_params: &[TypeParamDecl],
  contextual_return: Option<TypeId>,
  span: Span,
) -> CallResolution {
  resolve_overloads(
    store,
    relate,
    callee,
    args,
    type_params,
    contextual_return,
    span,
  )
}
