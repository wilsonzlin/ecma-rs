//! Internal helpers for type inference, flow analysis, and generic instantiation.

pub mod caches;
pub(super) mod cfg;
pub(crate) mod decls;
pub(crate) mod expr;
pub(super) mod flow;
pub(super) mod flow_narrow;
pub(super) mod legacy_narrow;
pub mod hir_body;
pub(crate) mod infer;
pub(crate) mod instantiate;
pub(super) mod modules;
pub(crate) mod overload;
pub(crate) mod type_expr;

use types_ts_interned::{Property, RelateHooks};

/// Default relation hooks used throughout the checker. These enforce nominal-ish
/// compatibility for private and protected members by requiring them to share
/// the same originating declaration.
pub(crate) fn relate_hooks<'a>() -> RelateHooks<'a> {
  fn same_origin(a: &Property, b: &Property) -> bool {
    match (a.data.declared_on, b.data.declared_on) {
      (Some(left), Some(right)) if left == right => return true,
      _ => {}
    }
    match (a.data.origin, b.data.origin) {
      (Some(left), Some(right)) => left == right,
      _ => false,
    }
  }

  RelateHooks {
    expander: None,
    is_same_origin_private_member: Some(&same_origin),
  }
}
