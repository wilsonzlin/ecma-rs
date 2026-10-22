//! Body-checking method groups split out of `hir_body` for maintainability.
//! Inherent `impl` blocks for `Checker` / `FlowBodyChecker` live here; types and
//! entrypoints remain in the parent `hir_body` module.

mod bindings;
mod call;
mod exprs;
mod flow;
mod flow_ops;
mod jsx;
mod stmts;

pub(super) use bindings::FlowBodyChecker;

// Sibling modules import binding helpers via `super::bindings::…` or these re-exports.
pub(super) use bindings::{
  classify_computed_obj_key, synthesize_computed_indexers, ComputedObjKey,
};
pub use bindings::{type_id_is_da_exempt, DaAliasBody, DaTypeAliasMap};
pub(super) use bindings::{BindingCollector, BindingMode, Reference, SwitchDiscriminant};
