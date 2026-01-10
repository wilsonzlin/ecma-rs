//! ECMAScript module graph loading (compatibility shim).
//!
//! This crate's module graph loading implementation has been consolidated into
//! [`crate::module_loading`] so there is a single canonical source of truth for:
//! - module-loading record types, and
//! - the graph loading state machine.
//!
//! This module remains as a compatibility shim and will be removed in a future release.
#![deprecated(
  note = "module_graph_loader was merged into module_loading; use vm_js::module_loading::* (or crate-level re-exports) instead."
)]

pub use crate::module_graph::ModuleGraph;
pub use crate::module_loading::{
  continue_module_loading, finish_loading_imported_module, inner_module_loading, load_requested_modules,
  HostDefined, ModuleCompletion, ModuleLoadPayload, ModuleLoaderHost,
};
pub use crate::module_record::ModuleStatus;
pub use crate::module_record::SourceTextModuleRecord as CyclicModuleRecord;
pub use crate::ModuleRequest;
pub use crate::LoadedModuleRequest;

