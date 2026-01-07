extern crate semantic_js as semantic_js_crate;

use crate::api::{DefId, FileId, TextRange};
use crate::check::type_expr::TypeResolver;
use crate::files::{FileOrigin, FileRegistry};
use hir_js::ids::MISSING_BODY;
use ordered_float::OrderedFloat;
use semantic_js_crate::ts as sem_ts;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use types_ts_interned as tti;
use types_ts_interned::{PropKey, TypeId, TypeParamId};

use super::{DefKind, ExportMap, Host, ProgramState, TypeKind};

#[path = "types/decl_resolver.rs"]
mod decl_resolver;
#[path = "types/display.rs"]
mod display;
#[path = "types/display_convert.rs"]
mod display_convert;
#[path = "types/expander.rs"]
mod expander;
#[path = "types/namespace_index.rs"]
mod namespace_index;
#[path = "types/property_lookup.rs"]
mod property_lookup;
#[path = "types/resolver.rs"]
mod resolver;

pub use display::{ExplainTree, TypeDisplay};

pub(crate) use namespace_index::NamespaceMemberIndex;
pub(crate) use resolver::ProgramTypeResolver;

pub(super) use decl_resolver::DeclTypeResolver;
pub(super) use display_convert::{
  callable_return_is_unknown, convert_type_for_display, display_type_from_state,
};
pub(super) use expander::ProgramTypeExpander;
pub(super) use property_lookup::lookup_interned_property_type;
pub(super) use resolver::export_assignment_path_for_file;
