extern crate semantic_js as semantic_js_crate;

use crate::api::{DefId, FileId, TextRange};
use crate::check::type_expr::TypeResolver;
use crate::files::{FileOrigin, FileRegistry};
use hir_js::ids::MISSING_BODY;
use semantic_js_crate::ts as sem_ts;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use types_ts_interned as tti;
use types_ts_interned::{PropKey, TypeId, TypeParamId};

use super::{DefKind, ExportMap, Host, ProgramState};

#[path = "types/decl_resolver.rs"]
mod decl_resolver;
#[path = "types/display.rs"]
mod display;
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
pub(super) use expander::ProgramTypeExpander;
pub(super) use property_lookup::lookup_interned_property_type;
pub(super) use resolver::export_assignment_path_for_file;

pub(super) fn callable_return_is_unknown(store: &Arc<tti::TypeStore>, ty: TypeId) -> bool {
  let prim = store.primitive_ids();
  let mut seen = HashSet::new();
  let mut pending = vec![store.canon(ty)];
  while let Some(ty) = pending.pop() {
    if !seen.insert(ty) {
      continue;
    }
    match store.type_kind(ty) {
      tti::TypeKind::Callable { overloads } => {
        if overloads
          .iter()
          .any(|sig_id| store.signature(*sig_id).ret == prim.unknown)
        {
          return true;
        }
      }
      tti::TypeKind::Union(members) | tti::TypeKind::Intersection(members) => {
        pending.extend(members.iter().copied());
      }
      _ => {}
    }
  }
  false
}
