use super::*;

// JSX tag names are not represented as `ExprKind::Ident` in HIR, so we need to
// collect component tag bases explicitly. This lets the body checker include
// value bindings for imported/global components referenced only from JSX (e.g.
// `<Foo />` or `<Foo.Bar />`).
//
// NOTE: JSX tag names containing `:` (namespaced) or `-` (custom elements)
// should always be treated as intrinsic elements and must not be seeded as
// value identifiers, regardless of capitalization.
pub(super) fn collect_jsx_root_names(
  element: &hir_js::JsxElement,
  lowered: &hir_js::LowerResult,
  names: &mut HashSet<String>,
) {
  if let Some(name) = element.name.as_ref() {
    match name {
      hir_js::JsxElementName::Member(member) => {
        if let Some(base) = lowered.names.resolve(member.base) {
          if !(base.contains(':') || base.contains('-')) {
            names.insert(base.to_string());
          }
        }
      }
      hir_js::JsxElementName::Ident(name_id) => {
        if let Some(name) = lowered.names.resolve(*name_id) {
          if !(name.contains(':') || name.contains('-')) {
            if let Some(first_char) = name.chars().next() {
              if !first_char.is_ascii_lowercase() {
                names.insert(name.to_string());
              }
            }
          }
        }
      }
      hir_js::JsxElementName::Name(_) => {}
    }
  }
  // Nested JSX elements are lowered as separate `ExprKind::Jsx` expressions, so
  // they will be visited by the outer `body.exprs` scan that calls this helper.
}

/// Seed the flow initial env from [`hir_js::Body::locals`] param entries.
pub(super) fn record_param_locals(
  body: &hir_js::Body,
  pat_types: &[TypeId],
  unknown: TypeId,
  initial_env: &mut HashMap<NameId, TypeId>,
) {
  for (_local_id, local) in body.locals_with_kind(hir_js::LocalKind::Param) {
    let Some(pat_id) = local.pat else {
      continue;
    };
    if let Some(ty) = pat_types.get(pat_id.0 as usize).copied() {
      if ty != unknown {
        initial_env.insert(local.name, ty);
      }
    }
  }
}

/// DA alias map for a file, including imported type aliases (re-export aware).
pub(super) fn da_type_alias_map_with_imports<'a>(
  state: &ProgramState,
  file: FileId,
  lowered: &'a hir_js::LowerResult,
  pinned: &'a mut Vec<std::sync::Arc<hir_js::LowerResult>>,
) -> check::hir_body::DaTypeAliasMap<'a> {
  enum ImportDaLink {
    Body {
      local: hir_js::NameId,
      alias_file: FileId,
      alias_span: TextRange,
    },
    Nullary {
      local: hir_js::NameId,
      ty: TypeId,
    },
  }
  let mut import_links: Vec<ImportDaLink> = Vec::new();
  for import in lowered.hir.imports.iter() {
    let hir_js::ImportKind::Es(es) = &import.kind else {
      continue;
    };
    for named in es.named.iter() {
      let Some(local_str) = lowered.names.resolve(named.local) else {
        continue;
      };
      let Some(import_def) = state.def_data.iter().find_map(|(def, data)| {
        (data.file == file && data.name == local_str && matches!(data.kind, DefKind::Import(_)))
          .then_some(*def)
      }) else {
        continue;
      };
      match resolve_imported_type_alias_link(state, import_def) {
        Some(ImportedAliasLink::Def(alias_def)) => {
          let Some(alias_data) = state.def_data.get(&alias_def) else {
            continue;
          };
          if !matches!(alias_data.kind, DefKind::TypeAlias(_)) {
            continue;
          }
          let alias_file = alias_data.file;
          let alias_span = alias_data.span;
          if pinned.iter().all(|l| l.hir.file != alias_file) {
            if let Some(foreign) = state.hir_lowered.get(&alias_file).cloned() {
              pinned.push(foreign);
            }
          }
          import_links.push(ImportDaLink::Body {
            local: named.local,
            alias_file,
            alias_span,
          });
        }
        Some(ImportedAliasLink::TypeId(ty)) => {
          import_links.push(ImportDaLink::Nullary {
            local: named.local,
            ty,
          });
        }
        None => {}
      }
    }
  }

  let mut map = check::hir_body::DaTypeAliasMap::from_lowered(lowered);
  for link in import_links {
    match link {
      ImportDaLink::Body {
        local,
        alias_file,
        alias_span,
      } => {
        let Some(foreign) = pinned.iter().find(|l| l.hir.file == alias_file) else {
          continue;
        };
        map.register_file_aliases(foreign);
        let Some(hir_def) = foreign
          .defs
          .iter()
          .find(|d| d.path.kind == hir_js::DefKind::TypeAlias && d.span == alias_span)
        else {
          continue;
        };
        let Some(export_name) = foreign.names.resolve(hir_def.name) else {
          continue;
        };
        let Some(body) = map
          .by_qualified
          .get(&(alias_file.0, export_name.to_string()))
          .copied()
        else {
          continue;
        };
        map.link_alias_body(local, body);
      }
      ImportDaLink::Nullary { local, ty } => {
        map.link_nullary_exempt(
          local,
          check::hir_body::type_id_is_da_exempt(&state.store, ty),
        );
      }
    }
  }
  map
}

enum ImportedAliasLink {
  Def(DefId),
  TypeId(TypeId),
}

fn resolve_imported_type_alias_link(
  state: &ProgramState,
  start: DefId,
) -> Option<ImportedAliasLink> {
  let mut current = start;
  for _ in 0..8 {
    let data = state.def_data.get(&current)?;
    match &data.kind {
      DefKind::TypeAlias(_) => return Some(ImportedAliasLink::Def(current)),
      DefKind::Import(imp) => {
        let ImportTarget::File(target_file) = &imp.target else {
          return None;
        };
        let exports = state.files.get(target_file).map(|f| &f.exports)?;
        let entry = exports.get(&imp.original)?;
        if let Some(def) = entry.def {
          current = def;
          continue;
        }
        if let Some(ty) = entry.type_id {
          return Some(ImportedAliasLink::TypeId(ty));
        }
        return None;
      }
      _ => return None,
    }
  }
  None
}

pub(super) fn prop_type(store: &tti::TypeStore, ty: TypeId, name: &str) -> Option<TypeId> {
  match store.type_kind(ty).clone() {
    tti::TypeKind::Object(obj) => {
      let obj = store.object(obj);
      let shape = store.shape(obj.shape);
      for prop in shape.properties.iter() {
        if let tti::PropKey::String(sym) = prop.key {
          if store.name(sym) == name {
            return Some(prop.data.ty);
          }
        }
      }
      let probe_key = if name.parse::<f64>().is_ok() {
        tti::PropKey::Number(0)
      } else {
        tti::PropKey::String(store.intern_name(String::new()))
      };
      for indexer in shape.indexers.iter() {
        if crate::type_queries::indexer_accepts_key(&probe_key, indexer.key_type, store) {
          return Some(indexer.value_type);
        }
      }
      None
    }
    tti::TypeKind::Union(members) => {
      let mut collected = Vec::new();
      for member in members {
        if let Some(ty) = prop_type(store, member, name) {
          collected.push(ty);
        }
      }
      if collected.is_empty() {
        None
      } else {
        Some(store.union(collected))
      }
    }
    _ => None,
  }
}
