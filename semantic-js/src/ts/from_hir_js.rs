use crate::ts::{
  Decl, DeclKind, Export, ExportAll, ExportSpecifier, Exported, FileKind, HirFile, Import,
  ImportDefault, ImportNamed, ImportNamespace, ModuleKind, NamedExport,
};
use diagnostics::TextRange;
use hir_js::{DefId, DefKind, FileKind as HirFileKind, LowerResult};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;
use std::collections::{BTreeMap, HashMap, HashSet};

/// Convert a lowered `hir-js` file into the `semantic-js` TS binder input model.
///
/// This adapter preserves `DefId`s from `hir-js` so downstream semantics and type
/// checking can correlate binder declarations with lowered HIR data without
/// renumbering.
pub fn lower_to_ts_hir(ast: &Node<TopLevel>, lower: &LowerResult) -> HirFile {
  let file_id = lower.hir.file;
  let mut imports = Vec::new();
  let mut exports = Vec::new();
  let mut exported: HashMap<DefId, Exported> = HashMap::new();

  // Track module syntax to determine module vs script semantics.
  let mut has_module_syntax = false;

  let item_ids: HashSet<DefId> = lower.hir.items.iter().copied().collect();

  for stmt in ast.stx.body.iter() {
    let stmt_range = to_range(stmt.loc);
    match stmt.stx.as_ref() {
      Stmt::Import(import) => {
        has_module_syntax = true;
        let mut default = None;
        if let Some(pat) = import.stx.default.as_ref() {
          if let Some(name) = pat_name(&pat.stx.pat) {
            default = Some(ImportDefault {
              local_span: to_range(pat.loc),
              local: name,
              is_type_only: import.stx.type_only,
            });
          }
        }

        let mut namespace = None;
        let mut named = Vec::new();
        match &import.stx.names {
          Some(ImportNames::All(pat)) => {
            if let Some(name) = pat_name(&pat.stx.pat) {
              namespace = Some(ImportNamespace {
                local: name,
                local_span: to_range(pat.loc),
                is_type_only: import.stx.type_only,
              });
            }
          }
          Some(ImportNames::Specific(list)) => {
            for entry in list {
              if let Some(local) = pat_name(&entry.stx.alias.stx.pat) {
                named.push(ImportNamed {
                  imported: entry.stx.importable.as_str().to_string(),
                  local,
                  is_type_only: import.stx.type_only || entry.stx.type_only,
                  imported_span: to_range(entry.loc),
                  local_span: to_range(entry.stx.alias.loc),
                });
              }
            }
          }
          None => {}
        }

        imports.push(Import {
          specifier: import.stx.module.clone(),
          specifier_span: stmt_range,
          default,
          namespace,
          named,
          is_type_only: import.stx.type_only,
        });
      }
      Stmt::ExportList(list) => {
        has_module_syntax = true;
        match &list.stx.names {
          ExportNames::All(alias) => {
            if alias.is_none() {
              if let Some(specifier) = list.stx.from.clone() {
                exports.push(Export::All(ExportAll {
                  specifier_span: stmt_range,
                  specifier,
                  is_type_only: list.stx.type_only,
                }));
              }
            }
          }
          ExportNames::Specific(names) => {
            let mut items = Vec::new();
            let mut locals_to_export = Vec::new();
            for name in names {
              let local = name.stx.exportable.as_str().to_string();
              let exported_name = name.stx.alias.stx.name.clone();
              let exported_span = if exported_name == local {
                None
              } else {
                Some(to_range(name.stx.alias.loc))
              };
              items.push(ExportSpecifier {
                local,
                exported: if exported_span.is_some() {
                  Some(exported_name)
                } else {
                  None
                },
                local_span: to_range(name.loc),
                exported_span,
              });
              if list.stx.from.is_none() {
                let export_kind = if exported_span.is_some() && name.stx.alias.stx.name == "default"
                {
                  Exported::Default
                } else {
                  Exported::Named
                };
                locals_to_export.push((name.stx.exportable.as_str(), export_kind));
              }
            }
            exports.push(Export::Named(NamedExport {
              specifier: list.stx.from.clone(),
              specifier_span: list.stx.from.as_ref().map(|_| stmt_range),
              items,
              is_type_only: list.stx.type_only || names.iter().all(|n| n.stx.type_only),
            }));
            for (name, export_kind) in locals_to_export {
              mark_defs_with_name(
                &item_ids,
                &lower.defs,
                &lower.def_index,
                &lower.names,
                name,
                export_kind.clone(),
                &mut exported,
              );
            }
          }
        }
      }
      Stmt::ExportDefaultExpr(_) => {
        has_module_syntax = true;
        mark_defs_in_span(
          &item_ids,
          &lower.defs,
          &lower.def_index,
          &lower.hir.items,
          stmt_range,
          Some(DefKind::ExportAlias),
          Exported::Default,
          &mut exported,
        );
      }
      Stmt::ExportAssignmentDecl(assign) => {
        has_module_syntax = true;
        exports.push(Export::ExportAssignment {
          expr: format!("{:?}", assign.stx.expression.stx),
          span: stmt_range,
        });
      }
      Stmt::ImportTypeDecl(import_type) => {
        has_module_syntax = true;
        let named = import_type
          .stx
          .names
          .iter()
          .map(|n| ImportNamed {
            imported: n.imported.clone(),
            local: n.local.clone().unwrap_or_else(|| n.imported.clone()),
            is_type_only: true,
            imported_span: stmt_range,
            local_span: stmt_range,
          })
          .collect();
        imports.push(Import {
          specifier: import_type.stx.module.clone(),
          specifier_span: stmt_range,
          default: None,
          namespace: None,
          named,
          is_type_only: true,
        });
      }
      Stmt::ExportTypeDecl(export_type) => {
        has_module_syntax = true;
        let items = export_type
          .stx
          .names
          .iter()
          .map(|n| ExportSpecifier {
            local: n.local.clone(),
            exported: n.exported.clone(),
            local_span: stmt_range,
            exported_span: n.exported.as_ref().map(|_| stmt_range),
          })
          .collect();
        exports.push(Export::Named(NamedExport {
          specifier: export_type.stx.module.clone(),
          specifier_span: export_type.stx.module.as_ref().map(|_| stmt_range),
          items,
          is_type_only: true,
        }));
      }
      Stmt::VarDecl(var) => {
        if var.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Var),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::FunctionDecl(func) => {
        if func.stx.export || func.stx.export_default {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Function),
            if func.stx.export_default {
              Exported::Default
            } else {
              Exported::Named
            },
            &mut exported,
          );
        }
      }
      Stmt::ClassDecl(class_decl) => {
        if class_decl.stx.export || class_decl.stx.export_default {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Class),
            if class_decl.stx.export_default {
              Exported::Default
            } else {
              Exported::Named
            },
            &mut exported,
          );
        }
      }
      Stmt::InterfaceDecl(intf) => {
        if intf.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Interface),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::TypeAliasDecl(alias) => {
        if alias.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::TypeAlias),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::EnumDecl(en) => {
        if en.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Enum),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::NamespaceDecl(ns) => {
        if ns.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Namespace),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::ModuleDecl(module) => {
        if module.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Module),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::AmbientVarDecl(av) => {
        if av.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Var),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::AmbientFunctionDecl(af) => {
        if af.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Function),
            Exported::Named,
            &mut exported,
          );
        }
      }
      Stmt::AmbientClassDecl(ac) => {
        if ac.stx.export {
          has_module_syntax = true;
          mark_defs_in_span(
            &item_ids,
            &lower.defs,
            &lower.def_index,
            &lower.hir.items,
            stmt_range,
            Some(DefKind::Class),
            Exported::Named,
            &mut exported,
          );
        }
      }
      _ => {}
    }
  }

  let module_kind = if has_module_syntax {
    ModuleKind::Module
  } else {
    ModuleKind::Script
  };

  // Ambient declarations participate in exports for modules unless they augment global.
  if matches!(module_kind, ModuleKind::Module) {
    for def_id in &lower.hir.items {
      if exported.contains_key(def_id) {
        continue;
      }
      let def = def_by_id(*def_id, &lower.defs, &lower.def_index);
      if def.is_ambient && !def.in_global {
        exported.insert(*def_id, Exported::Named);
      }
    }
  }

  let mut decls = Vec::new();
  for def_id in lower.hir.items.iter().copied() {
    let def = def_by_id(def_id, &lower.defs, &lower.def_index);
    let kind = match def.path.kind {
      DefKind::Function => Some(DeclKind::Function),
      DefKind::Class => Some(DeclKind::Class),
      DefKind::Var => Some(DeclKind::Var),
      DefKind::Interface => Some(DeclKind::Interface),
      DefKind::TypeAlias => Some(DeclKind::TypeAlias),
      DefKind::Enum => Some(DeclKind::Enum),
      DefKind::Namespace | DefKind::Module => Some(DeclKind::Namespace),
      DefKind::ImportBinding => Some(DeclKind::ImportBinding),
      DefKind::ExportAlias => {
        if exported.get(&def_id) == Some(&Exported::Default) {
          Some(DeclKind::Var)
        } else {
          None
        }
      }
      _ => None,
    };
    if let Some(kind) = kind {
      let name = lower
        .names
        .resolve(def.name)
        .unwrap_or("<anon>")
        .to_string();
      let exported = exported.get(&def_id).cloned().unwrap_or(Exported::No);
      decls.push(Decl {
        def_id,
        name,
        kind,
        is_ambient: def.is_ambient,
        is_global: def.in_global,
        exported,
        span: def.span,
      });
    }
  }

  HirFile {
    file_id,
    module_kind,
    file_kind: match lower.hir.file_kind {
      HirFileKind::Dts => FileKind::Dts,
      _ => FileKind::Ts,
    },
    decls,
    imports,
    exports,
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
  }
}

fn def_by_id<'a>(
  def_id: DefId,
  defs: &'a [hir_js::DefData],
  def_index: &BTreeMap<DefId, usize>,
) -> &'a hir_js::DefData {
  let idx = def_index
    .get(&def_id)
    .copied()
    .expect("def present in index");
  &defs[idx]
}

fn mark_defs_with_name(
  items: &HashSet<DefId>,
  defs: &[hir_js::DefData],
  def_index: &BTreeMap<DefId, usize>,
  names: &hir_js::NameInterner,
  name: &str,
  exported: Exported,
  out: &mut HashMap<DefId, Exported>,
) {
  for def_id in items {
    let def = def_by_id(*def_id, defs, def_index);
    if names.resolve(def.name) == Some(name) {
      out.entry(*def_id).or_insert(exported.clone());
    }
  }
}

fn mark_defs_in_span(
  items: &HashSet<DefId>,
  defs: &[hir_js::DefData],
  def_index: &BTreeMap<DefId, usize>,
  top_level: &[DefId],
  span: TextRange,
  kind: Option<DefKind>,
  exported: Exported,
  out: &mut HashMap<DefId, Exported>,
) {
  for def_id in top_level.iter().copied() {
    if !items.contains(&def_id) {
      continue;
    }
    let def = def_by_id(def_id, defs, def_index);
    if def.span.start >= span.start && def.span.end <= span.end {
      if let Some(k) = kind {
        if def.path.kind != k {
          continue;
        }
      }
      out.entry(def_id).or_insert(exported.clone());
    }
  }
}

fn pat_name(pat: &Node<Pat>) -> Option<String> {
  match pat.stx.as_ref() {
    Pat::Id(id) => Some(id.stx.name.clone()),
    _ => None,
  }
}

fn to_range(loc: Loc) -> TextRange {
  TextRange::new(loc.start_u32(), loc.end_u32())
}
