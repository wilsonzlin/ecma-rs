use crate::ts::{
  AmbientModule, Decl, DeclKind, Export, ExportAll, ExportAsNamespace, ExportSpecifier, Exported,
  FileKind, HirFile, Import, ImportDefault, ImportEquals, ImportEqualsTarget, ImportNamed,
  ImportNamespace, ModuleKind, NamedExport, TypeImport as TsTypeImport,
};
use diagnostics::TextRange;
use hir_js::{DefId, DefKind, ExportKind, FileKind as HirFileKind, ImportKind, LowerResult};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::import_export::{ExportNames, ImportNames};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{ImportEqualsRhs, ModuleName};
use parse_js::loc::Loc;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

/// Convert a lowered `hir-js` file into the `semantic-js` TS binder input model.
///
/// This adapter preserves `DefId`s from `hir-js` so downstream semantics and type
/// checking can correlate binder declarations with lowered HIR data without
/// renumbering.
pub fn lower_to_ts_hir(ast: &Node<TopLevel>, lower: &LowerResult) -> HirFile {
  let file_id = lower.hir.file;
  let item_ids: HashSet<DefId> = lower.hir.items.iter().copied().collect();

  let imports_by_span: HashMap<_, _> = lower
    .hir
    .imports
    .iter()
    .map(|import| (import.span, import))
    .collect();
  let exports_by_span: HashMap<_, _> = lower
    .hir
    .exports
    .iter()
    .map(|export| (export.span, export))
    .collect();
  let import_specifier_span = |range: TextRange| -> Option<TextRange> {
    imports_by_span
      .get(&range)
      .and_then(|import| match &import.kind {
        ImportKind::Es(es) => Some(es.specifier.span),
        ImportKind::ImportEquals(eq) => match &eq.target {
          hir_js::ImportEqualsTarget::Module(spec) => Some(spec.span),
          _ => None,
        },
      })
  };
  let export_specifier_span = |range: TextRange| -> Option<TextRange> {
    exports_by_span
      .get(&range)
      .and_then(|export| match &export.kind {
        ExportKind::Named(named) => named.source.as_ref().map(|s| s.span),
        ExportKind::ExportAll(all) => Some(all.source.span),
        _ => None,
      })
  };

  let block = lower_block(
    &ast.stx.body,
    lower,
    Some(&item_ids),
    &import_specifier_span,
    &export_specifier_span,
  );

  let module_kind = if block.has_module_syntax {
    ModuleKind::Module
  } else {
    ModuleKind::Script
  };

  let finalized = finalize_block(block, lower, module_kind);
  let type_imports = collect_type_imports(lower);

  HirFile {
    file_id,
    module_kind,
    file_kind: match lower.hir.file_kind {
      HirFileKind::Dts => FileKind::Dts,
      _ => FileKind::Ts,
    },
    decls: finalized.decls,
    imports: finalized.imports,
    type_imports,
    import_equals: finalized.import_equals,
    exports: finalized.exports,
    export_as_namespace: finalized.export_as_namespace,
    ambient_modules: finalized.ambient_modules,
  }
}

fn collect_type_imports(lower: &LowerResult) -> Vec<TsTypeImport> {
  let mut seen = BTreeSet::<(String, TextRange)>::new();
  for arenas in lower.types.values() {
    for ty in arenas.type_exprs.iter() {
      match &ty.kind {
        hir_js::hir::TypeExprKind::TypeRef(type_ref) => {
          if let hir_js::hir::TypeName::Import(import) = &type_ref.name {
            if let Some(module) = &import.module {
              seen.insert((module.clone(), ty.span));
            }
          }
        }
        hir_js::hir::TypeExprKind::TypeQuery(name) => {
          if let hir_js::hir::TypeName::Import(import) = name {
            if let Some(module) = &import.module {
              seen.insert((module.clone(), ty.span));
            }
          }
        }
        hir_js::hir::TypeExprKind::Import(import) => {
          seen.insert((import.module.clone(), ty.span));
        }
        _ => {}
      }
    }
  }
  seen
    .into_iter()
    .map(|(specifier, specifier_span)| TsTypeImport {
      specifier,
      specifier_span,
    })
    .collect()
}

struct BlockResult {
  local_defs: Vec<DefId>,
  exported: HashMap<DefId, Exported>,
  imports: Vec<Import>,
  import_equals: Vec<ImportEquals>,
  exports: Vec<Export>,
  export_as_namespace: Vec<ExportAsNamespace>,
  ambient_modules: Vec<AmbientModule>,
  has_module_syntax: bool,
}

struct LoweredBlock {
  decls: Vec<Decl>,
  imports: Vec<Import>,
  import_equals: Vec<ImportEquals>,
  exports: Vec<Export>,
  export_as_namespace: Vec<ExportAsNamespace>,
  ambient_modules: Vec<AmbientModule>,
}

fn lower_block(
  stmts: &[Node<Stmt>],
  lower: &LowerResult,
  allowed_defs: Option<&HashSet<DefId>>,
  import_specifier_span: &impl Fn(TextRange) -> Option<TextRange>,
  export_specifier_span: &impl Fn(TextRange) -> Option<TextRange>,
) -> BlockResult {
  let targets = collect_def_targets(stmts);
  let local_defs = resolve_def_targets(&targets, lower, allowed_defs);
  let defs_by_name = build_name_map(&local_defs, lower);

  let mut result = BlockResult {
    local_defs,
    exported: HashMap::new(),
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules: Vec::new(),
    has_module_syntax: false,
  };

  for stmt in stmts.iter() {
    let stmt_range = to_range(stmt.loc);
    match stmt.stx.as_ref() {
      Stmt::Import(import) => {
        result.has_module_syntax = true;
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

        result.imports.push(Import {
          specifier: import.stx.module.clone(),
          specifier_span: import_specifier_span(stmt_range).unwrap_or(stmt_range),
          default,
          namespace,
          named,
          is_type_only: import.stx.type_only,
        });
      }
      Stmt::ImportEqualsDecl(import_eq) => {
        let target = match &import_eq.stx.rhs {
          ImportEqualsRhs::Require { module } => {
            result.has_module_syntax = true;
            ImportEqualsTarget::Require {
              specifier: module.clone(),
              specifier_span: import_specifier_span(stmt_range).unwrap_or(stmt_range),
            }
          }
          ImportEqualsRhs::EntityName { path } => ImportEqualsTarget::EntityName {
            path: path.clone(),
            span: stmt_range,
          },
        };

        if import_eq.stx.export {
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::ImportBinding),
            Exported::Named,
            &mut result.exported,
          );
        }

        result.import_equals.push(ImportEquals {
          local: import_eq.stx.name.clone(),
          local_span: span_for_name(stmt.loc, &import_eq.stx.name),
          target,
          is_exported: import_eq.stx.export,
        });
      }
      Stmt::ExportList(list) => {
        result.has_module_syntax = true;
        match &list.stx.names {
          ExportNames::All(alias) => {
            if let Some(specifier) = list.stx.from.clone() {
              result.exports.push(Export::All(ExportAll {
                specifier_span: export_specifier_span(stmt_range).unwrap_or(stmt_range),
                specifier,
                is_type_only: list.stx.type_only,
                alias: alias.as_ref().map(|a| a.stx.name.clone()),
                alias_span: alias.as_ref().map(|a| to_range(a.loc)),
              }));
            }
          }
          ExportNames::Specific(names) => {
            let mut items = Vec::new();
            for name in names {
              let local = name.stx.exportable.as_str().to_string();
              let exported_name = name.stx.alias.stx.name.clone();
              let exported_span = if exported_name == local {
                None
              } else {
                Some(to_range(name.stx.alias.loc))
              };
              items.push(ExportSpecifier {
                local: local.clone(),
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
                mark_defs_with_name(
                  &defs_by_name,
                  &local,
                  export_kind.clone(),
                  &mut result.exported,
                );
              }
            }
            result.exports.push(Export::Named(NamedExport {
              specifier: list.stx.from.clone(),
              specifier_span: list
                .stx
                .from
                .as_ref()
                .map(|_| export_specifier_span(stmt_range).unwrap_or(stmt_range)),
              items,
              is_type_only: list.stx.type_only || names.iter().all(|n| n.stx.type_only),
            }));
          }
        }
      }
      Stmt::ExportDefaultExpr(_) => {
        result.has_module_syntax = true;
        mark_defs_in_span(
          &result.local_defs,
          lower,
          stmt_range,
          Some(DefKind::ExportAlias),
          Exported::Default,
          &mut result.exported,
        );
      }
      Stmt::ExportAssignmentDecl(assign) => {
        result.has_module_syntax = true;
        let expr_span = to_range(assign.stx.expression.loc);
        let path = entity_name_path(&assign.stx.expression);
        result.exports.push(Export::ExportAssignment {
          path,
          expr_span,
          span: stmt_range,
        });
      }
      Stmt::ExportAsNamespaceDecl(decl) => {
        result.has_module_syntax = true;
        result.export_as_namespace.push(ExportAsNamespace {
          name: decl.stx.name.clone(),
          span: stmt_range,
        });
      }
      Stmt::ImportTypeDecl(import_type) => {
        result.has_module_syntax = true;
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
        result.imports.push(Import {
          specifier: import_type.stx.module.clone(),
          specifier_span: import_specifier_span(stmt_range).unwrap_or(stmt_range),
          default: None,
          namespace: None,
          named,
          is_type_only: true,
        });
      }
      Stmt::ExportTypeDecl(export_type) => {
        result.has_module_syntax = true;
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
        result.exports.push(Export::Named(NamedExport {
          specifier: export_type.stx.module.clone(),
          specifier_span: export_type
            .stx
            .module
            .as_ref()
            .map(|_| export_specifier_span(stmt_range).unwrap_or(stmt_range)),
          items,
          is_type_only: true,
        }));
      }
      Stmt::VarDecl(var) => {
        if var.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Var),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::FunctionDecl(func) => {
        if func.stx.export || func.stx.export_default {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Function),
            if func.stx.export_default {
              Exported::Default
            } else {
              Exported::Named
            },
            &mut result.exported,
          );
        }
      }
      Stmt::ClassDecl(class_decl) => {
        if class_decl.stx.export || class_decl.stx.export_default {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Class),
            if class_decl.stx.export_default {
              Exported::Default
            } else {
              Exported::Named
            },
            &mut result.exported,
          );
        }
      }
      Stmt::InterfaceDecl(intf) => {
        if intf.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Interface),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::TypeAliasDecl(alias) => {
        if alias.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::TypeAlias),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::EnumDecl(en) => {
        if en.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Enum),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::NamespaceDecl(ns) => {
        if ns.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Namespace),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::ModuleDecl(module) => match &module.stx.name {
        ModuleName::Identifier(_) => {
          if module.stx.export {
            result.has_module_syntax = true;
            mark_defs_in_span(
              &result.local_defs,
              lower,
              stmt_range,
              Some(DefKind::Module),
              Exported::Named,
              &mut result.exported,
            );
          }
        }
        ModuleName::String(spec) => {
          if module.stx.export {
            result.has_module_syntax = true;
          }
          let name_span = to_range(module.stx.name_loc);
          let nested = lower_block(
            module.stx.body.as_deref().unwrap_or(&[]),
            lower,
            None,
            import_specifier_span,
            export_specifier_span,
          );
          let nested = finalize_block(nested, lower, ModuleKind::Module);
          result.ambient_modules.push(AmbientModule {
            name: spec.clone(),
            name_span,
            decls: nested.decls,
            imports: nested.imports,
            type_imports: Vec::new(),
            import_equals: nested.import_equals,
            exports: nested.exports,
            export_as_namespace: nested.export_as_namespace,
            ambient_modules: nested.ambient_modules,
          });
        }
      },
      Stmt::GlobalDecl(global) => {
        let nested = lower_block(
          &global.stx.body,
          lower,
          allowed_defs,
          import_specifier_span,
          export_specifier_span,
        );
        result.local_defs.extend(nested.local_defs);
        result.exported.extend(nested.exported);
        result.imports.extend(nested.imports);
        result.import_equals.extend(nested.import_equals);
        result.exports.extend(nested.exports);
        result
          .export_as_namespace
          .extend(nested.export_as_namespace);
        result.ambient_modules.extend(nested.ambient_modules);
        result.has_module_syntax |= nested.has_module_syntax;
      }
      Stmt::AmbientVarDecl(av) => {
        if av.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Var),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::AmbientFunctionDecl(af) => {
        if af.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Function),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      Stmt::AmbientClassDecl(ac) => {
        if ac.stx.export {
          result.has_module_syntax = true;
          mark_defs_in_span(
            &result.local_defs,
            lower,
            stmt_range,
            Some(DefKind::Class),
            Exported::Named,
            &mut result.exported,
          );
        }
      }
      _ => {}
    }
  }

  result
}

fn finalize_block(
  block: BlockResult,
  lower: &LowerResult,
  module_kind: ModuleKind,
) -> LoweredBlock {
  let mut exported = block.exported;
  if matches!(module_kind, ModuleKind::Module) {
    for def_id in &block.local_defs {
      if exported.contains_key(def_id) {
        continue;
      }
      let def = def_by_id(*def_id, &lower.defs, &lower.def_index);
      // Ambient namespaces/modules implicitly export their members. However,
      // `.d.ts` files that become modules via top-level module syntax (e.g.
      // `export = Foo`) do *not* implicitly export top-level declarations.
      //
      // `hir-js` nests some declarations under intermediate defs (e.g. var
      // bindings are children of `VarDeclarator` defs), so checking
      // `def.parent.is_some()` alone would still incorrectly treat top-level
      // ambient `const Foo: ...` declarations as additional exports. Instead,
      // require that the declaration has a namespace/module ancestor.
      let mut nested_in_namespace_or_module = false;
      let mut parent = def.parent;
      while let Some(parent_id) = parent {
        let parent_def = def_by_id(parent_id, &lower.defs, &lower.def_index);
        if matches!(parent_def.path.kind, DefKind::Namespace | DefKind::Module) {
          nested_in_namespace_or_module = true;
          break;
        }
        parent = parent_def.parent;
      }

      if def.is_ambient && !def.in_global && nested_in_namespace_or_module {
        exported.insert(*def_id, Exported::Named);
      }
    }
  }

  let mut decls = Vec::new();
  for def_id in block.local_defs.iter().copied() {
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

  LoweredBlock {
    decls,
    imports: block.imports,
    import_equals: block.import_equals,
    exports: block.exports,
    export_as_namespace: block.export_as_namespace,
    ambient_modules: block.ambient_modules,
  }
}

#[derive(Clone, Copy)]
struct DefTarget {
  span: TextRange,
  kind: DefKind,
}

fn collect_def_targets(stmts: &[Node<Stmt>]) -> Vec<DefTarget> {
  let mut targets = Vec::new();
  for stmt in stmts {
    let span = to_range(stmt.loc);
    match stmt.stx.as_ref() {
      Stmt::Import(import) => {
        if let Some(default) = &import.stx.default {
          targets.push(DefTarget {
            span: to_range(default.loc),
            kind: DefKind::ImportBinding,
          });
        }
        match &import.stx.names {
          Some(ImportNames::All(pat)) => targets.push(DefTarget {
            span: to_range(pat.loc),
            kind: DefKind::ImportBinding,
          }),
          Some(ImportNames::Specific(list)) => {
            for entry in list {
              targets.push(DefTarget {
                span: to_range(entry.stx.alias.loc),
                kind: DefKind::ImportBinding,
              });
            }
          }
          None => {}
        }
      }
      Stmt::VarDecl(var) => {
        for decl in var.stx.declarators.iter() {
          targets.push(DefTarget {
            span: to_range(decl.pattern.loc),
            kind: DefKind::Var,
          });
        }
      }
      Stmt::FunctionDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Function,
      }),
      Stmt::ClassDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Class,
      }),
      Stmt::InterfaceDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Interface,
      }),
      Stmt::TypeAliasDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::TypeAlias,
      }),
      Stmt::EnumDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Enum,
      }),
      Stmt::NamespaceDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Namespace,
      }),
      Stmt::ModuleDecl(module) => {
        if matches!(module.stx.name, ModuleName::Identifier(_)) {
          targets.push(DefTarget {
            span,
            kind: DefKind::Module,
          });
        }
      }
      Stmt::AmbientVarDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Var,
      }),
      Stmt::AmbientFunctionDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Function,
      }),
      Stmt::AmbientClassDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::Class,
      }),
      Stmt::GlobalDecl(global) => targets.extend(collect_def_targets(&global.stx.body)),
      Stmt::ExportDefaultExpr(_) => targets.push(DefTarget {
        span,
        kind: DefKind::ExportAlias,
      }),
      Stmt::ImportEqualsDecl(_) => targets.push(DefTarget {
        span,
        kind: DefKind::ImportBinding,
      }),
      _ => {}
    }
  }
  targets
}

fn resolve_def_targets(
  targets: &[DefTarget],
  lower: &LowerResult,
  allowed_defs: Option<&HashSet<DefId>>,
) -> Vec<DefId> {
  let mut selected = Vec::new();
  let mut seen = HashSet::new();
  for def in &lower.defs {
    if let Some(allowed) = allowed_defs {
      if !allowed.contains(&def.id) {
        continue;
      }
    }
    if targets
      .iter()
      .any(|target| target.span == def.span && target.kind == def.path.kind)
    {
      if seen.insert(def.id) {
        selected.push(def.id);
      }
    }
  }
  selected
}

fn build_name_map(local_defs: &[DefId], lower: &LowerResult) -> HashMap<String, Vec<DefId>> {
  let mut names: HashMap<String, Vec<DefId>> = HashMap::new();
  for def_id in local_defs {
    let def = def_by_id(*def_id, &lower.defs, &lower.def_index);
    if let Some(name) = lower.names.resolve(def.name) {
      names.entry(name.to_string()).or_default().push(*def_id);
    }
  }
  names
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
  available_defs: &HashMap<String, Vec<DefId>>,
  name: &str,
  exported: Exported,
  out: &mut HashMap<DefId, Exported>,
) {
  if let Some(defs) = available_defs.get(name) {
    for def_id in defs {
      out.entry(*def_id).or_insert(exported.clone());
    }
  }
}

fn mark_defs_in_span(
  local_defs: &[DefId],
  lower: &LowerResult,
  span: TextRange,
  kind: Option<DefKind>,
  exported: Exported,
  out: &mut HashMap<DefId, Exported>,
) {
  for def_id in local_defs.iter().copied() {
    let def = def_by_id(def_id, &lower.defs, &lower.def_index);
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

fn entity_name_path(expr: &Node<Expr>) -> Option<Vec<String>> {
  match expr.stx.as_ref() {
    Expr::Id(id) => Some(vec![id.stx.name.clone()]),
    Expr::Member(member) if !member.stx.optional_chaining => {
      let mut path = entity_name_path(&member.stx.left)?;
      path.push(member.stx.right.clone());
      Some(path)
    }
    _ => None,
  }
}

fn to_range(loc: Loc) -> TextRange {
  TextRange::new(loc.start_u32(), loc.end_u32())
}

fn span_for_name(loc: Loc, name: &str) -> TextRange {
  let range = to_range(loc);
  let len = name.len() as u32;
  if range.len() >= len {
    return range;
  }
  let end = range.start;
  let start = end.saturating_sub(len);
  TextRange::new(start, end)
}
