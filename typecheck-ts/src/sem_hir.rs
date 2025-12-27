use diagnostics::TextRange;
use hir_js::{
  DefKind as HirDefKind, Export, ExportKind as HirExportKind, Import, ImportEqualsTarget,
  ImportKind as HirImportKind, LowerResult,
};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::{ModuleDecl, ModuleName};
use semantic_js::ts as sem_ts;

pub(crate) fn sem_hir_from_lower(ast: &Node<TopLevel>, lowered: &LowerResult) -> sem_ts::HirFile {
  let resolve_name = |name| lowered.names.resolve(name).unwrap_or_default().to_string();
  let namespace_spans: Vec<TextRange> = lowered
    .defs
    .iter()
    .filter(|d| matches!(d.path.kind, HirDefKind::Namespace | HirDefKind::Module))
    .map(|d| d.span)
    .collect();
  let mut decls = Vec::new();
  for def_id in lowered.hir.items.iter() {
    let Some(idx) = lowered.def_index.get(def_id) else {
      continue;
    };
    let Some(def) = lowered.defs.get(*idx) else {
      continue;
    };
    let name = resolve_name(def.path.name);
    let mapped = map_def_kind(def.path.kind);
    let Some(kind) = mapped else {
      continue;
    };
    let exported = if def.is_exported {
      if def.is_default_export {
        sem_ts::Exported::Default
      } else {
        sem_ts::Exported::Named
      }
    } else {
      sem_ts::Exported::No
    };
    decls.push(sem_ts::Decl {
      def_id: def.id,
      name,
      kind,
      is_ambient: def.is_ambient,
      is_global: def.in_global,
      exported,
      span: def.span,
    });
  }

  let imports: Vec<_> = lowered
    .hir
    .imports
    .iter()
    .filter_map(|import| map_import_from_lower(import, &resolve_name))
    .collect();
  let import_equals: Vec<sem_ts::ImportEquals> = Vec::new();
  let exports: Vec<_> = lowered
    .hir
    .exports
    .iter()
    .filter(|export| {
      !namespace_spans
        .iter()
        .any(|span| export.span.start >= span.start && export.span.end <= span.end)
    })
    .filter_map(|export| map_export_from_lower(export, &resolve_name))
    .collect();
  let module_kind = if imports.is_empty()
    && import_equals.is_empty()
    && exports.is_empty()
    && decls
      .iter()
      .all(|decl| matches!(decl.exported, sem_ts::Exported::No))
  {
    sem_ts::ModuleKind::Script
  } else {
    sem_ts::ModuleKind::Module
  };

  sem_ts::HirFile {
    file_id: sem_ts::FileId(lowered.hir.file.0),
    module_kind,
    file_kind: match lowered.hir.file_kind {
      hir_js::FileKind::Dts => sem_ts::FileKind::Dts,
      hir_js::FileKind::Ts
      | hir_js::FileKind::Js
      | hir_js::FileKind::Jsx
      | hir_js::FileKind::Tsx => sem_ts::FileKind::Ts,
    },
    decls,
    imports,
    import_equals,
      exports,
      export_as_namespace: Vec::new(),
    ambient_modules: collect_ambient_modules(ast.stx.body.as_slice()),
  }
}

fn map_def_kind(kind: HirDefKind) -> Option<sem_ts::DeclKind> {
  match kind {
    HirDefKind::Function => Some(sem_ts::DeclKind::Function),
    HirDefKind::Class => Some(sem_ts::DeclKind::Class),
    HirDefKind::Var => Some(sem_ts::DeclKind::Var),
    HirDefKind::Interface => Some(sem_ts::DeclKind::Interface),
    HirDefKind::TypeAlias => Some(sem_ts::DeclKind::TypeAlias),
    HirDefKind::Enum => Some(sem_ts::DeclKind::Enum),
    HirDefKind::Namespace | HirDefKind::Module => Some(sem_ts::DeclKind::Namespace),
    HirDefKind::ImportBinding => None,
    _ => None,
  }
}

fn map_import_from_lower(
  import: &Import,
  resolve_name: &impl Fn(hir_js::NameId) -> String,
) -> Option<sem_ts::Import> {
  match &import.kind {
    HirImportKind::Es(es) => {
      let default = es.default.as_ref().map(|binding| sem_ts::ImportDefault {
        local: resolve_name(binding.local),
        local_span: binding.span,
        is_type_only: es.is_type_only,
      });
      let namespace = es
        .namespace
        .as_ref()
        .map(|binding| sem_ts::ImportNamespace {
          local: resolve_name(binding.local),
          local_span: binding.span,
          is_type_only: es.is_type_only,
        });
      let named = es
        .named
        .iter()
        .map(|spec| sem_ts::ImportNamed {
          imported: resolve_name(spec.imported),
          local: resolve_name(spec.local),
          is_type_only: es.is_type_only || spec.is_type_only,
          imported_span: spec.span,
          local_span: spec.span,
        })
        .collect();
      Some(sem_ts::Import {
        specifier: es.specifier.value.clone(),
        specifier_span: es.specifier.span,
        default,
        namespace,
        named,
        is_type_only: es.is_type_only,
      })
    }
    HirImportKind::ImportEquals(import_equals) => match &import_equals.target {
      ImportEqualsTarget::Module(specifier) => Some(sem_ts::Import {
        specifier: specifier.value.clone(),
        specifier_span: specifier.span,
        default: None,
        namespace: Some(sem_ts::ImportNamespace {
          local: resolve_name(import_equals.local.local),
          local_span: import_equals.local.span,
          is_type_only: false,
        }),
        named: Vec::new(),
        is_type_only: false,
      }),
      ImportEqualsTarget::Path(_) => None,
    },
  }
}

fn map_export_from_lower(
  export: &Export,
  resolve_name: &impl Fn(hir_js::NameId) -> String,
) -> Option<sem_ts::Export> {
  match &export.kind {
    HirExportKind::Named(named) => {
      let items = named
        .specifiers
        .iter()
        .map(|spec| {
          let local = resolve_name(spec.local);
          let exported_name = resolve_name(spec.exported);
          let exported = if exported_name == local {
            None
          } else {
            Some(exported_name)
          };
          let exported_span = exported.as_ref().map(|_| spec.span);
          sem_ts::ExportSpecifier {
            local,
            exported,
            local_span: spec.span,
            exported_span,
          }
        })
        .collect();
      Some(sem_ts::Export::Named(sem_ts::NamedExport {
        specifier: named.source.as_ref().map(|s| s.value.clone()),
        specifier_span: named.source.as_ref().map(|s| s.span),
        items,
        is_type_only: named.is_type_only,
      }))
    }
    HirExportKind::ExportAll(all) => Some(sem_ts::Export::All(sem_ts::ExportAll {
      specifier: all.source.value.clone(),
      is_type_only: all.is_type_only,
      specifier_span: all.source.span,
      alias: all.alias.as_ref().map(|a| resolve_name(a.exported)),
      alias_span: all.alias.as_ref().map(|a| a.span),
    })),
    HirExportKind::Default(_) => None,
    HirExportKind::Assignment(_) => Some(sem_ts::Export::ExportAssignment {
      expr: String::new(),
      span: export.span,
    }),
  }
}

fn collect_ambient_modules(stmts: &[Node<Stmt>]) -> Vec<sem_ts::AmbientModule> {
  stmts
    .iter()
    .filter_map(|stmt| match stmt.stx.as_ref() {
      Stmt::ModuleDecl(module) => match module.stx.name {
        ModuleName::String(_) => Some(lower_ambient_module(module.stx.as_ref())),
        _ => None,
      },
      _ => None,
    })
    .collect()
}

fn lower_ambient_module(module: &ModuleDecl) -> sem_ts::AmbientModule {
  let name = match &module.name {
    ModuleName::Identifier(name) | ModuleName::String(name) => name.clone(),
  };
  let name_span = TextRange::new(module.name_loc.start_u32(), module.name_loc.end_u32());
  let ambient_modules = module
    .body
    .as_ref()
    .map(|body| collect_ambient_modules(body))
    .unwrap_or_default();
  sem_ts::AmbientModule {
    name,
    name_span,
    decls: Vec::new(),
    imports: Vec::new(),
    import_equals: Vec::new(),
    exports: Vec::new(),
    export_as_namespace: Vec::new(),
    ambient_modules,
  }
}
