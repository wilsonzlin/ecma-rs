use crate::execution_context::ModuleId;
use crate::module_graph::ModuleGraph;
use crate::ImportAttribute;
use crate::LoadedModuleRequest;
use crate::ModuleRequest;
use crate::RootId;
use crate::VmError;
use diagnostics::{Diagnostic, FileId};
use parse_js::ast::class_or_object::{
  ClassMember, ClassOrObjKey, ClassOrObjVal, ObjMember, ObjMemberType,
};
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::lit::{LitArrElem, LitTemplatePart};
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stmt::ForInOfLhs;
use parse_js::ast::stx::TopLevel;
use parse_js::lex::KEYWORDS_MAPPING;
use parse_js::operator::OperatorName;
use parse_js::token::TT;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};
use std::collections::HashSet;

/// Module linking/loading status.
///
/// This is a minimal subset of ECMA-262's `ModuleStatus` enum; additional states will be added as
/// module linking/evaluation are implemented.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, Default)]
pub enum ModuleStatus {
  #[default]
  New,
  Unlinked,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LocalExportEntry {
  pub export_name: String,
  pub local_name: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ImportName {
  Name(String),
  /// Corresponds to ECMA-262 `ImportName = all`, used by `export * as ns from "m"`.
  All,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IndirectExportEntry {
  pub export_name: String,
  pub module_request: ModuleRequest,
  pub import_name: ImportName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StarExportEntry {
  pub module_request: ModuleRequest,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BindingName {
  Name(String),
  Namespace,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResolvedBinding {
  pub module: ModuleId,
  pub binding_name: BindingName,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolveExportResult {
  Resolved(ResolvedBinding),
  NotFound,
  Ambiguous,
}

/// Cached data for a module's namespace object (`module.[[Namespace]]` in ECMA-262).
#[derive(Clone, Debug)]
pub(crate) struct ModuleNamespaceCache {
  pub object: RootId,
  pub exports: Vec<String>,
}

/// Source Text Module Record (ECMA-262).
#[derive(Clone, Debug, Default)]
pub struct SourceTextModuleRecord {
  pub requested_modules: Vec<ModuleRequest>,
  pub status: ModuleStatus,
  /// `[[HasTLA]]` – whether this module contains top-level `await`.
  pub has_tla: bool,
  pub local_export_entries: Vec<LocalExportEntry>,
  pub indirect_export_entries: Vec<IndirectExportEntry>,
  pub star_export_entries: Vec<StarExportEntry>,

  /// `[[LoadedModules]]` – a host-populated mapping from module requests to resolved module ids.
  pub loaded_modules: Vec<LoadedModuleRequest<ModuleId>>,

  /// `[[Namespace]]` – cached module namespace object + sorted `[[Exports]]` list.
  ///
  /// Note: the namespace object is rooted in the heap via a persistent [`RootId`] so it survives GC.
  pub(crate) namespace: Option<ModuleNamespaceCache>,
}

impl SourceTextModuleRecord {
  /// Returns the cached namespace export list (`[[Exports]]`) if a namespace object has been
  /// created.
  pub fn namespace_exports(&self) -> Option<&[String]> {
    self.namespace.as_ref().map(|ns| ns.exports.as_slice())
  }

  /// Parses a source text module using the `parse-js` front-end and extracts the module record
  /// fields needed by `GetExportedNames` and `ResolveExport`.
  ///
  /// This corresponds to the spec's `ParseModule` abstract operation, but only models the export
  /// entry lists and `[[RequestedModules]]`.
  pub fn parse(source: &str) -> Result<Self, VmError> {
    let opts = ParseOptions {
      dialect: Dialect::Ecma,
      source_type: SourceType::Module,
    };
    let top = parse_with_options(source, opts)
      .map_err(|err| VmError::Syntax(vec![err.to_diagnostic(FileId(0))]))?;

    let mut record = SourceTextModuleRecord::default();
    record.has_tla = module_contains_top_level_await(&top);

    for stmt in &top.stx.body {
      match &*stmt.stx {
        Stmt::Import(import_stmt) => {
          if import_stmt.stx.type_only {
            continue;
          }
          let req = module_request_from_specifier(
            &import_stmt.stx.module,
            import_stmt.stx.attributes.as_ref(),
          )?;
          push_requested_module(&mut record.requested_modules, req);
        }

        Stmt::ExportDefaultExpr(_) => {
          record.local_export_entries.push(LocalExportEntry {
            export_name: "default".to_string(),
            local_name: "*default*".to_string(),
          });
        }

        Stmt::ExportList(export_stmt) => {
          if export_stmt.stx.type_only {
            continue;
          }

          let from = match export_stmt.stx.from.as_ref() {
            Some(specifier) => Some(module_request_from_specifier(
              specifier,
              export_stmt.stx.attributes.as_ref(),
            )?),
            None => None,
          };
          if let Some(req) = &from {
            push_requested_module(&mut record.requested_modules, req.clone());
          }

          match (&export_stmt.stx.names, from) {
            (ExportNames::All(None), Some(req)) => {
              // `export * from "module"`
              record.star_export_entries.push(StarExportEntry { module_request: req });
            }
            (ExportNames::All(Some(alias)), Some(req)) => {
              // `export * as name from "module"`
              record.indirect_export_entries.push(IndirectExportEntry {
                export_name: alias.stx.name.clone(),
                module_request: req,
                import_name: ImportName::All,
              });
            }
            (ExportNames::Specific(names), Some(req)) => {
              // `export {x as y} from "module"`
              for name in names {
                record.indirect_export_entries.push(IndirectExportEntry {
                  export_name: name.stx.alias.stx.name.clone(),
                  module_request: req.clone(),
                  import_name: ImportName::Name(name.stx.exportable.as_str().to_string()),
                });
              }
            }
            (ExportNames::Specific(names), None) => {
              // `export {x as y}`
              for name in names {
                record.local_export_entries.push(LocalExportEntry {
                  export_name: name.stx.alias.stx.name.clone(),
                  local_name: name.stx.exportable.as_str().to_string(),
                });
              }
            }
            // `export *` without a `from` clause is not valid syntax; ignore.
            (ExportNames::All(_), None) => {}
          }
        }

        Stmt::VarDecl(var_decl) if var_decl.stx.export => {
          for declarator in &var_decl.stx.declarators {
            let pat = &declarator.pattern.stx.pat;
            let name = match &*pat.stx {
              Pat::Id(id) => id.stx.name.clone(),
              _ => return Err(VmError::Unimplemented("exported destructuring patterns")),
            };

            record.local_export_entries.push(LocalExportEntry {
              export_name: name.clone(),
              local_name: name,
            });
          }
        }

        Stmt::FunctionDecl(func) if func.stx.export || func.stx.export_default => {
          let local_name = func
            .stx
            .name
            .as_ref()
            .map(|n| n.stx.name.clone())
            .unwrap_or_else(|| "*default*".to_string());
          record.local_export_entries.push(LocalExportEntry {
            export_name: if func.stx.export {
              local_name.clone()
            } else {
              "default".to_string()
            },
            local_name,
          });
        }

        Stmt::ClassDecl(class) if class.stx.export || class.stx.export_default => {
          let local_name = class
            .stx
            .name
            .as_ref()
            .map(|n| n.stx.name.clone())
            .unwrap_or_else(|| "*default*".to_string());
          record.local_export_entries.push(LocalExportEntry {
            export_name: if class.stx.export {
              local_name.clone()
            } else {
              "default".to_string()
            },
            local_name,
          });
        }

        _ => {}
      }
    }

    Ok(record)
  }

  /// Implements ECMA-262 `GetExportedNames([exportStarSet])`.
  pub fn get_exported_names(&self, graph: &ModuleGraph, module: ModuleId) -> Vec<String> {
    self.get_exported_names_with_star_set(graph, module, &mut Vec::new())
  }

  pub fn get_exported_names_with_star_set(
    &self,
    graph: &ModuleGraph,
    module: ModuleId,
    export_star_set: &mut Vec<ModuleId>,
  ) -> Vec<String> {
    // 1. If exportStarSet contains module, then
    if export_star_set.contains(&module) {
      // a. Return a new empty List.
      return Vec::new();
    }

    // 2. Append module to exportStarSet.
    export_star_set.push(module);

    // 3. Let exportedNames be a new empty List.
    let mut exported_names = Vec::<String>::new();

    // 4. For each ExportEntry Record e of module.[[LocalExportEntries]], do
    for entry in &self.local_export_entries {
      // a. Append e.[[ExportName]] to exportedNames.
      exported_names.push(entry.export_name.clone());
    }

    // 5. For each ExportEntry Record e of module.[[IndirectExportEntries]], do
    for entry in &self.indirect_export_entries {
      // a. Append e.[[ExportName]] to exportedNames.
      exported_names.push(entry.export_name.clone());
    }

    // 6. For each ExportEntry Record e of module.[[StarExportEntries]], do
    for entry in &self.star_export_entries {
      // a. Let requestedModule be GetImportedModule(module, e.[[ModuleRequest]]).
      let Some(requested_module) = graph.get_imported_module(module, &entry.module_request) else {
        continue;
      };
      // b. Let starNames be requestedModule.GetExportedNames(exportStarSet).
      let star_names =
        graph
          .module(requested_module)
          .get_exported_names_with_star_set(graph, requested_module, export_star_set);

      // c. For each element n of starNames, do
      for name in star_names {
        // i. If SameValue(n, "default") is false, then
        if name == "default" {
          continue;
        }
        // 1. If exportedNames does not contain n, then
        if !exported_names.contains(&name) {
          // a. Append n to exportedNames.
          exported_names.push(name);
        }
      }
    }

    // 7. Return exportedNames.
    exported_names
  }

  /// Implements ECMA-262 `ResolveExport(exportName[, resolveSet])`.
  pub fn resolve_export(
    &self,
    graph: &ModuleGraph,
    module: ModuleId,
    export_name: &str,
  ) -> ResolveExportResult {
    self.resolve_export_with_set(graph, module, export_name, &mut Vec::new())
  }

  pub fn resolve_export_with_set(
    &self,
    graph: &ModuleGraph,
    module: ModuleId,
    export_name: &str,
    resolve_set: &mut Vec<(ModuleId, String)>,
  ) -> ResolveExportResult {
    // 1. For each Record { [[Module]], [[ExportName]] } r of resolveSet, do
    //    a. If module and r.[[Module]] are the same Module Record and SameValue(exportName, r.[[ExportName]]) is true, then
    //       i. Return null.
    if resolve_set
      .iter()
      .any(|(m, name)| *m == module && name == export_name)
    {
      return ResolveExportResult::NotFound;
    }

    // 2. Append the Record { [[Module]]: module, [[ExportName]]: exportName } to resolveSet.
    resolve_set.push((module, export_name.to_string()));

    // 3. For each ExportEntry Record e of module.[[LocalExportEntries]], do
    for entry in &self.local_export_entries {
      // a. If SameValue(exportName, e.[[ExportName]]) is true, then
      if entry.export_name == export_name {
        // i. Assert: module provides the direct binding for this export.
        // ii. Return ResolvedBinding Record { [[Module]]: module, [[BindingName]]: e.[[LocalName]] }.
        return ResolveExportResult::Resolved(ResolvedBinding {
          module,
          binding_name: BindingName::Name(entry.local_name.clone()),
        });
      }
    }

    // 4. For each ExportEntry Record e of module.[[IndirectExportEntries]], do
    for entry in &self.indirect_export_entries {
      // a. If SameValue(exportName, e.[[ExportName]]) is true, then
      if entry.export_name == export_name {
        // i. Let importedModule be GetImportedModule(module, e.[[ModuleRequest]]).
        let Some(imported_module) = graph.get_imported_module(module, &entry.module_request) else {
          return ResolveExportResult::NotFound;
        };
        // ii. If e.[[ImportName]] is all, then
        if entry.import_name == ImportName::All {
          // 1. Return ResolvedBinding Record { [[Module]]: importedModule, [[BindingName]]: namespace }.
          return ResolveExportResult::Resolved(ResolvedBinding {
            module: imported_module,
            binding_name: BindingName::Namespace,
          });
        }

        // iii. Else,
        // 1. Assert: e.[[ImportName]] is a String.
        // 2. Return importedModule.ResolveExport(e.[[ImportName]], resolveSet).
        let import_name = match &entry.import_name {
          ImportName::Name(name) => name,
          ImportName::All => {
            debug_assert!(false, "ImportName::All handled above");
            return ResolveExportResult::NotFound;
          }
        };
        return graph
          .module(imported_module)
          .resolve_export_with_set(graph, imported_module, import_name, resolve_set);
      }
    }

    // 5. If SameValue(exportName, "default") is true, then
    if export_name == "default" {
      // a. Return null.
      return ResolveExportResult::NotFound;
    }

    // 6. Let starResolution be null.
    let mut star_resolution: Option<ResolvedBinding> = None;

    // 7. For each ExportEntry Record e of module.[[StarExportEntries]], do
    for entry in &self.star_export_entries {
      // a. Let importedModule be GetImportedModule(module, e.[[ModuleRequest]]).
      let Some(imported_module) = graph.get_imported_module(module, &entry.module_request) else {
        continue;
      };
      // b. Let resolution be importedModule.ResolveExport(exportName, resolveSet).
      let resolution = graph
        .module(imported_module)
        .resolve_export_with_set(graph, imported_module, export_name, resolve_set);

      // c. If resolution is ambiguous, return ambiguous.
      if resolution == ResolveExportResult::Ambiguous {
        return ResolveExportResult::Ambiguous;
      }

      // d. If resolution is not null, then
      let ResolveExportResult::Resolved(resolution) = resolution else {
        continue;
      };

      // i. If starResolution is null, then
      let Some(existing) = &star_resolution else {
        // 1. Set starResolution to resolution.
        star_resolution = Some(resolution);
        continue;
      };

      // ii. Else,
      // 1. If resolution.[[Module]] and starResolution.[[Module]] are not the same Module Record, return ambiguous.
      // 2. If resolution.[[BindingName]] is not the same as starResolution.[[BindingName]], return ambiguous.
      if existing != &resolution {
        return ResolveExportResult::Ambiguous;
      }
    }

    // 8. Return starResolution.
    match star_resolution {
      Some(binding) => ResolveExportResult::Resolved(binding),
      None => ResolveExportResult::NotFound,
    }
  }
}

fn module_contains_top_level_await(top: &Node<TopLevel>) -> bool {
  stmt_list_contains_top_level_await(&top.stx.body)
}

fn stmt_list_contains_top_level_await(stmts: &[Node<Stmt>]) -> bool {
  stmts.iter().any(stmt_contains_top_level_await)
}

fn stmt_contains_top_level_await(stmt: &Node<Stmt>) -> bool {
  match &*stmt.stx {
    Stmt::Expr(expr_stmt) => expr_contains_top_level_await(&expr_stmt.stx.expr),
    Stmt::Block(block) => stmt_list_contains_top_level_await(&block.stx.body),
    Stmt::DoWhile(stmt) => {
      expr_contains_top_level_await(&stmt.stx.condition) || stmt_contains_top_level_await(&stmt.stx.body)
    }
    Stmt::If(stmt) => {
      expr_contains_top_level_await(&stmt.stx.test)
        || stmt_contains_top_level_await(&stmt.stx.consequent)
        || stmt
          .stx
          .alternate
          .as_ref()
          .is_some_and(stmt_contains_top_level_await)
    }
    Stmt::While(stmt) => {
      expr_contains_top_level_await(&stmt.stx.condition) || stmt_contains_top_level_await(&stmt.stx.body)
    }
    Stmt::ForTriple(stmt) => {
      (match &stmt.stx.init {
        parse_js::ast::stmt::ForTripleStmtInit::None => false,
        parse_js::ast::stmt::ForTripleStmtInit::Expr(expr) => expr_contains_top_level_await(expr),
        parse_js::ast::stmt::ForTripleStmtInit::Decl(decl) => var_decl_contains_top_level_await(&decl.stx),
      }) || stmt.stx.cond.as_ref().is_some_and(expr_contains_top_level_await)
        || stmt.stx.post.as_ref().is_some_and(expr_contains_top_level_await)
        || stmt_list_contains_top_level_await(&stmt.stx.body.stx.body)
    }
    Stmt::ForIn(stmt) => {
      for_in_of_lhs_contains_top_level_await(&stmt.stx.lhs)
        || expr_contains_top_level_await(&stmt.stx.rhs)
        || stmt_list_contains_top_level_await(&stmt.stx.body.stx.body)
    }
    Stmt::ForOf(stmt) => {
      if stmt.stx.await_ {
        return true;
      }
      for_in_of_lhs_contains_top_level_await(&stmt.stx.lhs)
        || expr_contains_top_level_await(&stmt.stx.rhs)
        || stmt_list_contains_top_level_await(&stmt.stx.body.stx.body)
    }
    Stmt::Label(stmt) => stmt_contains_top_level_await(&stmt.stx.statement),
    Stmt::Switch(stmt) => {
      expr_contains_top_level_await(&stmt.stx.test)
        || stmt
          .stx
          .branches
          .iter()
          .any(|branch| {
            branch.stx.case.as_ref().is_some_and(expr_contains_top_level_await)
              || stmt_list_contains_top_level_await(&branch.stx.body)
          })
    }
    Stmt::Throw(stmt) => expr_contains_top_level_await(&stmt.stx.value),
    Stmt::Try(stmt) => {
      stmt_list_contains_top_level_await(&stmt.stx.wrapped.stx.body)
        || stmt
          .stx
          .catch
          .as_ref()
          .is_some_and(|catch| stmt_list_contains_top_level_await(&catch.stx.body))
        || stmt
          .stx
          .finally
          .as_ref()
          .is_some_and(|finally| stmt_list_contains_top_level_await(&finally.stx.body))
    }
    Stmt::With(stmt) => {
      expr_contains_top_level_await(&stmt.stx.object) || stmt_contains_top_level_await(&stmt.stx.body)
    }

    // Import/export statements.
    Stmt::ExportDefaultExpr(stmt) => expr_contains_top_level_await(&stmt.stx.expression),
    Stmt::ExportList(stmt) => stmt
      .stx
      .attributes
      .as_ref()
      .is_some_and(expr_contains_top_level_await),
    Stmt::Import(stmt) => stmt
      .stx
      .attributes
      .as_ref()
      .is_some_and(expr_contains_top_level_await),

    // Declarations.
    Stmt::ClassDecl(stmt) => class_decl_contains_top_level_await(&stmt.stx),
    Stmt::VarDecl(stmt) => var_decl_contains_top_level_await(&stmt.stx),

    // Function-like boundaries: do not descend.
    Stmt::FunctionDecl(_) => false,

    // Everything else cannot contain `await` (or is syntax-error in modules).
    _ => false,
  }
}

fn var_decl_contains_top_level_await(decl: &parse_js::ast::stmt::decl::VarDecl) -> bool {
  decl.declarators.iter().any(|d| {
    pat_contains_top_level_await(&d.pattern.stx.pat)
      || d
        .initializer
        .as_ref()
        .is_some_and(expr_contains_top_level_await)
  })
}

fn for_in_of_lhs_contains_top_level_await(lhs: &ForInOfLhs) -> bool {
  match lhs {
    ForInOfLhs::Assign(pat) => pat_contains_top_level_await(pat),
    ForInOfLhs::Decl((_mode, pat_decl)) => pat_contains_top_level_await(&pat_decl.stx.pat),
  }
}

fn expr_contains_top_level_await(expr: &Node<Expr>) -> bool {
  match &*expr.stx {
    Expr::Unary(unary) => {
      if unary.stx.operator == OperatorName::Await {
        return true;
      }
      expr_contains_top_level_await(&unary.stx.argument)
    }
    Expr::UnaryPostfix(unary) => expr_contains_top_level_await(&unary.stx.argument),
    Expr::Binary(binary) => {
      expr_contains_top_level_await(&binary.stx.left) || expr_contains_top_level_await(&binary.stx.right)
    }
    Expr::Call(call) => {
      expr_contains_top_level_await(&call.stx.callee)
        || call
          .stx
          .arguments
          .iter()
          .any(|arg| expr_contains_top_level_await(&arg.stx.value))
    }
    Expr::ComputedMember(member) => {
      expr_contains_top_level_await(&member.stx.object) || expr_contains_top_level_await(&member.stx.member)
    }
    Expr::Cond(cond) => {
      expr_contains_top_level_await(&cond.stx.test)
        || expr_contains_top_level_await(&cond.stx.consequent)
        || expr_contains_top_level_await(&cond.stx.alternate)
    }
    Expr::Import(expr) => {
      expr_contains_top_level_await(&expr.stx.module)
        || expr
          .stx
          .attributes
          .as_ref()
          .is_some_and(expr_contains_top_level_await)
    }
    Expr::Member(member) => expr_contains_top_level_await(&member.stx.left),
    Expr::TaggedTemplate(template) => {
      expr_contains_top_level_await(&template.stx.function)
        || template
          .stx
          .parts
          .iter()
          .any(|part| matches!(part, LitTemplatePart::Substitution(expr) if expr_contains_top_level_await(expr)))
    }

    Expr::LitArr(arr) => arr.stx.elements.iter().any(|elem| match elem {
      LitArrElem::Single(expr) | LitArrElem::Rest(expr) => expr_contains_top_level_await(expr),
      LitArrElem::Empty => false,
    }),
    Expr::LitObj(obj) => obj.stx.members.iter().any(obj_member_contains_top_level_await),
    Expr::LitTemplate(template) => template.stx.parts.iter().any(|part| match part {
      LitTemplatePart::Substitution(expr) => expr_contains_top_level_await(expr),
      LitTemplatePart::String(_) => false,
    }),

    // Class expressions are not function boundaries: only method bodies are.
    Expr::Class(class) => class_expr_contains_top_level_await(&class.stx),

    // Patterns (can contain expressions via default values).
    Expr::ArrPat(arr) => arr_pat_contains_top_level_await(&arr.stx),
    Expr::IdPat(_) => false,
    Expr::ObjPat(obj) => obj_pat_contains_top_level_await(&obj.stx),

    // TypeScript wrappers around expressions.
    Expr::Instantiation(expr) => expr_contains_top_level_await(&expr.stx.expression),
    Expr::TypeAssertion(expr) => expr_contains_top_level_await(&expr.stx.expression),
    Expr::NonNullAssertion(expr) => expr_contains_top_level_await(&expr.stx.expression),
    Expr::SatisfiesExpr(expr) => expr_contains_top_level_await(&expr.stx.expression),

    // Function-like boundaries: do not descend.
    Expr::ArrowFunc(_) | Expr::Func(_) => false,

    // Everything else is leaf-like for our purposes.
    _ => false,
  }
}

fn pat_contains_top_level_await(pat: &Node<Pat>) -> bool {
  match &*pat.stx {
    Pat::Arr(arr) => arr_pat_contains_top_level_await(&arr.stx),
    Pat::Obj(obj) => obj_pat_contains_top_level_await(&obj.stx),
    Pat::AssignTarget(expr) => expr_contains_top_level_await(expr),
    Pat::Id(_) => false,
  }
}

fn arr_pat_contains_top_level_await(pat: &parse_js::ast::expr::pat::ArrPat) -> bool {
  pat.elements.iter().any(|elem| match elem {
    None => false,
    Some(elem) => {
      pat_contains_top_level_await(&elem.target)
        || elem
          .default_value
          .as_ref()
          .is_some_and(expr_contains_top_level_await)
    }
  }) || pat.rest.as_ref().is_some_and(pat_contains_top_level_await)
}

fn obj_pat_contains_top_level_await(pat: &parse_js::ast::expr::pat::ObjPat) -> bool {
  pat.properties.iter().any(|prop| {
    class_or_obj_key_contains_top_level_await(&prop.stx.key)
      || pat_contains_top_level_await(&prop.stx.target)
      || prop
        .stx
        .default_value
        .as_ref()
        .is_some_and(expr_contains_top_level_await)
  }) || pat.rest.as_ref().is_some_and(pat_contains_top_level_await)
}

fn class_decl_contains_top_level_await(class: &parse_js::ast::stmt::decl::ClassDecl) -> bool {
  class
    .decorators
    .iter()
    .any(|d| expr_contains_top_level_await(&d.stx.expression))
    || class
      .extends
      .as_ref()
      .is_some_and(expr_contains_top_level_await)
    || class
      .implements
      .iter()
      .any(expr_contains_top_level_await)
    || class
      .members
      .iter()
      .any(class_member_contains_top_level_await)
}

fn class_expr_contains_top_level_await(class: &parse_js::ast::expr::ClassExpr) -> bool {
  class
    .decorators
    .iter()
    .any(|d| expr_contains_top_level_await(&d.stx.expression))
    || class
      .extends
      .as_ref()
      .is_some_and(expr_contains_top_level_await)
    || class
      .members
      .iter()
      .any(class_member_contains_top_level_await)
}

fn class_member_contains_top_level_await(member: &Node<ClassMember>) -> bool {
  member
    .stx
    .decorators
    .iter()
    .any(|d| expr_contains_top_level_await(&d.stx.expression))
    || class_or_obj_key_contains_top_level_await(&member.stx.key)
    || class_or_obj_val_contains_top_level_await(&member.stx.val)
}

fn obj_member_contains_top_level_await(member: &Node<ObjMember>) -> bool {
  match &member.stx.typ {
    ObjMemberType::Valued { key, val } => {
      class_or_obj_key_contains_top_level_await(key) || class_or_obj_val_contains_top_level_await(val)
    }
    ObjMemberType::Shorthand { .. } => false,
    ObjMemberType::Rest { val } => expr_contains_top_level_await(val),
  }
}

fn class_or_obj_key_contains_top_level_await(key: &ClassOrObjKey) -> bool {
  match key {
    ClassOrObjKey::Direct(_) => false,
    ClassOrObjKey::Computed(expr) => expr_contains_top_level_await(expr),
  }
}

fn class_or_obj_val_contains_top_level_await(val: &ClassOrObjVal) -> bool {
  match val {
    // Function-like boundaries: do not descend.
    ClassOrObjVal::Getter(_) | ClassOrObjVal::Setter(_) | ClassOrObjVal::Method(_) => false,
    ClassOrObjVal::Prop(expr) => expr.as_ref().is_some_and(expr_contains_top_level_await),
    ClassOrObjVal::IndexSignature(_) => false,
    // Class static blocks are syntax-errors for `await`; don't scan them.
    ClassOrObjVal::StaticBlock(_) => false,
  }
}

fn module_request_from_specifier(
  specifier: &str,
  attributes: Option<&Node<Expr>>,
) -> Result<ModuleRequest, VmError> {
  Ok(ModuleRequest::new(
    specifier,
    with_clause_to_attributes(attributes)?,
  ))
}

fn push_requested_module(out: &mut Vec<ModuleRequest>, request: ModuleRequest) {
  if !out.iter().any(|existing| existing.spec_equal(&request)) {
    out.push(request);
  }
}

/// Implements `WithClauseToAttributes` (ECMA-262) for static import/export declarations.
fn with_clause_to_attributes(attributes: Option<&Node<Expr>>) -> Result<Vec<ImportAttribute>, VmError> {
  let Some(attributes) = attributes else {
    return Ok(Vec::new());
  };

  let Expr::LitObj(obj) = &*attributes.stx else {
    return Err(syntax_error(
      attributes.loc,
      "import attributes must be an object literal",
    ));
  };

  let mut seen = HashSet::<String>::new();
  let mut out = Vec::<ImportAttribute>::new();

  for member in &obj.stx.members {
    let (key, key_loc, value_expr) = match &member.stx.typ {
      ObjMemberType::Valued { key, val } => {
        let key_node = match key {
          ClassOrObjKey::Direct(direct) => direct,
          ClassOrObjKey::Computed(_) => {
            return Err(syntax_error(
              member.loc,
              "computed import attribute keys are not allowed",
            ));
          }
        };

        let is_ident_or_keyword =
          key_node.stx.tt == TT::Identifier || KEYWORDS_MAPPING.contains_key(&key_node.stx.tt);
        let is_string = key_node.stx.tt == TT::LiteralString;
        if !is_ident_or_keyword && !is_string {
          return Err(syntax_error(
            key_node.loc,
            "import attribute keys must be identifiers, keywords, or string literals",
          ));
        }

        let value_expr = match val {
          ClassOrObjVal::Prop(Some(expr)) => expr,
          _ => {
            return Err(syntax_error(
              member.loc,
              "import attribute entries must be simple key/value properties",
            ));
          }
        };

        (key_node.stx.key.clone(), key_node.loc, value_expr)
      }
      ObjMemberType::Shorthand { .. } => {
        return Err(syntax_error(
          member.loc,
          "shorthand properties are not allowed in import attributes",
        ));
      }
      ObjMemberType::Rest { .. } => {
        return Err(syntax_error(
          member.loc,
          "spread properties are not allowed in import attributes",
        ));
      }
    };

    if !seen.insert(key.clone()) {
      return Err(syntax_error(key_loc, "duplicate import attribute key"));
    }

    let value = match &*value_expr.stx {
      Expr::LitStr(str_lit) => str_lit.stx.value.clone(),
      _ => {
        return Err(syntax_error(
          value_expr.loc,
          "import attribute values must be string literals",
        ));
      }
    };

    out.push(ImportAttribute { key, value });
  }

  // Sort by key in lexicographic UTF-16 code unit order (ECMA-262 requirement).
  out.sort_by(|a, b| crate::cmp_utf16(&a.key, &b.key));
  Ok(out)
}

fn syntax_error(loc: parse_js::loc::Loc, message: &str) -> VmError {
  let span = loc.to_diagnostics_span(FileId(0));
  VmError::Syntax(vec![Diagnostic::error("VMJS0001", message, span)])
}
