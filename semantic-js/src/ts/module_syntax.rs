use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::ast::ts_stmt::ImportEqualsRhs;

/// Returns `true` if the parsed file contains TypeScript/ECMAScript syntax that
/// makes it an external module (as opposed to a global script).
///
/// This mirrors TypeScript's "external module indicator" rules: only top-level
/// imports/exports (including `export import`) and exported declarations make a
/// file a module. Ambient module declarations like `declare module "pkg" {}`
/// intentionally do *not* count on their own.
pub fn ast_has_module_syntax(top: &Node<TopLevel>) -> bool {
  fn walk(stmts: &[Node<Stmt>]) -> bool {
    for stmt in stmts.iter() {
      match stmt.stx.as_ref() {
        Stmt::Import(_)
        | Stmt::ExportList(_)
        | Stmt::ExportDefaultExpr(_)
        | Stmt::ExportAssignmentDecl(_)
        | Stmt::ExportAsNamespaceDecl(_)
        | Stmt::ImportTypeDecl(_)
        | Stmt::ExportTypeDecl(_) => return true,
        Stmt::ImportEqualsDecl(import_equals) => match &import_equals.stx.rhs {
          // `import Foo = require("bar")` is a module indicator.
          ImportEqualsRhs::Require { .. } => return true,
          // `import Foo = Bar` is not a module indicator unless it is exported
          // (`export import Foo = Bar`).
          ImportEqualsRhs::EntityName { .. } => {
            if import_equals.stx.export {
              return true;
            }
          }
        },
        Stmt::VarDecl(var) => {
          if var.stx.export {
            return true;
          }
        }
        Stmt::FunctionDecl(func) => {
          if func.stx.export || func.stx.export_default {
            return true;
          }
        }
        Stmt::ClassDecl(class) => {
          if class.stx.export || class.stx.export_default {
            return true;
          }
        }
        Stmt::InterfaceDecl(interface) => {
          if interface.stx.export {
            return true;
          }
        }
        Stmt::TypeAliasDecl(alias) => {
          if alias.stx.export {
            return true;
          }
        }
        Stmt::EnumDecl(en) => {
          if en.stx.export {
            return true;
          }
        }
        Stmt::NamespaceDecl(ns) => {
          if ns.stx.export {
            return true;
          }
        }
        // `declare module "pkg" {}` does not make the file a module unless the
        // declaration itself is exported.
        Stmt::ModuleDecl(module) => {
          if module.stx.export {
            return true;
          }
        }
        Stmt::AmbientVarDecl(av) => {
          if av.stx.export {
            return true;
          }
        }
        Stmt::AmbientFunctionDecl(af) => {
          if af.stx.export {
            return true;
          }
        }
        Stmt::AmbientClassDecl(ac) => {
          if ac.stx.export {
            return true;
          }
        }
        // `declare global { ... }` blocks can contain module syntax that should
        // classify the whole file as a module.
        Stmt::GlobalDecl(global) => {
          if walk(&global.stx.body) {
            return true;
          }
        }
        _ => {}
      }
    }
    false
  }

  walk(&top.stx.body)
}

