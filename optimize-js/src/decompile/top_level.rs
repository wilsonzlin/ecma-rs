use super::foreign::ForeignBindings;
use parse_js::ast::expr::pat::{IdPat, Pat};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{PatDecl, VarDecl, VarDeclMode, VarDeclarator};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::loc::Loc;

pub fn foreign_var_decl(bindings: &ForeignBindings) -> Option<Node<Stmt>> {
  if bindings.is_empty() {
    return None;
  }

  let declarators = bindings
    .iter()
    .map(|binding| {
      let pat = Pat::Id(Node::new(
        Loc(0, 0),
        IdPat {
          name: binding.ident.clone(),
        },
      ));
      let pat_decl = PatDecl {
        pat: Node::new(Loc(0, 0), pat),
      };
      VarDeclarator {
        pattern: Node::new(Loc(0, 0), pat_decl),
        definite_assignment: false,
        type_annotation: None,
        initializer: None,
      }
    })
    .collect();

  let decl = VarDecl {
    export: false,
    mode: VarDeclMode::Let,
    declarators,
  };

  Some(Node::new(
    Loc(0, 0),
    Stmt::VarDecl(Node::new(Loc(0, 0), decl)),
  ))
}

pub fn prepend_foreign_decls(stmts: &mut Vec<Node<Stmt>>, bindings: &ForeignBindings) {
  if let Some(decl) = foreign_var_decl(bindings) {
    stmts.insert(0, decl);
  }
}

pub fn build_top_level(mut body: Vec<Node<Stmt>>, bindings: &ForeignBindings) -> Node<TopLevel> {
  prepend_foreign_decls(&mut body, bindings);
  Node::new(Loc(0, 0), TopLevel { body })
}
