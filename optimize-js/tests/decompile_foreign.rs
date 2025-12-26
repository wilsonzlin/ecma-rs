#[path = "common/mod.rs"]
mod common;
use common::compile_source;
use optimize_js::decompile::{collect_foreign_bindings, prepend_foreign_decls, ForeignBindings};
use optimize_js::{Program, TopLevelMode};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;

fn compile(source: &str, mode: TopLevelMode) -> Program {
  compile_source(source, mode, false)
}

fn var_decl_names(stmt: &Node<Stmt>) -> Vec<String> {
  match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl
      .stx
      .declarators
      .iter()
      .map(|decl| match decl.pattern.stx.pat.stx.as_ref() {
        parse_js::ast::expr::pat::Pat::Id(id) => id.stx.name.clone(),
        other => panic!("unexpected pattern in declarator: {other:?}"),
      })
      .collect(),
    other => panic!("expected var decl, got {other:?}"),
  }
}

fn binding_names(bindings: &ForeignBindings) -> Vec<String> {
  bindings
    .iter()
    .map(|binding| binding.ident.clone())
    .collect()
}

#[test]
fn captured_variable_generates_foreign_binding() {
  let source = r#"
    (() => {
      let captured = 0;
      const inner = () => {
        captured = captured + 1;
      };
      inner();
    })();
  "#;

  let program = compile(source, TopLevelMode::Module);
  let bindings = collect_foreign_bindings(&program);

  assert_eq!(binding_names(&bindings), vec!["__f0".to_string()]);

  let mut stmts = Vec::new();
  prepend_foreign_decls(&mut stmts, &bindings);
  assert_eq!(var_decl_names(&stmts[0]), vec!["__f0".to_string()]);
}

#[test]
fn collisions_with_unknown_names_use_alternate_prefix() {
  let source = r#"
    (() => {
      let captured = 0;
      const inner = () => {
        captured = captured + 1;
      };
      __f0 = captured;
      inner();
    })();
  "#;

  let program = compile(source, TopLevelMode::Module);
  let bindings = collect_foreign_bindings(&program);

  assert_eq!(binding_names(&bindings), vec!["__ecma_f0".to_string()]);

  let mut stmts = Vec::new();
  prepend_foreign_decls(&mut stmts, &bindings);
  assert_eq!(var_decl_names(&stmts[0]), vec!["__ecma_f0".to_string()]);
}
