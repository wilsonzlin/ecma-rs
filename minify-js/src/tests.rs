use crate::{minify, minify_with_options, Dialect, FileId, MinifyOptions, Severity, TopLevelMode};
use parse_js::ast::expr::jsx::JsxElemChild;
use parse_js::ast::expr::Expr;
use parse_js::ast::func::FuncBody;
use parse_js::ast::import_export::ImportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse, parse_with_options, ParseOptions, SourceType};

fn minified(mode: TopLevelMode, src: &str) -> String {
  let mut out = Vec::new();
  minify(mode, src, &mut out).unwrap();
  String::from_utf8(out).unwrap()
}

fn minified_program(
  mode: TopLevelMode,
  input_dialect: Dialect,
  output_dialect: Dialect,
  src: &str,
) -> (String, Node<TopLevel>) {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(mode).with_dialect(input_dialect),
    src,
    &mut out,
  )
  .unwrap();
  let output = String::from_utf8(out).unwrap();
  let parsed = parse_with_options(
    &output,
    ParseOptions {
      dialect: output_dialect,
      source_type: match mode {
        TopLevelMode::Global => SourceType::Script,
        TopLevelMode::Module => SourceType::Module,
      },
    },
  )
  .expect("output should parse as JavaScript");
  (output, parsed)
}

fn iife_body_from_stmt(stmt: &Node<Stmt>) -> &Vec<Node<Stmt>> {
  let expr = match stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let call = match expr.stx.expr.stx.as_ref() {
    Expr::Call(call) => call,
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma-wrapped call, got {other:?}"),
      }
    }
    other => panic!("expected IIFE call, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  match func
    .stx
    .func
    .stx
    .body
    .as_ref()
    .expect("IIFE should have a body")
  {
    FuncBody::Block(body) => body,
    other => panic!("expected block body, got {other:?}"),
  }
}

#[test]
fn test_shadow_safety() {
  let result = minified(
    TopLevelMode::Global,
    "let x=1;(()=>{let y=x;let x=2;return y})();",
  );
  assert_eq!(result, "let x=1;(()=>{let a=b;let b=2;return a;})();");
}

#[test]
fn test_unknown_globals_not_shadowed() {
  let result = minified(
    TopLevelMode::Global,
    "console.log(x);(()=>{let console=1;})();",
  );
  assert_eq!(result, "console.log(x);(()=>{let a=1;})();");
}

#[test]
fn test_module_export_bindings_preserved() {
  let result = minified(TopLevelMode::Module, "export const x=1; const y=2;");
  assert_eq!(result, "export const x=1;const a=2;");
}

#[test]
fn returns_diagnostics_on_parse_error() {
  let mut output = Vec::new();
  let diagnostics = minify(TopLevelMode::Global, "let =", &mut output).unwrap_err();
  assert_eq!(diagnostics.len(), 1);
  let diagnostic = &diagnostics[0];
  assert!(diagnostic.code.as_str().starts_with("PS"));
  assert_eq!(diagnostic.primary.file, FileId(0));
  assert_eq!(diagnostic.severity, Severity::Error);
}

#[test]
fn test_export_function_inner_locals_renamed() {
  let result = minified(
    TopLevelMode::Module,
    "export function foo(){let bar=1;return bar;}",
  );
  assert_eq!(result, "export function foo(){let a=1;return a;}");
}

#[test]
fn test_minify_determinism() {
  let src =
    "const foo=1; const qux=2; function bar(){ let baz=foo+qux; return baz; } export { bar };";
  let first = minified(TopLevelMode::Module, src);
  let second = minified(TopLevelMode::Module, src);
  assert_eq!(first, second);
}

#[test]
fn readme_example_is_parseable() {
  let code = "const main = () => { let my_first_variable = 1; };";
  let result = minified(TopLevelMode::Global, code);
  parse(&result).expect("minified output should be parseable JavaScript");
}

#[test]
fn test_with_statement_disables_renaming() {
  let src = "with ({x:2}){x}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, "with({x:2}){x;}");
}

#[test]
fn test_direct_eval_disables_renaming() {
  let src = "function f(){let x;eval(\"x\");}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, src);
}

#[test]
fn test_shadowed_eval_allows_renaming() {
  let src = "function f(eval){let x;eval(\"x\");}";
  let result = minified(TopLevelMode::Global, src);
  assert_eq!(result, "function f(a){let b;a(\"x\");}");
}

#[test]
fn test_with_in_nested_scope_only_disables_that_scope() {
  let src = "function outer(){let top=1;function inner(obj){let value=obj.v;with(obj){value;}return value;}return inner({v:top})+top;}";
  let result = minified(TopLevelMode::Module, src);
  assert_eq!(
    result,
    "function a(){let a=1;function b(obj){let value=obj.v;with(obj){value;}return value;}return b({v:a})+a;}"
  );
}

#[test]
fn erases_type_annotations_and_aliases() {
  let src = r#"
    type Alias = { foo: string };
    interface Foo { bar: number }
    const value: number = (foo as any) satisfies Alias ? 1 : 2;
    function wrap<T>(item: T): T { return item; }
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(_) => {}
    other => panic!("expected var decl, got {other:?}"),
  }
  match parsed.stx.body[1].stx.as_ref() {
    Stmt::FunctionDecl(_) => {}
    other => panic!("expected function decl, got {other:?}"),
  }
}

#[test]
fn erases_type_parameters_from_functions() {
  let src = "const wrap = <T>(value: T): T => value; const result: string = wrap<string>(\"x\");";
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
}

#[test]
fn preserves_tsx_and_jsx_content() {
  let src = r#"
    import type { ReactNode } from "react";
    const element: ReactNode = <div className="x">{value as number}</div>;
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Tsx, Dialect::Jsx, src);
  assert_eq!(parsed.stx.body.len(), 1);
  let decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected var decl, got {other:?}"),
  };
  let initializer = decl
    .stx
    .declarators
    .first()
    .and_then(|decl| decl.initializer.as_ref())
    .expect("initializer should exist");
  let jsx = match initializer.stx.as_ref() {
    Expr::JsxElem(elem) => elem,
    other => panic!("expected JSX element, got {other:?}"),
  };
  let expr_child = jsx
    .stx
    .children
    .iter()
    .find_map(|child| match child {
      JsxElemChild::Expr(expr) => Some(expr),
      _ => None,
    })
    .expect("expected jsx expression child");
  match expr_child.stx.value.stx.as_ref() {
    Expr::Id(_) => {}
    other => panic!("type assertions should be erased from JSX expressions, got {other:?}"),
  }
}

#[test]
fn drops_type_only_imports() {
  let src = r#"
    import type { Foo } from "./types";
    import { type Bar, baz } from "./mod";
    export type { Foo as FooType };
    export const value = baz;
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::Import(import) => {
      assert_eq!(import.stx.module, "./mod");
      match import.stx.names.as_ref() {
        Some(ImportNames::Specific(names)) => assert_eq!(names.len(), 1),
        other => panic!("expected single named import, got {other:?}"),
      }
    }
    other => panic!("expected remaining value import, got {other:?}"),
  }
  assert!(matches!(parsed.stx.body[1].stx.as_ref(), Stmt::VarDecl(_)));
}

#[test]
fn lowers_import_equals_require() {
  let src = r#"
    import foo = require("bar");
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 1);
  let decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected var decl, got {other:?}"),
  };
  assert_eq!(decl.stx.mode, VarDeclMode::Const);
  let initializer = decl
    .stx
    .declarators
    .first()
    .and_then(|declarator| declarator.initializer.as_ref())
    .expect("initializer should exist");
  match initializer.stx.as_ref() {
    Expr::Call(call) => match call.stx.callee.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "require"),
      other => panic!("expected require call, got {other:?}"),
    },
    other => panic!("expected require initializer, got {other:?}"),
  }
}

#[test]
fn lowers_export_assignment_to_module_exports() {
  let src = r#"
    const value = 1;
    export = value;
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  let export_stmt = parsed.stx.body.last().expect("module.exports assignment");
  let expr_stmt = match export_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assignment = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  assert_eq!(assignment.stx.operator, OperatorName::Assignment);
  match assignment.stx.left.stx.as_ref() {
    Expr::Member(member) => {
      assert_eq!(member.stx.right, "exports");
      match member.stx.left.stx.as_ref() {
        Expr::Id(id) => assert_eq!(id.stx.name, "module"),
        other => panic!("expected module identifier, got {other:?}"),
      }
    }
    other => panic!("expected module.exports assignment, got {other:?}"),
  }
}

#[test]
fn drops_type_only_import_equals() {
  let src = r#"import type foo = require("bar");"#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(parsed.stx.body.is_empty());
}

#[test]
fn lowers_runtime_numeric_enum() {
  let src = "export enum E { A, B = 2, C }";
  let (_output, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => {
      assert!(decl.stx.export);
      assert_eq!(decl.stx.mode, VarDeclMode::Var);
    }
    other => panic!("expected enum var decl, got {other:?}"),
  }
  let body = iife_body_from_stmt(&parsed.stx.body[1]);
  let mut reverse_mappings = 0;
  let mut has_auto_increment = false;
  for stmt in body.iter() {
    if let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() {
      if let Expr::Binary(bin) = expr_stmt.stx.expr.stx.as_ref() {
        if let Expr::ComputedMember(member) = bin.stx.left.stx.as_ref() {
          if let Expr::Binary(inner) = member.stx.member.stx.as_ref() {
            reverse_mappings += 1;
            if let Expr::LitNum(num) = inner.stx.right.stx.as_ref() {
              if num.stx.value.0 == 3.0 {
                has_auto_increment = true;
              }
            }
          }
        }
      }
    }
  }
  assert_eq!(reverse_mappings, 3);
  assert!(has_auto_increment);
}

#[test]
fn lowers_string_enum_members() {
  let src = "enum Names { A = \"x\" }";
  let (_output, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  let body = iife_body_from_stmt(&parsed.stx.body[1]);
  assert_eq!(body.len(), 1);
  let expr_stmt = match body[0].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum assignment, got {other:?}"),
  };
  match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) => match bin.stx.left.stx.as_ref() {
      Expr::ComputedMember(member) => match member.stx.member.stx.as_ref() {
        Expr::LitStr(lit) => assert_eq!(lit.stx.value, "A"),
        other => panic!("expected string member assignment, got {other:?}"),
      },
      other => panic!("expected computed member assignment, got {other:?}"),
    },
    other => panic!("expected binary assignment, got {other:?}"),
  }
}

#[test]
fn lowers_namespace_exports() {
  let src = r#"
    namespace N {
      export const x = 1;
      export function f() { return x; }
      const y = f();
    }
  "#;
  let (_output, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => assert_eq!(decl.stx.mode, VarDeclMode::Var),
    other => panic!("expected namespace declaration lowered to var, got {other:?}"),
  }
  let body = iife_body_from_stmt(&parsed.stx.body[1]);
  assert!(body
    .iter()
    .any(|stmt| matches!(stmt.stx.as_ref(), Stmt::VarDecl(_))));
  let mut exported_props = Vec::new();
  for stmt in body.iter() {
    if let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() {
      if let Expr::Binary(bin) = expr_stmt.stx.expr.stx.as_ref() {
        if let Expr::ComputedMember(member) = bin.stx.left.stx.as_ref() {
          if let Expr::LitStr(prop) = member.stx.member.stx.as_ref() {
            exported_props.push(prop.stx.value.clone());
          }
        }
      }
    }
  }
  assert!(exported_props.contains(&"x".to_string()));
  assert!(exported_props.contains(&"f".to_string()));
}
