#[cfg(feature = "emit-minify")]
use crate::{
  clear_last_emit_backend_for_tests, force_hir_emit_failure_for_tests, last_emit_backend_for_tests,
  EmitBackend,
};
use crate::{minify, minify_with_options, Dialect, FileId, MinifyOptions, Severity, TopLevelMode};
use parse_js::ast::expr::jsx::JsxElemChild;
use parse_js::ast::expr::Expr;
use parse_js::ast::import_export::ImportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse, parse_with_options, ParseOptions, SourceType};
#[cfg(feature = "emit-minify")]
use serde_json::to_value;

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

#[cfg(feature = "emit-minify")]
fn minified_with_backend_options(options: MinifyOptions, src: &str) -> (String, EmitBackend) {
  clear_last_emit_backend_for_tests();
  let mut out = Vec::new();
  minify_with_options(options, src, &mut out).unwrap();
  let backend = last_emit_backend_for_tests().expect("emitter backend should be recorded");
  (String::from_utf8(out).unwrap(), backend)
}

#[cfg(feature = "emit-minify")]
fn assert_outputs_parse_to_same_ast(
  mode: TopLevelMode,
  dialect: Dialect,
  hir_output: &str,
  ast_output: &str,
) {
  let parse_opts = ParseOptions {
    dialect,
    source_type: match mode {
      TopLevelMode::Global => SourceType::Script,
      TopLevelMode::Module => SourceType::Module,
    },
  };
  let hir_parsed = parse_with_options(hir_output, parse_opts).expect("HIR output should parse");
  let ast_parsed = parse_with_options(ast_output, parse_opts).expect("AST output should parse");
  let hir_json = to_value(&hir_parsed).expect("serialize HIR AST");
  let ast_json = to_value(&ast_parsed).expect("serialize AST AST");
  assert_eq!(hir_json, ast_json);
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

#[cfg(feature = "emit-minify")]
#[test]
fn hir_emitter_matches_ast_output() {
  let src =
    "function wrap(value){return value+1;} const result=wrap(2); const doubled=wrap(result);";
  let (hir_output, hir_backend) = minified_with_backend_options(
    MinifyOptions::new(TopLevelMode::Global).with_dialect(Dialect::Js),
    src,
  );
  assert_eq!(hir_backend, EmitBackend::Hir);

  force_hir_emit_failure_for_tests();
  let (ast_output, ast_backend) = minified_with_backend_options(
    MinifyOptions::new(TopLevelMode::Global).with_dialect(Dialect::Js),
    src,
  );
  assert_eq!(ast_backend, EmitBackend::Ast);
  assert_outputs_parse_to_same_ast(TopLevelMode::Global, Dialect::Js, &hir_output, &ast_output);
}

#[cfg(feature = "emit-minify")]
#[test]
fn hir_emitter_can_differ_from_ast_output() {
  // Expression statements starting with arrow functions are one example where
  // the emitters may differ in parentheses without affecting semantics.
  let src = "long_parameter_name=>long_parameter_name;";
  let (hir_output, hir_backend) = minified_with_backend_options(
    MinifyOptions::new(TopLevelMode::Global).with_dialect(Dialect::Js),
    src,
  );
  assert_eq!(hir_backend, EmitBackend::Hir);

  force_hir_emit_failure_for_tests();
  let (ast_output, ast_backend) = minified_with_backend_options(
    MinifyOptions::new(TopLevelMode::Global).with_dialect(Dialect::Js),
    src,
  );
  assert_eq!(ast_backend, EmitBackend::Ast);

  assert_ne!(
    hir_output, ast_output,
    "HIR emission should be accepted even when its formatting differs from the AST emitter"
  );
  assert_outputs_parse_to_same_ast(TopLevelMode::Global, Dialect::Js, &hir_output, &ast_output);
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
fn lowers_runtime_enums_to_parseable_js() {
  let src = r#"
    export enum Num { A, B = 5, C }
    export enum Str { A = "a", B = `b` }
    export declare enum Gone { A }
  "#;
  let (code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(!code.contains("Gone"));
  assert_eq!(parsed.stx.body.len(), 4);

  let first = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum var decl, got {other:?}"),
  };
  assert!(first.stx.export);

  let third = match parsed.stx.body[2].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum var decl, got {other:?}"),
  };
  assert!(third.stx.export);
}

#[test]
fn lowers_runtime_namespaces_to_parseable_js() {
  let src = r#"
    export namespace NS {
      export const x: number = 1;
      export function get() { return x; }
      export namespace Inner {
        export const y = 2;
      }
    }
    export declare namespace Gone { export const z: number; }
  "#;
  let (code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert!(!code.contains("Gone"));
  assert_eq!(parsed.stx.body.len(), 2);
  let decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected namespace var decl, got {other:?}"),
  };
  assert!(decl.stx.export);
}

#[test]
fn lowers_runtime_modules_to_parseable_js() {
  let src = r#"
    module Mod {
      export const x = 1;
    }
  "#;
  let (_code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
}

#[test]
fn minifies_ts_enums_and_namespaces_deterministically() {
  let src = r#"
    export enum E { A, B }
    export namespace N { export const x = 1; }
  "#;
  let first = minified(TopLevelMode::Module, src);
  let second = minified(TopLevelMode::Module, src);
  assert_eq!(first, second);
}

#[test]
fn rewrites_enum_member_references_in_initializers() {
  let src = r#"enum E { A = 1, B = A, C }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => match bin.stx.right.stx.as_ref()
    {
      Expr::Call(call) => call,
      other => panic!("expected comma call rhs, got {other:?}"),
    },
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let outer_assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let outer_left = match outer_assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  let name_assign = match outer_left.stx.member.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected inner assignment, got {other:?}"),
  };
  match name_assign.stx.right.stx.as_ref() {
    Expr::ComputedMember(_) => {}
    other => panic!("expected rewritten enum member reference, got {other:?}"),
  }
}

#[test]
fn string_enum_aliases_do_not_emit_reverse_mappings() {
  let src = r#"enum S { A = "a", B = A }"#;
  let mut parsed = parse_with_options(
    src,
    ParseOptions {
      dialect: Dialect::Ts,
      source_type: SourceType::Module,
    },
  )
  .expect("input should parse");
  crate::ts_erase::erase_types(FileId(0), TopLevelMode::Module, src, &mut parsed)
    .expect("type erasure should succeed");

  assert_eq!(parsed.stx.body.len(), 2);
  let iife = match parsed.stx.body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected enum IIFE expr stmt, got {other:?}"),
  };
  let call = match iife.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => match bin.stx.right.stx.as_ref()
    {
      Expr::Call(call) => call,
      other => panic!("expected comma call rhs, got {other:?}"),
    },
    other => panic!("expected comma expression, got {other:?}"),
  };
  let func = match call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function callee, got {other:?}"),
  };
  let body = match func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let b_stmt = body.get(1).expect("B member statement");
  let expr_stmt = match b_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  let left = match assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member assignment, got {other:?}"),
  };
  assert!(matches!(left.stx.member.stx.as_ref(), Expr::LitStr(_)));
  assert!(matches!(
    assign.stx.right.stx.as_ref(),
    Expr::ComputedMember(_)
  ));
}
