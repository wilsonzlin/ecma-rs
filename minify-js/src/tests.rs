#[cfg(feature = "emit-minify")]
use crate::{
  clear_last_emit_backend_for_tests, force_hir_emit_failure_for_tests, last_emit_backend_for_tests,
  EmitBackend,
};
use crate::{minify, minify_with_options, Dialect, FileId, MinifyOptions, Severity, TopLevelMode};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal, ObjMemberType};
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
    "console.log(x);(()=>{let console=1;return console;})();",
  );
  assert_eq!(result, "console.log(x);(()=>{let a=1;return a;})();");
}

#[test]
fn test_module_export_bindings_preserved() {
  let result = minified(TopLevelMode::Module, "export const x=1; const y=2;");
  assert_eq!(result, "export const x=1;");
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
fn folds_numeric_expressions() {
  let result = minified(TopLevelMode::Global, "console.log(1+2*3);");
  assert_eq!(result, "console.log(7);");
}

#[test]
fn folds_string_concatenation() {
  let result = minified(TopLevelMode::Global, r#"console.log("a"+"b");"#);
  assert_eq!(result, r#"console.log("ab");"#);
}

#[test]
fn folds_boolean_negation() {
  let result = minified(TopLevelMode::Global, "console.log(!true);");
  assert_eq!(result, "console.log(false);");
}

#[test]
fn rewrites_if_to_logical_and() {
  let result = minified(TopLevelMode::Global, "if(foo)bar();");
  assert_eq!(result, "foo&&bar();");
}

#[test]
fn rewrites_if_to_ternary_expression() {
  let result = minified(TopLevelMode::Global, "if(foo)a();else b();");
  assert_eq!(result, "foo?a():b();");
}

#[test]
fn removes_unreachable_if_branches() {
  let result = minified(TopLevelMode::Global, "if(false)foo();bar();");
  assert_eq!(result, "bar();");
}

#[test]
fn removes_unreachable_if_branches_in_arrow_expr_bodies() {
  let result = minified(
    TopLevelMode::Global,
    "const f=()=>{if(false){sideEffect()}return 1;};",
  );
  assert_eq!(result, "const f=()=>{return 1;};");
}

#[test]
fn dce_removes_unused_locals_in_arrow_expr_bodies() {
  let result = minified(TopLevelMode::Global, "const f=()=>{let x=1;return 2;};");
  assert_eq!(result, "const f=()=>{return 2;};");
}

#[test]
fn direct_eval_disables_dce_in_nested_arrow_expr_bodies() {
  let result = minified(
    TopLevelMode::Global,
    r#"const f=()=>{if(false){sideEffect()}let x=1;eval("x");return 2;};"#,
  );
  assert_eq!(result, r#"const f=()=>{let x=1;eval("x");return 2;};"#);
}

#[test]
fn with_statement_disables_dce_in_nested_arrow_expr_bodies() {
  let result = minified(
    TopLevelMode::Global,
    "call(()=>{with({}){let x=1;}return 2;});",
  );
  assert_eq!(result, "call(()=>{with({}){let x=1;}return 2;});");
}

#[test]
fn direct_eval_disables_dce_in_ancestor_scopes() {
  let result = minified(TopLevelMode::Module, r#"let x=1;(()=>{eval("x");})();"#);
  assert_eq!(result, r#"let x=1;(()=>{eval("x");})();"#);
}

#[test]
fn semantic_rewrite_does_not_break_dce_symbol_tracking() {
  let result = minified(
    TopLevelMode::Module,
    "let x=1;if(x===null||x===undefined)g();",
  );
  assert_eq!(result, "let a=1;a==null&&g();");
}

#[test]
fn optimizes_object_literal_methods_in_expression_position() {
  let result = minified(
    TopLevelMode::Global,
    "const o={m(){if(false){sideEffect()}return 1;}};",
  );
  assert_eq!(result, "const o={m(){return 1;}};");
}

#[test]
fn optimizes_class_expression_methods_in_expression_position() {
  let result = minified(
    TopLevelMode::Global,
    "const C=class{m(){if(false){sideEffect()}return 1;}};",
  );
  assert_eq!(result, "const C=class{m(){return 1;}};");
}

#[test]
fn removes_unused_var_decls_with_pure_initializers() {
  let result = minified(TopLevelMode::Module, "let x=1;console.log(2);");
  assert_eq!(result, "console.log(2);");
}

#[test]
fn rewrites_return_undefined() {
  let result = minified(TopLevelMode::Global, "function f(){return undefined;}");
  assert_eq!(result, "function f(){return;}");
}

#[test]
fn does_not_rewrite_shadowed_undefined() {
  let result = minified(
    TopLevelMode::Global,
    "function f(undefined){return undefined;}",
  );
  assert_eq!(result, "function f(a){return a;}");
}

#[test]
fn rewrites_nullish_or_to_loose_equality() {
  let result = minified(
    TopLevelMode::Global,
    "function f(x){if(x===null||x===undefined)g();}",
  );
  assert_eq!(result, "function f(a){a==null&&g();}");
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
  assert_eq!(result, "function f(a){a(\"x\");}");
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
fn lowers_const_enums_to_runtime_js() {
  let src = r#"const enum E { A = 1, B = A } const x = E.B;"#;
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

  assert_eq!(parsed.stx.body.len(), 3);
  let enum_var = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum var decl, got {other:?}"),
  };
  assert_eq!(enum_var.stx.mode, VarDeclMode::Var);
  let name = enum_var
    .stx
    .declarators
    .first()
    .expect("enum declarator")
    .pattern
    .stx
    .pat
    .stx
    .as_ref();
  match name {
    parse_js::ast::expr::pat::Pat::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected identifier pattern, got {other:?}"),
  };
  assert!(matches!(parsed.stx.body[1].stx.as_ref(), Stmt::Expr(_)));
  let x_decl = match parsed.stx.body[2].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected x var decl, got {other:?}"),
  };
  let initializer = x_decl
    .stx
    .declarators
    .first()
    .and_then(|decl| decl.initializer.as_ref())
    .expect("initializer should exist");
  match initializer.stx.as_ref() {
    Expr::Member(member) => {
      assert_eq!(member.stx.right, "B");
      match member.stx.left.stx.as_ref() {
        Expr::Id(id) => assert_eq!(id.stx.name, "E"),
        other => panic!("expected enum identifier, got {other:?}"),
      }
    }
    other => panic!("expected enum member reference, got {other:?}"),
  }
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
fn lowers_dotted_runtime_namespaces_to_parseable_js() {
  let src = r#"export namespace A.B { export const x = 1; }"#;
  let (code, parsed) = minified_program(TopLevelMode::Module, Dialect::Ts, Dialect::Js, src);
  assert_eq!(parsed.stx.body.len(), 2);
  let decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected namespace var decl, got {other:?}"),
  };
  assert!(decl.stx.export);
  assert!(
    code.contains("\"B\""),
    "dotted namespace lowering should initialize A[\"B\"]"
  );
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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
fn rewrites_enum_member_references_in_nested_scopes() {
  let src = r#"enum E { A = 1, B = (() => A)(), C = (function(){ return A; })() }"#;
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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

  fn get_value_expr<'a>(stmt: &'a Node<Stmt>) -> &'a Node<Expr> {
    let expr_stmt = match stmt.stx.as_ref() {
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
    &name_assign.stx.right
  }

  let b_stmt = body.get(1).expect("B member statement");
  let b_value = get_value_expr(b_stmt);
  let b_call = match b_value.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let b_arrow = match b_call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let b_arrow_body = match b_arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  assert!(
    matches!(b_arrow_body.stx.as_ref(), Expr::ComputedMember(_)),
    "expected A in arrow initializer to rewrite to E[\"A\"]"
  );

  let c_stmt = body.get(2).expect("C member statement");
  let c_value = get_value_expr(c_stmt);
  let c_call = match c_value.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for C initializer, got {other:?}"),
  };
  let c_func = match c_call.stx.callee.stx.as_ref() {
    Expr::Func(func) => func,
    other => panic!("expected function expression callee, got {other:?}"),
  };
  let c_body = match c_func.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected function body block, got {other:?}"),
  };
  let ret = c_body.iter().find_map(|stmt| match stmt.stx.as_ref() {
    Stmt::Return(ret) => ret.stx.value.as_ref(),
    _ => None,
  });
  let ret = ret.expect("expected return statement in function initializer");
  assert!(
    matches!(ret.stx.as_ref(), Expr::ComputedMember(_)),
    "expected A in function initializer to rewrite to E[\"A\"]"
  );
}

#[test]
fn does_not_rewrite_shadowed_enum_member_references() {
  let src = r#"enum E { A = 1, B = ((A) => A)(2) }"#;
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  assert!(
    matches!(arrow_body.stx.as_ref(), Expr::Id(_)),
    "shadowed A in arrow initializer should remain an identifier"
  );
}

#[test]
fn rewrites_enum_member_references_using_alias_when_enum_name_shadowed() {
  let src = r#"enum E { A = 1, B = ((E) => A)(0) }"#;
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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

  assert_eq!(body.len(), 3);
  let alias_stmt = body.first().expect("enum alias var decl statement");
  let alias_decl = match alias_stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl,
    other => panic!("expected enum alias var decl, got {other:?}"),
  };
  assert_eq!(alias_decl.stx.mode, VarDeclMode::Var);
  let alias_declarator = alias_decl
    .stx
    .declarators
    .first()
    .expect("alias declarator");
  match alias_declarator.pattern.stx.pat.stx.as_ref() {
    parse_js::ast::expr::pat::Pat::Id(id) => assert_eq!(id.stx.name, "__minify_ts_enum_E"),
    other => panic!("expected identifier pattern, got {other:?}"),
  };
  let alias_init = alias_declarator
    .initializer
    .as_ref()
    .expect("alias initializer");
  match alias_init.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected initializer identifier, got {other:?}"),
  };

  let b_stmt = body.get(2).expect("B member statement");
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
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let computed = match arrow_body.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member access, got {other:?}"),
  };
  match computed.stx.object.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "__minify_ts_enum_E"),
    other => panic!("expected enum alias identifier, got {other:?}"),
  };
  match computed.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "A"),
    other => panic!("expected string literal member, got {other:?}"),
  };
}

#[test]
fn rewrites_enum_member_references_in_object_shorthand() {
  let src = r#"enum E { A = 1, B = (() => ({ A }))() }"#;
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let obj = match arrow_body.stx.as_ref() {
    Expr::LitObj(obj) => obj,
    other => panic!("expected object literal, got {other:?}"),
  };
  let member = obj.stx.members.first().expect("object member");
  let (key, value) = match &member.stx.typ {
    ObjMemberType::Valued { key, val } => (key, val),
    other => panic!("expected valued member, got {other:?}"),
  };
  match key {
    ClassOrObjKey::Direct(name) => assert_eq!(name.stx.key, "A"),
    other => panic!("expected direct key, got {other:?}"),
  };
  let value = match value {
    ClassOrObjVal::Prop(Some(expr)) => expr,
    other => panic!("expected property value expression, got {other:?}"),
  };
  let computed = match value.stx.as_ref() {
    Expr::ComputedMember(member) => member,
    other => panic!("expected computed member access, got {other:?}"),
  };
  match computed.stx.object.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "E"),
    other => panic!("expected enum identifier, got {other:?}"),
  };
  match computed.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "A"),
    other => panic!("expected string literal member, got {other:?}"),
  };
}

#[test]
fn does_not_rewrite_shadowed_enum_member_references_in_object_shorthand() {
  let src = r#"enum E { A = 1, B = ((A) => ({ A }))(2) }"#;
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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
  let value_expr = &name_assign.stx.right;
  let call = match value_expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected call expression for B initializer, got {other:?}"),
  };
  let arrow = match call.stx.callee.stx.as_ref() {
    Expr::ArrowFunc(arrow) => arrow,
    other => panic!("expected arrow function callee, got {other:?}"),
  };
  let arrow_body = match arrow.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Expression(expr)) => expr,
    other => panic!("expected arrow expression body, got {other:?}"),
  };
  let obj = match arrow_body.stx.as_ref() {
    Expr::LitObj(obj) => obj,
    other => panic!("expected object literal, got {other:?}"),
  };
  let member = obj.stx.members.first().expect("object member");
  match &member.stx.typ {
    ObjMemberType::Shorthand { id } => assert_eq!(id.stx.name, "A"),
    other => panic!("expected shorthand member, got {other:?}"),
  };
}

#[test]
fn lowers_parameter_properties_in_constructors() {
  let src = r#"class C { constructor(public x: number, readonly y: string) {} }"#;
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

  let class_decl = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  let ctor = class_decl
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };

  fn assert_this_property_assignment(stmt: &Node<Stmt>, name: &str) {
    let expr_stmt = match stmt.stx.as_ref() {
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
    assert!(
      matches!(left.stx.object.stx.as_ref(), Expr::This(_)),
      "expected this[...] on assignment LHS"
    );
    match left.stx.member.stx.as_ref() {
      Expr::LitStr(key) => assert_eq!(key.stx.value, name),
      other => panic!("expected string member, got {other:?}"),
    };
    match assign.stx.right.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, name),
      other => panic!("expected identifier RHS, got {other:?}"),
    };
  }

  assert_eq!(body.len(), 2);
  assert_this_property_assignment(&body[0], "x");
  assert_this_property_assignment(&body[1], "y");
}

#[test]
fn lowers_parameter_properties_after_super_in_derived_constructors() {
  let src = r#"
    class Base { constructor(x: number) {} }
    class Derived extends Base {
      constructor(public x: number) {
        console.log(x);
        super(x);
      }
    }
  "#;
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

  assert!(parsed.stx.body.len() >= 2);
  let derived = match parsed.stx.body.get(1).map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected derived class decl, got {other:?}"),
  };
  let ctor = derived
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };

  assert_eq!(body.len(), 3);
  let super_stmt = body.get(1).expect("super call statement");
  let expr_stmt = match super_stmt.stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let call = match expr_stmt.stx.expr.stx.as_ref() {
    Expr::Call(call) => call,
    other => panic!("expected super call, got {other:?}"),
  };
  assert!(
    matches!(call.stx.callee.stx.as_ref(), Expr::Super(_)),
    "expected super(...) call"
  );

  let assign_stmt = body.get(2).expect("parameter property assignment");
  let expr_stmt = match assign_stmt.stx.as_ref() {
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
  assert!(
    matches!(left.stx.object.stx.as_ref(), Expr::This(_)),
    "expected this[...] on assignment LHS"
  );
  match left.stx.member.stx.as_ref() {
    Expr::LitStr(key) => assert_eq!(key.stx.value, "x"),
    other => panic!("expected string member, got {other:?}"),
  };
  match assign.stx.right.stx.as_ref() {
    Expr::Id(id) => assert_eq!(id.stx.name, "x"),
    other => panic!("expected identifier RHS, got {other:?}"),
  };
}

#[test]
fn constructor_parameter_properties_preserve_directive_prologue() {
  let src = r#"class C { constructor(public x: number) { "use strict"; } }"#;
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

  let class_decl = match parsed.stx.body.first().map(|stmt| stmt.stx.as_ref()) {
    Some(Stmt::ClassDecl(decl)) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  let ctor = class_decl
    .stx
    .members
    .iter()
    .find(|member| match &member.stx.key {
      ClassOrObjKey::Direct(key) => key.stx.key == "constructor",
      _ => false,
    })
    .expect("constructor member");
  let method = match &ctor.stx.val {
    ClassOrObjVal::Method(method) => method,
    other => panic!("expected constructor method, got {other:?}"),
  };
  let body = match method.stx.func.stx.body.as_ref() {
    Some(parse_js::ast::func::FuncBody::Block(stmts)) => stmts,
    other => panic!("expected constructor body block, got {other:?}"),
  };
  assert_eq!(body.len(), 2);

  let directive = match body[0].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  match directive.stx.expr.stx.as_ref() {
    Expr::LitStr(lit) => assert_eq!(lit.stx.value, "use strict"),
    other => panic!("expected string literal directive, got {other:?}"),
  };

  let assign = match body[1].stx.as_ref() {
    Stmt::Expr(expr) => expr,
    other => panic!("expected expression statement, got {other:?}"),
  };
  let assign = match assign.stx.expr.stx.as_ref() {
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Assignment => bin,
    other => panic!("expected assignment expression, got {other:?}"),
  };
  match assign.stx.left.stx.as_ref() {
    Expr::ComputedMember(member) => {
      assert!(matches!(member.stx.object.stx.as_ref(), Expr::This(_)));
      assert!(matches!(member.stx.member.stx.as_ref(), Expr::LitStr(_)));
    }
    other => panic!("expected computed member assignment, got {other:?}"),
  };
}

#[test]
fn drops_method_signatures_in_abstract_classes() {
  let src = r#"
    abstract class C {
      foo(): void;
      bar() {}
    }
  "#;
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

  assert_eq!(parsed.stx.body.len(), 1);
  let class_decl = match parsed.stx.body[0].stx.as_ref() {
    Stmt::ClassDecl(decl) => decl,
    other => panic!("expected class decl, got {other:?}"),
  };
  assert!(!class_decl.stx.abstract_);
  assert_eq!(class_decl.stx.members.len(), 1);
  let member = class_decl.stx.members.first().expect("class member");
  match &member.stx.key {
    ClassOrObjKey::Direct(key) => assert_eq!(key.stx.key, "bar"),
    other => panic!("expected direct class member key, got {other:?}"),
  };
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
    Expr::Binary(bin) if bin.stx.operator == OperatorName::Comma => {
      match bin.stx.right.stx.as_ref() {
        Expr::Call(call) => call,
        other => panic!("expected comma call rhs, got {other:?}"),
      }
    }
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
