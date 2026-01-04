use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode};
use parse_js::ast::class_or_object::{ClassOrObjKey, ClassOrObjVal};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::import_export::ExportNames;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, ParseOptions, SourceType};

fn minify_ts_module(src: &str) -> (String, Node<TopLevel>) {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(TopLevelMode::Module).with_dialect(Dialect::Ts),
    src,
    &mut out,
  )
  .expect("minify should succeed");
  let code = String::from_utf8(out).expect("minifier output must be UTF-8");
  let parsed = parse_with_options(
    &code,
    ParseOptions {
      dialect: Dialect::Js,
      source_type: SourceType::Module,
    },
  )
  .expect("output should parse as JavaScript");
  (code, parsed)
}

fn has_exported_var_decl(program: &Node<TopLevel>, name: &str) -> bool {
  program.stx.body.iter().any(|stmt| {
    match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) if decl.stx.export => decl.stx.declarators.iter().any(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == name)
    }),
    _ => false,
  }
  })
}

fn has_exported_name(program: &Node<TopLevel>, exported: &str) -> bool {
  program.stx.body.iter().any(|stmt| {
    match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) if decl.stx.export => decl.stx.declarators.iter().any(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == exported)
    }),
    Stmt::FunctionDecl(func) if func.stx.export => func
      .stx
      .name
      .as_ref()
      .is_some_and(|name| name.stx.name == exported),
    Stmt::ClassDecl(class_decl) if class_decl.stx.export => class_decl
      .stx
      .name
      .as_ref()
      .is_some_and(|name| name.stx.name == exported),
    Stmt::ExportList(export_stmt) if !export_stmt.stx.type_only => match &export_stmt.stx.names {
      ExportNames::Specific(entries) => entries.iter().any(|entry| {
        !entry.stx.type_only && entry.stx.alias.stx.name == exported
      }),
      ExportNames::All(Some(alias)) => alias.stx.name == exported,
      ExportNames::All(None) => false,
    },
    _ => false,
  }
  })
}

fn find_iife_body_by_outer_name<'a>(
  program: &'a Node<TopLevel>,
  outer_name: &str,
) -> Option<&'a Vec<Node<Stmt>>> {
  for stmt in &program.stx.body {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      continue;
    };
    let Expr::Binary(comma) = expr_stmt.stx.expr.stx.as_ref() else {
      continue;
    };
    if comma.stx.operator != OperatorName::Comma {
      continue;
    }
    let Expr::Call(call) = comma.stx.right.stx.as_ref() else {
      continue;
    };
    if call.stx.arguments.len() != 1 {
      continue;
    }
    let arg = &call.stx.arguments[0].stx.value;
    let Expr::Binary(or) = arg.stx.as_ref() else {
      continue;
    };
    if or.stx.operator != OperatorName::LogicalOr {
      continue;
    }
    match or.stx.left.stx.as_ref() {
      Expr::Id(id) if id.stx.name == outer_name => {}
      _ => continue,
    }
    let Expr::Func(func_expr) = call.stx.callee.stx.as_ref() else {
      continue;
    };
    let func = &func_expr.stx.func.stx;
    let Some(parse_js::ast::func::FuncBody::Block(body)) = func.body.as_ref() else {
      continue;
    };
    return Some(body);
  }
  None
}

#[test]
fn lowers_enums_with_runtime_semantics_to_js() {
  let src = r#"
    export enum Num { A, B = 5, C }
    export enum Str { A = "a", B = `b` }
    export enum Mixed { A = 0, B = "b", C = 1, D }
    console.log(Num.C, Str.B, Mixed.D);
  "#;
  let (code, parsed) = minify_ts_module(src);

  assert!(
    !code.contains("enum"),
    "output should not contain TypeScript enum syntax: {code}"
  );
  assert!(has_exported_var_decl(&parsed, "Num"));
  assert!(has_exported_var_decl(&parsed, "Str"));
  assert!(has_exported_var_decl(&parsed, "Mixed"));

  // String enums should not emit reverse mappings (i.e. no `E[E["A"] = ...] = "A"`).
  let body = find_iife_body_by_outer_name(&parsed, "Str").expect("expected Str enum IIFE");
  assert_eq!(body.len(), 2, "expected two Str enum member statements");
  for stmt in body {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      panic!("expected expression statement in Str enum body, got {stmt:?}");
    };
    let Expr::Binary(assign) = expr_stmt.stx.expr.stx.as_ref() else {
      panic!("expected assignment expression in Str enum body, got {stmt:?}");
    };
    assert_eq!(assign.stx.operator, OperatorName::Assignment);
    let Expr::ComputedMember(member) = assign.stx.left.stx.as_ref() else {
      panic!("expected computed member assignment in Str enum body, got {stmt:?}");
    };
    assert!(
      matches!(member.stx.member.stx.as_ref(), Expr::LitStr(_)),
      "string enums should only assign E[\"name\"], got {member:?}"
    );
  }
}

#[test]
fn lowers_namespaces_with_runtime_semantics_to_js() {
  let src = r#"
    export namespace NS {
      export const x: number = 1;
      export function get() { return x; }
      export namespace Inner { export const y = x + 1; }
    }
    console.log(NS.Inner.y, NS.get());
  "#;
  let (code, parsed) = minify_ts_module(src);

  assert!(
    !code.contains("namespace"),
    "output should not contain TypeScript namespace syntax: {code}"
  );
  assert!(has_exported_var_decl(&parsed, "NS"));
  assert!(
    code.contains("\"Inner\""),
    "nested namespace lowering should reference the Inner object: {code}"
  );

  let body = find_iife_body_by_outer_name(&parsed, "NS").expect("expected NS namespace IIFE");
  assert!(
    body.iter().any(|stmt| {
      matches!(stmt.stx.as_ref(), Stmt::VarDecl(decl) if decl.stx.mode == VarDeclMode::Var)
    }),
    "expected namespace body to contain at least one var declaration"
  );
}

#[test]
fn lowers_import_equals_and_export_assignment_to_commonjs() {
  let src = r#"
    import foo = require("bar");
    export = foo;
  "#;
  let (code, _parsed) = minify_ts_module(src);
  assert!(
    code.contains("require(\"bar\")"),
    "expected require call from import= lowering: {code}"
  );
  assert!(
    code.contains("module.exports"),
    "expected module.exports assignment from export= lowering: {code}"
  );
  assert!(
    !code.contains("export ="),
    "output should not contain TypeScript export assignment syntax: {code}"
  );
}

#[test]
fn lowers_constructor_parameter_properties_to_this_assignments() {
  let src = r#"
    class C { constructor(public x: number, readonly y: string) {} }
    export const value = new C(1, "a").x + new C(2, "b").y;
  "#;
  let (_code, parsed) = minify_ts_module(src);

  let class_decl = parsed
    .stx
    .body
    .iter()
    .find_map(|stmt| match stmt.stx.as_ref() {
      Stmt::ClassDecl(decl) => Some(decl),
      _ => None,
    })
    .expect("expected class declaration");

  let ctor = class_decl
    .stx
    .members
    .iter()
    .find(|member| matches!(&member.stx.key, ClassOrObjKey::Direct(key) if key.stx.key == "constructor"))
    .expect("expected constructor member");
  let ClassOrObjVal::Method(method) = &ctor.stx.val else {
    panic!("expected constructor method, got {ctor:?}");
  };
  let Some(parse_js::ast::func::FuncBody::Block(stmts)) = method.stx.func.stx.body.as_ref() else {
    panic!("expected constructor body block");
  };

  assert!(
    stmts.iter().any(|stmt| match stmt.stx.as_ref() {
      Stmt::Expr(expr_stmt) => matches!(expr_stmt.stx.expr.stx.as_ref(), Expr::Binary(_)),
      _ => false,
    }),
    "expected constructor to contain this-property assignments"
  );

  let mut assigned_props = stmts
    .iter()
    .filter_map(|stmt| {
      let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
        return None;
      };
      let Expr::Binary(assign) = expr_stmt.stx.expr.stx.as_ref() else {
        return None;
      };
      if assign.stx.operator != OperatorName::Assignment {
        return None;
      }
      let Expr::ComputedMember(member) = assign.stx.left.stx.as_ref() else {
        return None;
      };
      if !matches!(member.stx.object.stx.as_ref(), Expr::This(_)) {
        return None;
      }
      let Expr::LitStr(key) = member.stx.member.stx.as_ref() else {
        return None;
      };
      Some(key.stx.value.as_str())
    })
    .collect::<Vec<_>>();
  assigned_props.sort_unstable();
  assert_eq!(assigned_props, vec!["x", "y"]);
}

#[test]
fn derived_constructor_parameter_properties_follow_super_call() {
  let src = r#"
    class Base { constructor(public x: number) {} }
    class Derived extends Base { constructor(public y: number) { super(y); } }
    export const value = new Derived(1).y;
  "#;
  let (_code, parsed) = minify_ts_module(src);

  let derived = parsed
    .stx
    .body
    .iter()
    .filter_map(|stmt| match stmt.stx.as_ref() {
      Stmt::ClassDecl(decl) => Some(decl),
      _ => None,
    })
    .nth(1)
    .expect("expected derived class declaration");

  let ctor = derived
    .stx
    .members
    .iter()
    .find(|member| matches!(&member.stx.key, ClassOrObjKey::Direct(key) if key.stx.key == "constructor"))
    .expect("expected derived constructor member");
  let ClassOrObjVal::Method(method) = &ctor.stx.val else {
    panic!("expected constructor method, got {ctor:?}");
  };
  let Some(parse_js::ast::func::FuncBody::Block(stmts)) = method.stx.func.stx.body.as_ref() else {
    panic!("expected constructor body block");
  };
  assert!(
    stmts.len() >= 2,
    "expected derived constructor to contain super call + param property assignment"
  );

  let is_super_call_stmt = |stmt: &Node<Stmt>| {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      return false;
    };
    matches!(
      expr_stmt.stx.expr.stx.as_ref(),
      Expr::Call(call) if matches!(call.stx.callee.stx.as_ref(), Expr::Super(_))
    )
  };
  assert!(
    is_super_call_stmt(&stmts[0]),
    "expected first statement to be super(...)"
  );

  let is_this_assignment_stmt = |stmt: &Node<Stmt>| {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      return false;
    };
    let Expr::Binary(assign) = expr_stmt.stx.expr.stx.as_ref() else {
      return false;
    };
    if assign.stx.operator != OperatorName::Assignment {
      return false;
    }
    let Expr::ComputedMember(member) = assign.stx.left.stx.as_ref() else {
      return false;
    };
    matches!(member.stx.object.stx.as_ref(), Expr::This(_))
  };
  assert!(
    is_this_assignment_stmt(&stmts[1]),
    "expected param property assignment immediately after super(...)"
  );
}

#[test]
fn lowers_namespaces_merged_with_classes_inside_runtime_namespaces() {
  // Disable renaming so we can assert on the exact merged binding name.
  let src = r#"
    eval("x");
    export namespace N {
      class C {}
      export namespace C { export const x = 1; }
    }
    console.log(N.C.x);
  "#;
  let (code, parsed) = minify_ts_module(src);

  let body = find_iife_body_by_outer_name(&parsed, "N").expect("expected N namespace IIFE");
  let class_name = body
    .iter()
    .find_map(|stmt| match stmt.stx.as_ref() {
      Stmt::ClassDecl(decl) => decl.stx.name.as_ref().map(|name| name.stx.name.clone()),
      _ => None,
    })
    .expect("expected class declaration inside the N namespace body");
  let mut saw_var_for_class = false;
  let mut saw_parent_assignment = false;
  for stmt in body {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => {
        for declarator in &decl.stx.declarators {
          if matches!(
            declarator.pattern.stx.pat.stx.as_ref(),
            Pat::Id(id) if id.stx.name == class_name
          ) {
            saw_var_for_class = true;
          }
        }
      }
      Stmt::Expr(expr_stmt) => {
        let Expr::Binary(bin) = expr_stmt.stx.expr.stx.as_ref() else {
          continue;
        };
        if bin.stx.operator != OperatorName::Assignment {
          continue;
        }
        let Expr::ComputedMember(member) = bin.stx.left.stx.as_ref() else {
          continue;
        };
        if !matches!(member.stx.object.stx.as_ref(), Expr::Id(_)) {
          continue;
        }
        if !matches!(member.stx.member.stx.as_ref(), Expr::LitStr(key) if key.stx.value == "C") {
          continue;
        }
        if !matches!(bin.stx.right.stx.as_ref(), Expr::Id(id) if id.stx.name == class_name) {
          continue;
        }
        saw_parent_assignment = true;
      }
      _ => {}
    }
  }

  assert!(
    !saw_var_for_class,
    "namespace merging should not introduce a `var` binding that collides with the merged class. output: {code}"
  );
  assert!(
    saw_parent_assignment,
    "expected an assignment of the merged class onto the parent namespace object. output: {code}"
  );
}

#[test]
fn lowers_export_import_equals_inside_runtime_namespaces() {
  let src = r#"
    export namespace N {
      export import Foo = require("foo");
      export import Bar = Other.Nested;
    }
    console.log(N.Foo, N.Bar);
  "#;
  let (code, parsed) = minify_ts_module(src);

  assert!(
    !code.contains("import Foo"),
    "expected TS import= syntax to be removed: {code}"
  );

  let body = find_iife_body_by_outer_name(&parsed, "N").expect("expected N namespace IIFE");
  let mut decl_inits = std::collections::HashMap::<String, &Node<Expr>>::new();
  let mut exports = std::collections::HashMap::<String, String>::new();

  for stmt in body {
    match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => {
        for declarator in &decl.stx.declarators {
          let Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() else {
            continue;
          };
          let Some(init) = declarator.initializer.as_ref() else {
            continue;
          };
          decl_inits.insert(id.stx.name.clone(), init);
        }
      }
      Stmt::Expr(expr_stmt) => {
        let Expr::Binary(assign) = expr_stmt.stx.expr.stx.as_ref() else {
          continue;
        };
        if assign.stx.operator != OperatorName::Assignment {
          continue;
        }
        let Expr::ComputedMember(member) = assign.stx.left.stx.as_ref() else {
          continue;
        };
        let Expr::LitStr(key) = member.stx.member.stx.as_ref() else {
          continue;
        };
        let Expr::Id(value) = assign.stx.right.stx.as_ref() else {
          continue;
        };
        exports.insert(key.stx.value.clone(), value.stx.name.clone());
      }
      _ => {}
    }
  }

  let foo_binding = exports
    .get("Foo")
    .expect("expected N[\"Foo\"] assignment")
    .clone();
  let foo_init = decl_inits
    .get(&foo_binding)
    .expect("expected a binding initializer for Foo alias");
  match foo_init.stx.as_ref() {
    Expr::Call(call) => match call.stx.callee.stx.as_ref() {
      Expr::Id(id) => assert_eq!(id.stx.name, "require"),
      other => panic!("expected require call callee, got {other:?}"),
    },
    other => panic!("expected require call initializer for Foo, got {other:?}"),
  }

  let bar_binding = exports
    .get("Bar")
    .expect("expected N[\"Bar\"] assignment")
    .clone();
  let bar_init = decl_inits
    .get(&bar_binding)
    .expect("expected a binding initializer for Bar alias");
  assert!(
    matches!(
      bar_init.stx.as_ref(),
      Expr::Member(member) if member.stx.right == "Nested"
    ),
    "expected Bar initializer to reference `.Nested`, got {bar_init:?}"
  );
}

#[test]
fn exported_runtime_enums_preserve_self_export_when_exported_under_alias() {
  let src = r#"
    export enum E { A }
    export { E as E2 };
  "#;
  let (_code, parsed) = minify_ts_module(src);

  assert!(
    has_exported_name(&parsed, "E"),
    "expected enum lowering to export `E`"
  );
  assert!(
    has_exported_name(&parsed, "E2"),
    "expected the alias export `E2` to be preserved"
  );
}

#[test]
fn exported_runtime_namespaces_merged_with_functions_preserve_self_export_when_exported_under_alias(
) {
  let src = r#"
    function N() {}
    export namespace N { export const x = 1; }
    export { N as N2 };
  "#;
  let (_code, parsed) = minify_ts_module(src);

  assert!(
    has_exported_name(&parsed, "N"),
    "expected namespace merging to export `N`"
  );
  assert!(
    has_exported_name(&parsed, "N2"),
    "expected the alias export `N2` to be preserved"
  );
}

#[test]
fn lowers_computed_numeric_enum_members_and_preserves_auto_increments() {
  // Disable renaming so we can assert on the exact enum/func names.
  let src = r#"
    eval("x");
    export enum E {
      A = side(),
      B,
      C = side2(),
      D,
    }
    function side() { return 10; }
    function side2() { return 20; }
  "#;
  let (_code, parsed) = minify_ts_module(src);

  let body = find_iife_body_by_outer_name(&parsed, "E").expect("expected E enum IIFE");
  assert_eq!(body.len(), 4, "expected one statement per enum member");

  fn enum_member_value_expr<'a>(stmt: &'a Node<Stmt>) -> &'a Node<Expr> {
    let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
      panic!("expected expression statement, got {stmt:?}");
    };
    let Expr::Binary(outer_assign) = expr_stmt.stx.expr.stx.as_ref() else {
      panic!("expected assignment expression, got {stmt:?}");
    };
    assert_eq!(outer_assign.stx.operator, OperatorName::Assignment);
    let Expr::ComputedMember(member) = outer_assign.stx.left.stx.as_ref() else {
      panic!("expected computed member assignment, got {stmt:?}");
    };
    let Expr::Binary(name_assign) = member.stx.member.stx.as_ref() else {
      panic!("expected inner assignment in reverse mapping, got {stmt:?}");
    };
    assert_eq!(name_assign.stx.operator, OperatorName::Assignment);
    &name_assign.stx.right
  }

  // Computed enum member initializers should be preserved.
  assert!(
    matches!(enum_member_value_expr(&body[0]).stx.as_ref(), Expr::Call(_)),
    "expected computed initializer for A to remain a call expression"
  );
  assert!(
    matches!(enum_member_value_expr(&body[2]).stx.as_ref(), Expr::Call(_)),
    "expected computed initializer for C to remain a call expression"
  );

  // Auto-incremented members should be based on the previous member at runtime.
  let b_value = enum_member_value_expr(&body[1]);
  let Expr::Binary(b_add) = b_value.stx.as_ref() else {
    panic!("expected B initializer to be an addition expression, got {b_value:?}");
  };
  assert_eq!(b_add.stx.operator, OperatorName::Addition);
  assert!(
    matches!(
      b_add.stx.left.stx.as_ref(),
      Expr::ComputedMember(member)
        if matches!(member.stx.object.stx.as_ref(), Expr::Id(_))
          && matches!(member.stx.member.stx.as_ref(), Expr::LitStr(key) if key.stx.value == "A")
    ),
    "expected B to be initialized from E[\"A\"] + 1, got {b_value:?}"
  );
  assert!(
    matches!(b_add.stx.right.stx.as_ref(), Expr::LitNum(num) if num.stx.value.0 == 1.0),
    "expected B initializer to add 1, got {b_value:?}"
  );

  let d_value = enum_member_value_expr(&body[3]);
  let Expr::Binary(d_add) = d_value.stx.as_ref() else {
    panic!("expected D initializer to be an addition expression, got {d_value:?}");
  };
  assert_eq!(d_add.stx.operator, OperatorName::Addition);
  assert!(
    matches!(
      d_add.stx.left.stx.as_ref(),
      Expr::ComputedMember(member)
        if matches!(member.stx.object.stx.as_ref(), Expr::Id(_))
          && matches!(member.stx.member.stx.as_ref(), Expr::LitStr(key) if key.stx.value == "C")
    ),
    "expected D to be initialized from E[\"C\"] + 1, got {d_value:?}"
  );
  assert!(
    matches!(d_add.stx.right.stx.as_ref(), Expr::LitNum(num) if num.stx.value.0 == 1.0),
    "expected D initializer to add 1, got {d_value:?}"
  );
}

#[test]
fn lowers_dotted_namespaces_with_reserved_keyword_segments_to_parseable_js() {
  // Disable renaming to ensure the TS erasure itself produces valid JS identifiers even when the
  // dotted namespace path contains reserved words.
  let src = r#"
    export namespace A.class {
      eval("x");
      export const x = 1;
    }
    console.log(A["class"].x);
  "#;
  let (code, _parsed) = minify_ts_module(src);

  assert!(
    code.contains("\"class\""),
    "expected reserved namespace segment to be accessed via a string key: {code}"
  );
  assert!(
    !code.contains("var class"),
    "lowering should not introduce a `var class` binding (invalid JS): {code}"
  );
  assert!(
    !code.contains("function(class"),
    "lowering should not introduce a `function(class)` parameter (invalid JS): {code}"
  );
}

#[test]
fn lowers_dotted_namespaces_with_strict_mode_restricted_identifiers_to_parseable_js() {
  // `eval` / `arguments` are not keywords, but they are invalid binding identifiers in strict mode
  // (including ESM output).
  let src = r#"
    export namespace A.eval.arguments {
      eval("x");
      export const x = 1;
    }
    console.log(A["eval"]["arguments"].x);
  "#;
  let (code, _parsed) = minify_ts_module(src);

  assert!(
    code.contains("\"eval\"") && code.contains("\"arguments\""),
    "expected restricted namespace segments to be accessed via string keys: {code}"
  );
  assert!(
    !code.contains("var eval"),
    "lowering should not introduce a `var eval` binding (invalid strict mode JS): {code}"
  );
  assert!(
    !code.contains("function(eval"),
    "lowering should not introduce a `function(eval)` parameter (invalid strict mode JS): {code}"
  );
  assert!(
    !code.contains("var arguments"),
    "lowering should not introduce a `var arguments` binding (invalid strict mode JS): {code}"
  );
  assert!(
    !code.contains("function(arguments"),
    "lowering should not introduce a `function(arguments)` parameter (invalid strict mode JS): {code}"
  );
}

#[test]
fn avoids_synthetic_namespace_param_collisions_with_user_bindings() {
  // When a dotted namespace segment is not a valid binding identifier, TS erasure synthesizes an
  // internal IIFE parameter name. That name must not collide with user-declared bindings in the
  // namespace body, otherwise the output is invalid JS (and we can't rely on renaming when direct
  // eval is present).
  let src = r#"
    export namespace A.class {
      eval("x");
      const __minify_ts_namespace_class = 123;
      export const x = 1;
    }
    console.log(A["class"].x);
  "#;
  let (code, _parsed) = minify_ts_module(src);

  assert!(
    !code.contains("function(__minify_ts_namespace_class)"),
    "expected synthesized namespace param to avoid colliding with user binding: {code}"
  );
  assert!(
    code.contains("function(__minify_ts_namespace_class_"),
    "expected synthesized namespace param to be disambiguated with a suffix: {code}"
  );
}

#[test]
fn lowers_exported_enums_with_strict_reserved_names_inside_namespaces_to_parseable_js() {
  let src = r#"
    export namespace A {
      eval("x");
      export enum static { A = 1, B }
    }
    console.log(A["static"].A, A["static"].B);
  "#;
  let (code, _parsed) = minify_ts_module(src);

  assert!(
    code.contains("\"static\""),
    "expected enum name to be accessed via a string key on the namespace object: {code}"
  );
  assert!(
    !code.contains("var static"),
    "lowering should not introduce a `var static` binding (invalid strict mode JS): {code}"
  );
  assert!(
    !code.contains("function(static"),
    "lowering should not introduce a `function(static)` parameter (invalid strict mode JS): {code}"
  );
}

#[test]
fn lowers_top_level_namespaces_named_using_to_parseable_js() {
  let src = r#"
    export namespace using {
      export const x = 1;
    }
    console.log(using.x);
  "#;
  let (_code, _parsed) = minify_ts_module(src);
}
