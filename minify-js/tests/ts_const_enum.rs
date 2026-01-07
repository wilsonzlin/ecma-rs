use minify_js::{minify_with_options, ConstEnumMode, Dialect, MinifyOptions, TopLevelMode, TsEraseOptions};
use parse_js::ast::expr::Expr;
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::VarDeclMode;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::{parse_with_options, ParseOptions, SourceType};

fn minify_ts_module(src: &str, ts_erase_options: TsEraseOptions) -> (String, Node<TopLevel>) {
  let mut out = Vec::new();
  minify_with_options(
    MinifyOptions::new(TopLevelMode::Module)
      .with_dialect(Dialect::Ts)
      .with_ts_erase_options(ts_erase_options),
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

fn find_exported_const_initializer<'a>(program: &'a Node<TopLevel>, name: &str) -> Option<&'a Node<Expr>> {
  for stmt in &program.stx.body {
    let Stmt::VarDecl(decl) = stmt.stx.as_ref() else {
      continue;
    };
    if !decl.stx.export || decl.stx.mode != VarDeclMode::Const {
      continue;
    }
    for declarator in &decl.stx.declarators {
      let Pat::Id(id) = declarator.pattern.stx.pat.stx.as_ref() else {
        continue;
      };
      if id.stx.name != name {
        continue;
      }
      if let Some(init) = declarator.initializer.as_ref() {
        return Some(init);
      }
    }
  }
  None
}

fn program_declares_var(program: &Node<TopLevel>, name: &str) -> bool {
  program.stx.body.iter().any(|stmt| match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) => decl.stx.declarators.iter().any(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == name)
    }),
    _ => false,
  })
}

#[test]
fn inlines_numeric_const_enums_in_inline_mode() {
  let src = r#"
    const enum E { A, B = 5, C }
    export const x = E.C;
  "#;
  let (code, parsed) = minify_ts_module(
    src,
    TsEraseOptions {
      const_enum_mode: ConstEnumMode::Inline,
      ..TsEraseOptions::default()
    },
  );

  assert!(
    code.contains("const x=6"),
    "expected E.C to inline to 6, got: {code}"
  );
  assert!(
    !program_declares_var(&parsed, "E"),
    "inline mode should not emit a runtime enum binding: {code}"
  );

  let init = find_exported_const_initializer(&parsed, "x").expect("exported const x initializer");
  assert!(matches!(init.stx.as_ref(), Expr::LitNum(num) if num.stx.value.0 == 6.0));
}

#[test]
fn inlines_string_const_enums_in_inline_mode() {
  let src = r#"
    const enum E { A = "a" }
    export const x = E.A;
  "#;
  let (code, parsed) = minify_ts_module(
    src,
    TsEraseOptions {
      const_enum_mode: ConstEnumMode::Inline,
      ..TsEraseOptions::default()
    },
  );

  assert!(
    code.contains("const x=\"a\"") || code.contains("const x='a'"),
    "expected E.A to inline to \"a\", got: {code}"
  );
  assert!(
    !program_declares_var(&parsed, "E"),
    "inline mode should not emit a runtime enum binding: {code}"
  );

  let init = find_exported_const_initializer(&parsed, "x").expect("exported const x initializer");
  assert!(matches!(init.stx.as_ref(), Expr::LitStr(str) if str.stx.value == "a"));
}

#[test]
fn inlines_const_enum_member_refs_in_initializers() {
  let src = r#"
    const enum E { A = 1, B = A + 1 }
    export const x = E.B;
  "#;
  let (code, parsed) = minify_ts_module(
    src,
    TsEraseOptions {
      const_enum_mode: ConstEnumMode::Inline,
      ..TsEraseOptions::default()
    },
  );

  assert!(
    code.contains("const x=2"),
    "expected E.B to inline to 2, got: {code}"
  );
  let init = find_exported_const_initializer(&parsed, "x").expect("exported const x initializer");
  assert!(matches!(init.stx.as_ref(), Expr::LitNum(num) if num.stx.value.0 == 2.0));
}

#[test]
fn preserves_runtime_lowering_for_const_enums_in_runtime_mode() {
  let src = r#"
    export const enum E { A, B = 5, C }
    export const x = E.C;
  "#;
  let (code, parsed) = minify_ts_module(
    src,
    TsEraseOptions {
      const_enum_mode: ConstEnumMode::Runtime,
      ..TsEraseOptions::default()
    },
  );

  assert!(
    program_declares_var(&parsed, "E"),
    "runtime mode should preserve enum lowering: {code}"
  );
}

