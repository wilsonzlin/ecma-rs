use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode};
use parse_js::ast::expr::pat::Pat;
use parse_js::ast::expr::Expr;
use parse_js::ast::import_export::{ExportNames, ModuleExportImportName};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;
use parse_js::operator::OperatorName;
use parse_js::{parse_with_options, ParseOptions, SourceType};

fn minify_ts_module_deterministic(src: &str) -> (String, Node<TopLevel>) {
  fn minify_once(src: &str) -> String {
    let mut out = Vec::new();
    minify_with_options(
      MinifyOptions::new(TopLevelMode::Module).with_dialect(Dialect::Ts),
      src,
      &mut out,
    )
    .expect("minify should succeed");
    String::from_utf8(out).expect("minifier output must be UTF-8")
  }

  let code1 = minify_once(src);
  let code2 = minify_once(src);
  assert_eq!(
    code1, code2,
    "minifier output should be deterministic across runs. first: {code1} second: {code2}"
  );

  let parsed = parse_with_options(
    &code1,
    ParseOptions {
      dialect: Dialect::Js,
      source_type: SourceType::Module,
    },
  )
  .expect("output should parse as JavaScript");

  (code1, parsed)
}

fn has_exported_var_decl(program: &Node<TopLevel>, name: &str) -> bool {
  program.stx.body.iter().any(|stmt| match stmt.stx.as_ref() {
    Stmt::VarDecl(decl) if decl.stx.export => decl.stx.declarators.iter().any(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == name)
    }),
    _ => false,
  })
}

fn count_top_level_var_bindings(program: &Node<TopLevel>, name: &str) -> usize {
  program
    .stx
    .body
    .iter()
    .filter_map(|stmt| match stmt.stx.as_ref() {
      Stmt::VarDecl(decl) => Some(decl),
      _ => None,
    })
    .flat_map(|decl| decl.stx.declarators.iter())
    .filter(|declarator| {
      matches!(declarator.pattern.stx.pat.stx.as_ref(), Pat::Id(id) if id.stx.name == name)
    })
    .count()
}

fn count_export_list_entries(program: &Node<TopLevel>, exported: &str) -> usize {
  program
    .stx
    .body
    .iter()
    .filter_map(|stmt| match stmt.stx.as_ref() {
      Stmt::ExportList(export_list) if !export_list.stx.type_only => Some(export_list),
      _ => None,
    })
    .filter(|export_list| export_list.stx.from.is_none())
    .filter_map(|export_list| match &export_list.stx.names {
      ExportNames::Specific(entries) => Some(entries),
      _ => None,
    })
    .flat_map(|entries| entries.iter())
    .filter(|entry| !entry.stx.type_only && entry.stx.alias.stx.name == exported)
    .count()
}

fn find_exported_local_binding(program: &Node<TopLevel>, exported: &str) -> Option<String> {
  for stmt in &program.stx.body {
    let Stmt::ExportList(export_list) = stmt.stx.as_ref() else {
      continue;
    };
    if export_list.stx.type_only || export_list.stx.from.is_some() {
      continue;
    }
    let ExportNames::Specific(entries) = &export_list.stx.names else {
      continue;
    };
    for entry in entries {
      if entry.stx.type_only || entry.stx.alias.stx.name != exported {
        continue;
      }
      let ModuleExportImportName::Ident(local) = &entry.stx.exportable else {
        continue;
      };
      return Some(local.clone());
    }
  }
  None
}

struct Iife<'a> {
  arg: &'a Node<Expr>,
  body: &'a Vec<Node<Stmt>>,
}

fn extract_iife(stmt: &Node<Stmt>) -> Option<Iife<'_>> {
  let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
    return None;
  };
  let Expr::Binary(comma) = expr_stmt.stx.expr.stx.as_ref() else {
    return None;
  };
  if comma.stx.operator != OperatorName::Comma {
    return None;
  }
  let Expr::Call(call) = comma.stx.right.stx.as_ref() else {
    return None;
  };
  if call.stx.arguments.len() != 1 {
    return None;
  }
  let Expr::Func(func_expr) = call.stx.callee.stx.as_ref() else {
    return None;
  };
  let func = &func_expr.stx.func.stx;
  if func.parameters.len() != 1 {
    return None;
  }
  let Pat::Id(_param) = func.parameters[0].stx.pattern.stx.pat.stx.as_ref() else {
    return None;
  };
  let Some(parse_js::ast::func::FuncBody::Block(body)) = func.body.as_ref() else {
    return None;
  };
  Some(Iife {
    arg: &call.stx.arguments[0].stx.value,
    body,
  })
}

fn iife_targets_outer_ident(iife: &Iife<'_>, outer: &str) -> bool {
  let Expr::Binary(or) = iife.arg.stx.as_ref() else {
    return false;
  };
  if or.stx.operator != OperatorName::LogicalOr {
    return false;
  }
  matches!(or.stx.left.stx.as_ref(), Expr::Id(id) if id.stx.name == outer)
}

fn is_member_access(expr: &Node<Expr>, object: &str, key: &str) -> bool {
  match expr.stx.as_ref() {
    Expr::ComputedMember(member) => {
      matches!(member.stx.object.stx.as_ref(), Expr::Id(id) if id.stx.name == object)
        && matches!(member.stx.member.stx.as_ref(), Expr::LitStr(lit) if lit.stx.value == key)
    }
    Expr::Member(member) => {
      matches!(member.stx.left.stx.as_ref(), Expr::Id(id) if id.stx.name == object)
        && member.stx.right == key
    }
    _ => false,
  }
}

fn is_member_assignment_stmt(stmt: &Node<Stmt>, object: &str, key: &str, value: &str) -> bool {
  let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
    return false;
  };
  let Expr::Binary(assign) = expr_stmt.stx.expr.stx.as_ref() else {
    return false;
  };
  if assign.stx.operator != OperatorName::Assignment {
    return false;
  }
  if !is_member_access(&assign.stx.left, object, key) {
    return false;
  }
  matches!(assign.stx.right.stx.as_ref(), Expr::Id(id) if id.stx.name == value)
}

fn member_assignment_rhs_ident(stmt: &Node<Stmt>, object: &str, key: &str) -> Option<String> {
  let Stmt::Expr(expr_stmt) = stmt.stx.as_ref() else {
    return None;
  };
  let Expr::Binary(assign) = expr_stmt.stx.expr.stx.as_ref() else {
    return None;
  };
  if assign.stx.operator != OperatorName::Assignment {
    return None;
  }
  if !is_member_access(&assign.stx.left, object, key) {
    return None;
  }
  let Expr::Id(id) = assign.stx.right.stx.as_ref() else {
    return None;
  };
  Some(id.stx.name.clone())
}

#[test]
fn attaches_local_enum_binding_before_exported_namespace_iife() {
  let src = r#"
    export namespace N {
      eval("x");
      enum E { A = 1, B }
      export namespace E { export const x = 123; }
    }
  "#;
  let (code, parsed) = minify_ts_module_deterministic(src);

  let n_iife = parsed
    .stx
    .body
    .iter()
    .find_map(extract_iife)
    .filter(|iife| iife_targets_outer_ident(iife, "N"))
    .unwrap_or_else(|| panic!("expected top-level namespace IIFE for N. output: {code}"));

  let (exported_e_iife_index, local) = n_iife
    .body
    .iter()
    .enumerate()
    .find_map(|(idx, stmt)| {
      let local = member_assignment_rhs_ident(stmt, "N", "E")?;
      let next = n_iife.body.get(idx + 1)?;
      extract_iife(next)?;
      Some((idx + 1, local))
    })
    .unwrap_or_else(|| {
      panic!(
        "expected `N[\"E\"] = <value>` immediately followed by an IIFE for the exported E. output: {code}"
      )
    });

  assert!(
    exported_e_iife_index > 0,
    "exported E IIFE should not be the first statement in N body. output: {code}"
  );
  assert!(
    is_member_assignment_stmt(&n_iife.body[exported_e_iife_index - 1], "N", "E", &local),
    "expected pre-existing local binding `{local}` to be attached as N[\"E\"] = {local} immediately before the exported E IIFE. output: {code}"
  );
}

#[test]
fn attaches_local_namespace_binding_before_exported_enum_iife() {
  let src = r#"
    export namespace N {
      eval("x");
      namespace E { export const x = 123; }
      export enum E { A = 1, B }
    }
  "#;
  let (code, parsed) = minify_ts_module_deterministic(src);

  let n_iife = parsed
    .stx
    .body
    .iter()
    .find_map(extract_iife)
    .filter(|iife| iife_targets_outer_ident(iife, "N"))
    .unwrap_or_else(|| panic!("expected top-level namespace IIFE for N. output: {code}"));

  let (exported_e_iife_index, local) = n_iife
    .body
    .iter()
    .enumerate()
    .find_map(|(idx, stmt)| {
      let local = member_assignment_rhs_ident(stmt, "N", "E")?;
      let next = n_iife.body.get(idx + 1)?;
      extract_iife(next)?;
      Some((idx + 1, local))
    })
    .unwrap_or_else(|| {
      panic!(
        "expected `N[\"E\"] = <value>` immediately followed by an IIFE for the exported E. output: {code}"
      )
    });

  assert!(
    exported_e_iife_index > 0,
    "exported E IIFE should not be the first statement in N body. output: {code}"
  );
  assert!(
    is_member_assignment_stmt(&n_iife.body[exported_e_iife_index - 1], "N", "E", &local),
    "expected pre-existing local binding `{local}` to be attached as N[\"E\"] = {local} immediately before the exported E IIFE. output: {code}"
  );
}

#[test]
fn merges_invalid_namespace_and_enum_exports_using_single_binding() {
  let src = r#"
    eval("x");
    export namespace static { export const x = 1; }
    export enum static { A = 1, B }
  "#;
  let (code, parsed) = minify_ts_module_deterministic(src);

  assert_eq!(
    count_export_list_entries(&parsed, "static"),
    1,
    "expected a single export list entry for the merged `static` value. output: {code}"
  );

  let local = find_exported_local_binding(&parsed, "static")
    .expect("expected `export { <local> as static }` for merged namespace/enum");
  assert_eq!(
    count_top_level_var_bindings(&parsed, &local),
    1,
    "expected a single top-level var binding for merged `static` runtime value. output: {code}"
  );

  let iife_count = parsed
    .stx
    .body
    .iter()
    .filter_map(extract_iife)
    .filter(|iife| iife_targets_outer_ident(iife, &local))
    .count();
  assert_eq!(
    iife_count, 2,
    "expected both namespace and enum lowering to target the same merged binding `{local}`. output: {code}"
  );
}

#[test]
fn exported_runtime_enum_still_emits_export_var_despite_synthetic_iife_param_span() {
  let src = r#"
    export enum E { A }
  "#;
  let (code, parsed) = minify_ts_module_deterministic(src);

  assert!(
    has_exported_var_decl(&parsed, "E"),
    "expected `export var E` emission for runtime enum lowering. output: {code}"
  );
  let iife_count = parsed
    .stx
    .body
    .iter()
    .filter_map(extract_iife)
    .filter(|iife| iife_targets_outer_ident(iife, "E"))
    .count();
  assert_eq!(
    iife_count, 1,
    "expected a single enum IIFE targeting the exported enum binding `E`. output: {code}"
  );
}
