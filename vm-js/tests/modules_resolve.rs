use vm_js::{
  BindingName, ModuleGraph, ResolveExportResult, ResolvedBinding, SourceTextModuleRecord,
};

fn parse(src: &str) -> SourceTextModuleRecord {
  SourceTextModuleRecord::parse(src).expect("module should parse")
}

#[test]
fn exported_names_and_resolve_export() {
  let mut graph = ModuleGraph::new();

  let a = graph.add_module_with_specifier(
    "a",
    parse(
      r#"
      const foo = 1;
      export { foo as bar };
      export { x as y } from "b";
      export * from "c";
      export * as ns from "c";
    "#,
    ),
  );

  let b = graph.add_module_with_specifier(
    "b",
    parse(
      r#"
      const x = 1;
      export { x };
    "#,
    ),
  );

  let c = graph.add_module_with_specifier(
    "c",
    parse(
      r#"
      const c1 = 1;
      const c2 = 2;
      export { c1, c2 as renamed, c1 as default };
    "#,
    ),
  );

  graph.link_all_by_specifier();

  let names = graph.module(a).get_exported_names(&graph, a);
  assert_eq!(
    names,
    vec!["bar", "y", "ns", "c1", "renamed"]
      .into_iter()
      .map(String::from)
      .collect::<Vec<_>>()
  );

  assert_eq!(
    graph.module(a).resolve_export(&graph, a, "bar"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: a,
      binding_name: BindingName::Name("foo".to_string()),
    })
  );

  assert_eq!(
    graph.module(a).resolve_export(&graph, a, "y"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: b,
      binding_name: BindingName::Name("x".to_string()),
    })
  );

  assert_eq!(
    graph.module(a).resolve_export(&graph, a, "ns"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: c,
      binding_name: BindingName::Namespace,
    })
  );

  assert_eq!(
    graph.module(a).resolve_export(&graph, a, "c1"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: c,
      binding_name: BindingName::Name("c1".to_string()),
    })
  );
}

#[test]
fn circular_export_star_does_not_infinite_loop() {
  let mut graph = ModuleGraph::new();

  let d = graph.add_module_with_specifier(
    "d",
    parse(
      r#"
      export * from "e";
    "#,
    ),
  );

  let e = graph.add_module_with_specifier(
    "e",
    parse(
      r#"
      export * from "d";
      const z = 1;
      export { z };
    "#,
    ),
  );

  graph.link_all_by_specifier();

  assert_eq!(
    graph.module(d).get_exported_names(&graph, d),
    vec!["z".to_string()]
  );

  assert_eq!(
    graph.module(d).resolve_export(&graph, d, "z"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: e,
      binding_name: BindingName::Name("z".to_string()),
    })
  );
}

#[test]
fn ambiguous_star_exports() {
  let mut graph = ModuleGraph::new();

  let m1 = graph.add_module_with_specifier(
    "m1",
    parse(
      r#"
      const x = 1;
      export { x };
    "#,
    ),
  );

  let m2 = graph.add_module_with_specifier(
    "m2",
    parse(
      r#"
      const x = 2;
      export { x };
    "#,
    ),
  );

  let star = graph.add_module_with_specifier(
    "star",
    parse(
      r#"
      export * from "m1";
      export * from "m2";
    "#,
    ),
  );

  graph.link_all_by_specifier();

  assert_eq!(
    graph.module(star).resolve_export(&graph, star, "x"),
    ResolveExportResult::Ambiguous
  );

  assert_eq!(
    graph.module(star).get_exported_names(&graph, star),
    vec!["x".to_string()]
  );

  assert_ne!(
    graph.module(m1).resolve_export(&graph, m1, "x"),
    graph.module(m2).resolve_export(&graph, m2, "x")
  );
}

#[test]
fn exported_names_preserve_local_and_indirect_duplicates() {
  let mut graph = ModuleGraph::new();

  let a = graph.add_module_with_specifier(
    "a",
    parse(
      r#"
      const foo = 1;
      export { foo as dup, foo as dup };
      export { x as y } from "b";
      export { x as y } from "b";
      export * from "c";
    "#,
    ),
  );

  let b = graph.add_module_with_specifier(
    "b",
    parse(
      r#"
      const x = 1;
      export { x };
    "#,
    ),
  );

  let _c = graph.add_module_with_specifier(
    "c",
    parse(
      r#"
      const c1 = 1;
      export { c1 };
    "#,
    ),
  );

  graph.link_all_by_specifier();

  // `GetExportedNames` appends `[[LocalExportEntries]]` + `[[IndirectExportEntries]]` verbatim,
  // including duplicates, and only de-dupes names that come from `export *`.
  assert_eq!(
    graph.module(a).get_exported_names(&graph, a),
    vec!["dup", "dup", "y", "y", "c1"]
      .into_iter()
      .map(String::from)
      .collect::<Vec<_>>()
  );

  // Local exports take precedence over indirect exports/star exports.
  assert_eq!(
    graph.module(a).resolve_export(&graph, a, "dup"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: a,
      binding_name: BindingName::Name("foo".to_string()),
    })
  );

  // Indirect export duplicates still resolve deterministically.
  assert_eq!(
    graph.module(a).resolve_export(&graph, a, "y"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: b,
      binding_name: BindingName::Name("x".to_string()),
    })
  );
}

#[test]
fn ambiguous_star_exports_when_binding_name_differs() {
  let mut graph = ModuleGraph::new();

  let base = graph.add_module_with_specifier(
    "base",
    parse(
      r#"
      const a = 1;
      const b = 2;
      export { a, b };
    "#,
    ),
  );

  let m1 = graph.add_module_with_specifier(
    "m1",
    parse(
      r#"
      export { a as x } from "base";
    "#,
    ),
  );

  let m2 = graph.add_module_with_specifier(
    "m2",
    parse(
      r#"
      export { b as x } from "base";
    "#,
    ),
  );

  let star = graph.add_module_with_specifier(
    "star",
    parse(
      r#"
      export * from "m1";
      export * from "m2";
    "#,
    ),
  );

  graph.link_all_by_specifier();

  // Both `m1` and `m2` contribute an `x` export through `export *`, and both resolve into the same
  // target module but with different binding names, which is still ambiguous per ECMA-262.
  assert_eq!(
    graph.module(star).resolve_export(&graph, star, "x"),
    ResolveExportResult::Ambiguous
  );

  // `GetExportedNames` still reports the name once (it de-dups star-exported names).
  assert_eq!(
    graph.module(star).get_exported_names(&graph, star),
    vec!["x".to_string()]
  );

  assert_eq!(
    graph.module(m1).resolve_export(&graph, m1, "x"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: base,
      binding_name: BindingName::Name("a".to_string()),
    })
  );
  assert_eq!(
    graph.module(m2).resolve_export(&graph, m2, "x"),
    ResolveExportResult::Resolved(ResolvedBinding {
      module: base,
      binding_name: BindingName::Name("b".to_string()),
    })
  );
}

