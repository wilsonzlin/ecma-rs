//! HIR-preferred JSX body checking: element/tag/attribute/children typing is
//! driven from `hir_js::JsxElement` (`ExprKind::Jsx`) via the body expr map.
//! Nested JSX children recurse on HIR `ExprId`s (AstIndex does not index nested
//! `JsxElem` nodes as expressions).
//!
//! Residual AST path: missing HIR at the element span; nested non-JSX attr /
//! child expression values still resolve AST nodes by span for `check_expr`
//! and excess-property reporting. No AST `TypeLowerer` / `TypeExpr` here.

mod common;

use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, JsxMode, LibFile};
use typecheck_ts::{FileKey, MemoryHost, Program, TypeKindSummary};

const JSX_LIB: &str = r#"
declare namespace JSX {
  interface Element {}
  interface IntrinsicElements {
    div: { id?: string; children?: string };
    span: { children?: string };
  }
}
"#;

fn jsx_host(source: &str) -> (MemoryHost, FileKey) {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);
  let mut host = MemoryHost::with_options(options);
  host.add_lib(common::core_globals_lib());
  host.add_lib(LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(JSX_LIB),
  });
  let entry = FileKey::new("entry.tsx");
  host.insert(entry.clone(), Arc::from(source));
  (host, entry)
}

#[test]
fn hir_jsx_intrinsic_props_checked() {
  let (host, entry) = jsx_host(
    r#"
const ok = <div id="x">hi</div>;
const bad = <div id={123} />;
"#,
  );
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected HIR-driven intrinsic prop mismatch, got {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::CANNOT_FIND_NAME.as_str()),
    "did not expect unknown identifiers, got {diagnostics:?}"
  );
}

#[test]
fn hir_jsx_component_tag_props_checked() {
  let (host, entry) = jsx_host(
    r#"
function Foo(props: { x: number }): JSX.Element { return null as any; }
const ok = <Foo x={1} />;
const bad = <Foo x={"no"} />;
"#,
  );
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics.iter().any(|d| {
      d.code.as_str() == codes::TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::NO_OVERLOAD.as_str()
    }),
    "expected HIR-driven component prop error, got {diagnostics:?}"
  );
}

#[test]
fn hir_jsx_member_tag_resolves_base() {
  let (host, entry) = jsx_host(
    r#"
const NS = {
  Bar(props: { n: number }): JSX.Element { return null as any; }
};
const ok = <NS.Bar n={1} />;
const bad = <NS.Bar n={"x"} />;
"#,
  );
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::CANNOT_FIND_NAME.as_str()),
    "HIR member tag should resolve NS, got {diagnostics:?}"
  );
  assert!(
    diagnostics.iter().any(|d| {
      d.code.as_str() == codes::TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::NO_OVERLOAD.as_str()
    }),
    "expected HIR-driven member-tag prop error, got {diagnostics:?}"
  );
}

#[test]
fn hir_jsx_nested_child_element_typed() {
  let source = "const el = <div><span /></div>;";
  let (host, entry) = jsx_host(source);
  let program = Program::new(host, vec![entry.clone()]);
  let file_id = program.file_id(&entry).expect("file id");
  let offset = source.find("<span").expect("span tag") as u32 + 1;
  let ty = program
    .type_at(file_id, offset)
    .expect("type at nested JSX");
  assert_ne!(
    program.type_kind(ty),
    TypeKindSummary::Unknown,
    "nested HIR JsxChild::Element should record a non-unknown type"
  );
}

#[test]
fn hir_jsx_empty_expr_container_ignored() {
  let (host, entry) = jsx_host(r#"const el = <div>{/* comment */}</div>;"#);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "HIR empty JsxExprContainer (expr: None) should be ignored, got {diagnostics:?}"
  );
}

#[test]
fn hir_jsx_spread_attr_checked() {
  let (host, entry) = jsx_host(
    r#"
const ok = <div {...{ id: "y" }} />;
const bad = <div {...{ id: 123 }} />;
"#,
  );
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected HIR-driven spread attr mismatch, got {diagnostics:?}"
  );
}
