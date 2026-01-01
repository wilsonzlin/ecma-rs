use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, JsxMode, LibFile};
use typecheck_ts::{FileKey, Host, HostError, Program, TypeKindSummary};

const JSX_LIB: &str = r#"
declare namespace JSX {
  interface Element {}
  interface IntrinsicElements {
    div: { id?: string; children?: string };
    span: { children?: string };

    "Svg:Path": {};
    "my-tag": {};
    "My-Tag": {};
  }
}
"#;

#[derive(Default)]
struct TestHost {
  files: HashMap<FileKey, Arc<str>>,
  options: CompilerOptions,
  libs: Vec<LibFile>,
  edges: HashMap<(FileKey, String), FileKey>,
}

impl TestHost {
  fn new(options: CompilerOptions) -> Self {
    TestHost {
      files: HashMap::new(),
      options,
      libs: Vec::new(),
      edges: HashMap::new(),
    }
  }

  fn with_file(mut self, key: FileKey, text: &str) -> Self {
    self.files.insert(key, Arc::from(text));
    self
  }

  fn with_lib(mut self, lib: LibFile) -> Self {
    self.libs.push(lib);
    self
  }

  fn link(mut self, from: FileKey, spec: &str, to: FileKey) -> Self {
    self.edges.insert((from, spec.to_string()), to);
    self
  }
}

impl Host for TestHost {
  fn file_text(&self, file: &FileKey) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, from: &FileKey, specifier: &str) -> Option<FileKey> {
    self
      .edges
      .get(&(from.clone(), specifier.to_string()))
      .cloned()
  }

  fn compiler_options(&self) -> CompilerOptions {
    self.options.clone()
  }

  fn lib_files(&self) -> Vec<LibFile> {
    self.libs.clone()
  }

  fn file_kind(&self, file: &FileKey) -> FileKind {
    if let Some(lib) = self.libs.iter().find(|l| &l.key == file) {
      return lib.kind;
    }
    if file.as_str().ends_with(".tsx") {
      FileKind::Tsx
    } else {
      FileKind::Ts
    }
  }
}

fn jsx_lib_file() -> LibFile {
  LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(JSX_LIB),
  }
}

fn empty_lib_file() -> LibFile {
  LibFile {
    key: FileKey::new("empty.d.ts"),
    name: Arc::from("empty.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(""),
  }
}

#[test]
fn jsx_requires_compiler_option() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = None;

  let entry = FileKey::new("entry.tsx");
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), "const el = <div />;");
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::JSX_DISABLED.as_str(),
    "expected JSX_DISABLED, got {diagnostics:?}"
  );
}

#[test]
fn jsx_namespace_missing_emits_diagnostic() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let host = TestHost::new(options)
    .with_lib(empty_lib_file())
    .with_file(entry.clone(), "const el = <div />;");
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::JSX_NAMESPACE_MISSING.as_str(),
    "expected JSX_NAMESPACE_MISSING, got {diagnostics:?}"
  );
}

#[test]
fn intrinsic_props_checked() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
const ok = <div id="x">hi</div>;
const ok2 = <div {...{ id: "y", children: "yo" }} />;
const bad = <div id={123} />;
const bad2 = <div {...{ id: 123 }} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected a type mismatch diagnostic, got {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str()),
    "did not expect unknown identifiers, got {diagnostics:?}"
  );
}

#[test]
fn intrinsic_attribute_values_are_contextually_typed() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);
  options.no_implicit_any = true;

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  interface IntrinsicElements {
    div: { onClick?: (ev: { x: number }) => void };
  }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
 <div onClick={(ev) => { const n: number = ev.x; }} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics (including implicit any) for contextually typed intrinsic attrs, got {diagnostics:?}"
  );
}

#[test]
fn component_props_checked_for_imported_component_and_imported_value_used_only_in_jsx() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let component = FileKey::new("component.ts");
  let values = FileKey::new("values.ts");
  let main = FileKey::new("main.tsx");

  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(
      component.clone(),
      r#"export function Foo(props: { x: number; children?: string }): JSX.Element { return null as any; }"#,
    )
    .with_file(values.clone(), "export const x: number = 1;")
    .with_file(
      main.clone(),
      r#"
import { Foo } from "./component";
import { x } from "./values";
const ok = <Foo x={x}>hi</Foo>;
const ok2 = <Foo {...{ x }}>hi</Foo>;
const bad = <Foo x={"no"} />;
"#,
    )
    .link(main.clone(), "./component", component)
    .link(main.clone(), "./values", values);

  let program = Program::new(host, vec![main]);
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str()),
    "did not expect unknown identifiers, got {diagnostics:?}"
  );
  assert!(
    diagnostics.iter().any(|d| {
      d.code.as_str() == codes::TYPE_MISMATCH.as_str()
        || d.code.as_str() == codes::NO_OVERLOAD.as_str()
    }),
    "expected a prop type error for bad JSX usage, got {diagnostics:?}"
  );
}

#[test]
fn nested_jsx_child_elements_record_types_for_type_at() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = "const el = <div><span /></div>;";
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry.clone()]);
  let file_id = program.file_id(&entry).expect("file id");

  let offset = source.find("<span").expect("span tag") as u32 + 1;
  let ty = program.type_at(file_id, offset).expect("type at <span>");
  assert_ne!(
    program.type_kind(ty),
    TypeKindSummary::Unknown,
    "expected nested JSX element to have a non-unknown type"
  );
}

#[test]
fn jsx_empty_expression_container_is_ignored() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"const el = <div>{/* comment */}</div>;"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics for JSX empty expression container, got {diagnostics:?}"
  );
}

#[test]
fn jsx_spread_attrs_are_merged_before_props_check() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let component = FileKey::new("component.ts");
  let main = FileKey::new("main.tsx");

  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(
      component.clone(),
      r#"export function Foo(props: { x: number }) { return null as any; }"#,
    )
    .with_file(
      main.clone(),
      r#"
import { Foo } from "./component";
const ok = <Foo {...{ x: 1 }} {...{}} />;
"#,
    )
    .link(main.clone(), "./component", component);

  let program = Program::new(host, vec![main]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics for merged spreads, got {diagnostics:?}"
  );
}

#[test]
fn jsx_spread_children_are_checked_against_children_prop() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"const el = <div>{...[1]}</div>;"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected a type mismatch diagnostic for spread children, got {diagnostics:?}"
  );
}

#[test]
fn multiple_jsx_children_become_array() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
const ok = <div>hi</div>;
const bad = <div>{"a"}{"b"}</div>;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics
      .iter()
      .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
      .count(),
    1,
    "expected exactly one type mismatch diagnostic for multiple children, got {diagnostics:?}"
  );
}

#[test]
fn intrinsic_namespaced_and_hyphenated_tags_are_not_value_identifiers() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
const a = <Svg:Path />;
const b = <my-tag />;
const c = <My-Tag />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str()),
    "did not expect unknown identifiers, got {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| { d.code.as_str() == codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.as_str() }),
    "did not expect unknown intrinsic elements, got {diagnostics:?}"
  );
}

#[test]
fn unknown_intrinsic_emits_diagnostic() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), "const el = <bogus />;");
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::JSX_UNKNOWN_INTRINSIC_ELEMENT.as_str()),
    "expected JSX_UNKNOWN_INTRINSIC_ELEMENT, got {diagnostics:?}"
  );
}

#[test]
fn component_member_tags_seed_base_identifier() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let component = FileKey::new("component.ts");
  let main = FileKey::new("main.tsx");

  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(
      component.clone(),
      r#"export const Foo = { Bar: (props: { x: number }): JSX.Element => null as any };"#,
    )
    .with_file(
      main.clone(),
      r#"
import { Foo } from "./component";
const ok = <Foo.Bar x={1} />;
"#,
    )
    .link(main.clone(), "./component", component);

  let program = Program::new(host, vec![main]);
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::UNKNOWN_IDENTIFIER.as_str()),
    "did not expect unknown identifiers, got {diagnostics:?}"
  );
}

#[test]
fn intrinsic_excess_props_are_reported() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), r#"const bad = <div foo="x" />;"#);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::EXCESS_PROPERTY.as_str()),
    "expected an excess property diagnostic, got {diagnostics:?}"
  );
}

#[test]
fn component_without_props_param_allows_empty_props() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
function Foo() { return null as any; }
const ok = <Foo />;
const bad = <Foo x={1} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "expected EXCESS_PROPERTY, got {diagnostics:?}"
  );
}

#[test]
fn component_return_type_must_be_valid_jsx_element() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element { readonly __tag: "jsx" }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
function Foo(): string { return "hi"; }
function Bar(): JSX.Element | null { return null; }
const ok = <Bar />;
const bad = <Foo />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected exactly one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::NO_OVERLOAD.as_str(),
    "expected NO_OVERLOAD, got {diagnostics:?}"
  );
}

#[test]
fn element_children_attribute_controls_children_prop_name() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  interface ElementChildrenAttribute { kid: {} }
  interface IntrinsicElements {
    div: { kid?: string };
  }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = "const el = <div>hi</div>;";
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics for ElementChildrenAttribute, got {diagnostics:?}"
  );
}

#[test]
fn qualified_jsx_element_return_type_is_resolved() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
function Foo(): JSX.Element { return null as any; }
const ok = <Foo />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );
}

#[test]
fn generic_component_respects_type_param_constraints() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
function Foo<T extends number>(props: { x: T }): JSX.Element { return null as any; }
const ok = <Foo x={1} />;
const bad = <Foo x={"no"} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected a type mismatch diagnostic for constrained generic props, got {diagnostics:?}"
  );
}

#[test]
fn intrinsic_attributes_are_merged_into_expected_props() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  interface IntrinsicAttributes { key?: string }
  interface IntrinsicElements {
    div: { id?: string };
  }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
function Foo(props: { x: number }): JSX.Element { return null as any; }
const ok = <div key="x" id="y" />;
const ok2 = <Foo x={1} key="k" />;
const bad = <div key={123} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics
      .iter()
      .filter(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str())
      .count(),
    1,
    "expected exactly one type mismatch diagnostic, got {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::EXCESS_PROPERTY.as_str()),
    "did not expect excess property diagnostics, got {diagnostics:?}"
  );
}

#[test]
fn intrinsic_class_attributes_apply_to_construct_signatures() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  interface IntrinsicAttributes { key?: string }
  interface IntrinsicClassAttributes<T> { ref?: T }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
interface FooInstance { readonly _tag: "Foo" }
declare const Foo: { new (props: { x: number }): FooInstance };
declare const inst: FooInstance;
const ok = <Foo x={1} ref={inst} key="k" />;
const bad = <Foo x={1} ref={123} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected a type mismatch diagnostic for bad ref type, got {diagnostics:?}"
  );
  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::EXCESS_PROPERTY.as_str()),
    "did not expect excess property diagnostics, got {diagnostics:?}"
  );
}

#[test]
fn element_attributes_property_controls_class_component_props() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  interface ElementAttributesProperty { props: {} }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
interface FooProps { x: number }
interface FooInstance { props: FooProps }
declare const Foo: { new (): FooInstance };
const ok = <Foo x={1} />;
const bad = <Foo y={1} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "expected excess property, got {diagnostics:?}"
  );
}

#[test]
fn library_managed_attributes_are_applied_to_component_props() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  type LibraryManagedAttributes<C, P> = P & { managed?: string };
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
function Foo(props: { x: number }): JSX.Element { return null as any; }
const ok = <Foo x={1} managed="yes" />;
const bad = <Foo x={1} managed={123} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert!(
    !diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::EXCESS_PROPERTY.as_str()),
    "did not expect excess property diagnostics, got {diagnostics:?}"
  );
  assert!(
    diagnostics
      .iter()
      .any(|d| d.code.as_str() == codes::TYPE_MISMATCH.as_str()),
    "expected a type mismatch diagnostic for managed, got {diagnostics:?}"
  );
}

#[test]
fn element_class_filters_invalid_class_components() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let jsx = LibFile {
    key: FileKey::new("jsx.d.ts"),
    name: Arc::from("jsx.d.ts"),
    kind: FileKind::Dts,
    text: Arc::from(
      r#"
declare namespace JSX {
  interface Element {}
  interface ElementClass { render(): Element }
}
"#,
    ),
  };

  let entry = FileKey::new("entry.tsx");
  let source = r#"
interface FooInstance { props: { x: number } }
declare const Foo: { new (props: { x: number }): FooInstance };
const el = <Foo x={1} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx)
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::NO_OVERLOAD.as_str(),
    "expected NO_OVERLOAD, got {diagnostics:?}"
  );
}

#[test]
fn value_tag_string_literal_is_treated_as_intrinsic_element() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
const Tag = "div";
const ok = <Tag id="x">hi</Tag>;
const bad = <Tag foo="x" />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected exactly one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "expected EXCESS_PROPERTY, got {diagnostics:?}"
  );
}

#[test]
fn value_tag_union_of_string_literals_requires_common_props() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
declare const cond: boolean;
const Tag = cond ? "div" : "span";
const ok = <Tag children="hi" />;
const bad = <Tag id="x" />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected exactly one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "expected EXCESS_PROPERTY, got {diagnostics:?}"
  );
}

#[test]
fn value_tag_union_of_components_requires_common_props() {
  let mut options = CompilerOptions::default();
  options.no_default_lib = true;
  options.jsx = Some(JsxMode::React);

  let entry = FileKey::new("entry.tsx");
  let source = r#"
declare const cond: boolean;
function Foo(props: { x: number }): JSX.Element { return null as any; }
function Bar(props: { x: number; y?: number }): JSX.Element { return null as any; }
const Comp = cond ? Foo : Bar;
const ok = <Comp x={1} />;
const bad = <Comp x={1} y={2} />;
"#;
  let host = TestHost::new(options)
    .with_lib(jsx_lib_file())
    .with_file(entry.clone(), source);
  let program = Program::new(host, vec![entry]);
  let diagnostics = program.check();

  assert_eq!(
    diagnostics.len(),
    1,
    "expected exactly one diagnostic, got {diagnostics:?}"
  );
  assert_eq!(
    diagnostics[0].code.as_str(),
    codes::EXCESS_PROPERTY.as_str(),
    "expected EXCESS_PROPERTY, got {diagnostics:?}"
  );
}
