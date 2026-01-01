use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::codes;
use typecheck_ts::lib_support::{CompilerOptions, FileKind, JsxMode, LibFile};
use typecheck_ts::{FileKey, Host, HostError, Program};

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
