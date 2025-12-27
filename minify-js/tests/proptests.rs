use minify_js::{minify_with_options, Dialect, MinifyOptions, TopLevelMode};
use parse_js::{parse_with_options, ParseOptions, SourceType};
use proptest::prelude::*;

#[derive(Clone, Debug)]
struct ProgramCase {
  mode: TopLevelMode,
  input_dialect: Dialect,
  output_dialect: Dialect,
  source: String,
}

fn source_type(mode: TopLevelMode) -> SourceType {
  match mode {
    TopLevelMode::Global => SourceType::Script,
    TopLevelMode::Module => SourceType::Module,
  }
}

fn ident() -> impl Strategy<Value = String> {
  const CHARS: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
  prop::collection::vec(prop::sample::select(CHARS.to_vec()), 1..6)
    .prop_map(|bytes| String::from_utf8(bytes).unwrap())
}

fn js_statement() -> impl Strategy<Value = String> {
  prop_oneof![
    ident().prop_map(|name| format!("const {name} = 1 + 2 * 3;")),
    (ident(), ident()).prop_map(|(fn_name, param)| format!(
      "function {fn_name}({param}) {{ return {param} ?? 0; }}"
    )),
    ident().prop_map(|name| format!("const {name} = [1,2,3].map(v => v * v);")),
    (ident(), ident()).prop_map(|(exported, base)| format!(
      "export const {exported} = ({base}) => ({base} && {base}.value);"
    )),
    ident().prop_map(|name| format!("class {name} {{ method(v) {{ return v?.toString(); }} }}")),
    prop::sample::select(vec![
      "const helper = (...args) => args.join(\"\");".to_string(),
      "export default (value => ({computed: value ?? 0}));".to_string(),
      "const chain = promise.then(v => v ?? 1);".to_string(),
    ]),
  ]
}

fn jsx_statement() -> impl Strategy<Value = String> {
  prop_oneof![
    prop::sample::select(vec![
      r#"const element = <div className="box">{value}</div>;"#.to_string(),
      r#"export const list = <ul>{items.map(item => <li>{item}</li>)}</ul>;"#
        .to_string(),
      r#"function Component(props){ return <section data-id={props.id ?? "x"}>{props.children}</section>; }"#
        .to_string(),
    ]),
    ident().prop_map(|name| format!("const {name} = <span>{{{name}}}</span>;")),
  ]
}

fn ts_statement() -> impl Strategy<Value = String> {
  prop_oneof![
    ident().prop_map(|name| format!("type {name} = {{ value: string; count?: number }};")),
    ident().prop_map(|name| format!("const {name}: Array<number | string> = [1, \"two\"];")),
    prop::sample::select(vec![
      "interface User { id: number; name?: string; readonly active?: boolean; }".to_string(),
      "function wrap<T>(value: T): T { return value; }".to_string(),
      "const pair: [number, string] = [1, \"x\"];".to_string(),
      "import type { Foo } from \"./types\";".to_string(),
      "export type { Foo as FooType };".to_string(),
      "const checked: number = (maybe as any) satisfies number ? 1 : 2;".to_string(),
      "class Box<T> implements Iterable<T> { constructor(private value: T) {} *[Symbol.iterator](): Iterator<T> { yield this.value; } }".to_string(),
      "export default function identity<U>(value: U): U { return value; }".to_string(),
    ]),
  ]
}

fn tsx_statement() -> impl Strategy<Value = String> {
  prop_oneof![
    prop::sample::select(vec![
      r#"const view: JSX.Element = <div className="box">{value as number}</div>;"#.to_string(),
      r#"function Component<T>(props: {value: T}) { return <span>{props.value}</span>; }"#
        .to_string(),
      r#"export const header = <Header title={"Title" as string} />;"#.to_string(),
      r#"const list = <>{items.map(item => <Item value={item as number} />)}</>;"#.to_string(),
    ]),
    ident().prop_map(|name| format!(
      "const {name}: JSX.Element = <section>{{{name} as const}}</section>;"
    )),
  ]
}

fn join_statements(stmts: Vec<String>) -> String {
  stmts.join("\n")
}

fn js_program() -> impl Strategy<Value = ProgramCase> {
  prop::collection::vec(js_statement(), 1..6).prop_map(|stmts| ProgramCase {
    mode: TopLevelMode::Module,
    input_dialect: Dialect::Js,
    output_dialect: Dialect::Js,
    source: join_statements(stmts),
  })
}

fn jsx_program() -> impl Strategy<Value = ProgramCase> {
  prop::collection::vec(jsx_statement(), 1..6).prop_map(|stmts| ProgramCase {
    mode: TopLevelMode::Module,
    input_dialect: Dialect::Jsx,
    output_dialect: Dialect::Jsx,
    source: join_statements(stmts),
  })
}

fn ts_program() -> impl Strategy<Value = ProgramCase> {
  prop::collection::vec(ts_statement(), 1..6).prop_map(|stmts| ProgramCase {
    mode: TopLevelMode::Module,
    input_dialect: Dialect::Ts,
    output_dialect: Dialect::Js,
    source: join_statements(stmts),
  })
}

fn tsx_program() -> impl Strategy<Value = ProgramCase> {
  prop::collection::vec(tsx_statement(), 1..6).prop_map(|stmts| ProgramCase {
    mode: TopLevelMode::Module,
    input_dialect: Dialect::Tsx,
    output_dialect: Dialect::Jsx,
    source: join_statements(stmts),
  })
}

fn any_program() -> impl Strategy<Value = ProgramCase> {
  prop_oneof![js_program(), jsx_program(), ts_program(), tsx_program()]
}

proptest! {
  #![proptest_config(ProptestConfig::with_cases(64))]

  #[test]
  fn minified_programs_remain_parseable_and_deterministic(case in any_program()) {
    let mut first = Vec::new();
    let result = minify_with_options(
      MinifyOptions::new(case.mode).with_dialect(case.input_dialect),
      &case.source,
      &mut first,
    );
    prop_assert!(result.is_ok(), "minify returned diagnostics: {:?}", result.err());
    let first_output = String::from_utf8(first).expect("minifier output must be UTF-8");

    let mut second = Vec::new();
    let second_result = minify_with_options(
      MinifyOptions::new(case.mode).with_dialect(case.input_dialect),
      &case.source,
      &mut second,
    );
    prop_assert!(second_result.is_ok(), "second minify returned diagnostics: {:?}", second_result.err());
    let second_output = String::from_utf8(second).expect("minifier output must be UTF-8");

    prop_assert_eq!(first_output.as_str(), second_output.as_str());

    let parsed = parse_with_options(
      &first_output,
      ParseOptions {
        dialect: case.output_dialect,
        source_type: source_type(case.mode),
      },
    );
    prop_assert!(parsed.is_ok(), "minified output failed to parse: {:?}", parsed.err());
  }
}

proptest! {
  #![proptest_config(ProptestConfig::with_cases(64))]

  #[test]
  fn typescript_erasure_outputs_parseable_js(case in ts_program()) {
    let mut output = Vec::new();
    let result = minify_with_options(
      MinifyOptions::new(case.mode).with_dialect(case.input_dialect),
      &case.source,
      &mut output,
    );
    prop_assert!(result.is_ok(), "minify returned diagnostics: {:?}", result.err());
    let code = String::from_utf8(output).expect("minifier output must be UTF-8");
    let parsed = parse_with_options(
      &code,
      ParseOptions {
        dialect: case.output_dialect,
        source_type: source_type(case.mode),
      },
    );
    prop_assert!(parsed.is_ok(), "minified TypeScript failed to parse as JavaScript: {:?}", parsed.err());
  }
}
