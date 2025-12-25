use parse_js;

#[test]
fn allows_destructuring_parameters_in_type_signatures() {
  let sources = [
    "interface F { f([, a, b], {p, m: { q, r}}); }",
    "type Fn = ({x}: { x: number }) => void;",
    "type G = (...[a, b]: [number, string]) => void;",
  ];

  for source in sources {
    let parsed = parse_js::parse(source);
    assert!(parsed.is_ok(), "failed to parse {source:?}: {parsed:?}");
  }
}
