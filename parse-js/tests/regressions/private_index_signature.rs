use parse_js;

#[test]
fn parses_private_index_signature_in_object_literal_for_recovery() {
  let sources = [
    "var x = { private [key: string]: string; };",
    "var y = { [key: string]: number };",
  ];

  for source in sources {
    let parsed = parse_js::parse(source);
    assert!(parsed.is_ok(), "failed to parse {source:?}: {parsed:?}");
  }
}
