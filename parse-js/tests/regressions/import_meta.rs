use parse_js;

#[test]
fn import_meta_statement_parses_as_expression() {
  let sources = [
    "import.meta.url;",
    "import.meta;",
    "if (true) { import.meta.foo; }",
  ];

  for source in sources {
    let parsed = parse_js::parse(source);
    assert!(parsed.is_ok(), "failed to parse {source:?}: {parsed:?}");
  }
}

#[test]
fn import_meta_can_be_an_assignment_target_for_recovery() {
  let sources = [
    "import.meta = value;",
    "import.meta.foo = import.meta;",
    "export const ref = (import.meta = other);",
  ];

  for source in sources {
    let parsed = parse_js::parse(source);
    assert!(parsed.is_ok(), "failed to parse {source:?}: {parsed:?}");
  }
}
