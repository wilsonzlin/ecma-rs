use parse_js;

#[test]
fn export_assignment_allows_asi_at_end_of_file() {
  let sources = [
    "export = {}",
    "export = {}\n",
    "export = {}\nconst value = 1;",
  ];

  for source in sources {
    let parsed = parse_js::parse(source);
    assert!(parsed.is_ok(), "failed to parse {source:?}: {parsed:?}");
  }
}
