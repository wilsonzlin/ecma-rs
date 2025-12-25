use optimize_js::decompile::NameMangler;

#[test]
fn avoids_unknown_and_reserved_collisions() {
  // Reserve names that might come from UnknownLoad/UnknownStore or builtins.
  let mut minified = NameMangler::new(vec!["a".to_string()]);
  minified.minify_locals = true;
  assert_eq!(minified.name_for_reg(0), "b");
  assert_eq!(minified.name_for_reg(1), "c");

  // Canonical names should also avoid collisions.
  let mut canonical = NameMangler::new(vec!["r0".to_string()]);
  assert_eq!(canonical.name_for_reg(0), "r0_1");
}

#[test]
fn avoids_keyword_collisions() {
  let mut mangler = NameMangler::new(Vec::new());
  let kw1 = mangler.fresh("for");
  assert_ne!(kw1, "for");
  assert!(kw1.starts_with("for"));

  let kw2 = mangler.fresh("await");
  assert_ne!(kw2, "await");
  assert!(kw2.starts_with("await"));
}

#[test]
fn deterministic_across_runs() {
  let mut first = NameMangler::new(vec!["taken".to_string()]);
  first.minify_locals = true;
  let mut second = NameMangler::new(vec!["taken".to_string()]);
  second.minify_locals = true;

  let seq1 = vec![
    first.name_for_reg(0),
    first.name_for_foreign(0),
    first.fresh("tmp"),
    first.name_for_reg(1),
    first.name_for_foreign(1),
  ];
  let seq2 = vec![
    second.name_for_reg(0),
    second.name_for_foreign(0),
    second.fresh("tmp"),
    second.name_for_reg(1),
    second.name_for_foreign(1),
  ];

  assert_eq!(seq1, seq2);
  // Stable on repeat.
  assert_eq!(first.name_for_reg(0), seq1[0]);
  assert_eq!(second.name_for_foreign(1), seq2[4]);

  // Deterministic regardless of call order when using index-based encoding.
  let mut reversed = NameMangler::new(vec!["taken".to_string()]);
  reversed.minify_locals = true;
  let mut reversed_seq = vec![
    reversed.name_for_reg(1),
    reversed.name_for_reg(0),
    reversed.name_for_foreign(1),
    reversed.name_for_foreign(0),
  ];
  // Reconstruct with canonical ordering for comparison.
  reversed_seq.swap(0, 1);
  reversed_seq.swap(2, 3);
  assert_eq!(
    reversed_seq,
    vec![
      seq1[0].clone(),
      seq1[3].clone(),
      seq1[4].clone(),
      seq1[1].clone()
    ]
  );
}
