use types_ts_interned::{IntrinsicKind, TemplateChunk, TemplateLiteralType, TypeKind, TypeStore};

#[test]
fn uppercase_distributes_over_unions_deterministically() {
  let store = TypeStore::new();

  let a = store.intern_type(TypeKind::StringLiteral(store.intern_name("a")));
  let b = store.intern_type(TypeKind::StringLiteral(store.intern_name("b")));
  let union = store.union(vec![b, a]);

  let ty = store.intern_type(TypeKind::Intrinsic {
    kind: IntrinsicKind::Uppercase,
    ty: union,
  });
  let evaluated = store.evaluate(ty);

  let TypeKind::Union(members) = store.type_kind(evaluated) else {
    panic!("expected union, got {:?}", store.type_kind(evaluated));
  };
  assert_eq!(members.len(), 2);

  let mut strings: Vec<_> = members
    .iter()
    .map(|member| match store.type_kind(*member) {
      TypeKind::StringLiteral(id) => store.name(id),
      other => panic!("expected string literal, got {other:?}"),
    })
    .collect();
  strings.sort();
  assert_eq!(strings, vec!["A", "B"]);

  // Union members should be in canonical (stable) order.
  let mut sorted = members.clone();
  sorted.sort_by(|a, b| store.type_cmp(*a, *b));
  assert_eq!(members, sorted);
}

#[test]
fn uppercase_transforms_template_literal_parts() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let tpl = TemplateLiteralType {
    head: "foo".into(),
    spans: vec![TemplateChunk {
      ty: primitives.string,
      literal: "bar".into(),
    }],
  };
  let tpl = store.intern_type(TypeKind::TemplateLiteral(tpl));

  let ty = store.intern_type(TypeKind::Intrinsic {
    kind: IntrinsicKind::Uppercase,
    ty: tpl,
  });
  let evaluated = store.evaluate(ty);
  assert_eq!(
    store.display(evaluated).to_string(),
    "`FOO${Uppercase<string>}BAR`"
  );
}

#[test]
fn builtin_iterator_return_evaluates_to_any() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let ty = store.intern_type(TypeKind::Intrinsic {
    kind: IntrinsicKind::BuiltinIteratorReturn,
    ty: primitives.unknown,
  });
  let evaluated = store.evaluate(ty);

  assert_eq!(evaluated, primitives.any);
}
