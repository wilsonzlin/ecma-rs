use std::collections::HashMap;
use std::sync::Arc;

use ordered_float::OrderedFloat;
use types_ts_interned::{
  DefId, ExpandedType, Indexer, MappedModifier, MappedType, ObjectType, PropData, PropKey, Property,
  Shape, TemplateChunk, TemplateLiteralType, TypeEvaluator, TypeExpander, TypeId, TypeKind,
  TypeParamId, TypeStore,
};

#[derive(Default)]
struct MockExpander {
  defs: HashMap<DefId, ExpandedType>,
}

impl MockExpander {
  fn insert(&mut self, def: DefId, expanded: ExpandedType) {
    self.defs.insert(def, expanded);
  }
}

impl TypeExpander for MockExpander {
  fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
    self.defs.get(&def).cloned()
  }
}

fn evaluator(store: Arc<TypeStore>, expander: &MockExpander) -> TypeEvaluator<'_, MockExpander> {
  TypeEvaluator::new(store, expander)
}

#[test]
fn conditional_distributes_over_union_with_substitution() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let cond = store.intern_type(TypeKind::Conditional {
    check: store.intern_type(TypeKind::TypeParam(TypeParamId(0))),
    extends: primitives.string,
    true_ty: primitives.number,
    false_ty: primitives.boolean,
    distributive: true,
  });

  let mut expander = MockExpander::default();
  expander.insert(
    DefId(0),
    ExpandedType {
      params: vec![TypeParamId(0)],
      ty: cond,
    },
  );

  let arg_union = store.union(vec![
    store.intern_type(TypeKind::StringLiteral(store.intern_name("ok"))),
    store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(1.0))),
  ]);
  let ref_ty = store.intern_type(TypeKind::Ref {
    def: DefId(0),
    args: vec![arg_union],
  });

  let mut eval = evaluator(store.clone(), &expander);
  let result = eval.evaluate(ref_ty);
  let TypeKind::Union(members) = store.type_kind(result) else {
    panic!("expected union, got {:?}", store.type_kind(result));
  };
  assert!(members.contains(&primitives.number));
  assert!(members.contains(&primitives.boolean));
  assert_eq!(members.len(), 2);
}

#[test]
fn mapped_type_applies_modifiers_and_remaps() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");
  let shape_id = store.intern_shape(Shape {
    properties: vec![
      Property {
        key: PropKey::String(name_a),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
      Property {
        key: PropKey::String(name_b),
        data: PropData {
          ty: primitives.number,
          optional: true,
          readonly: true,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let obj_ty = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let mapped = store.intern_type(TypeKind::Mapped(MappedType {
    param: TypeParamId(0),
    source: store.intern_type(TypeKind::KeyOf(obj_ty)),
    value: primitives.boolean,
    readonly: MappedModifier::Add,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: Some(
      store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
        head: "".into(),
        spans: vec![TemplateChunk {
          literal: "_done".into(),
          ty: store.intern_type(TypeKind::TypeParam(TypeParamId(0))),
        }],
      })),
    ),
  }));

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);
  let result = eval.evaluate(mapped);
  let TypeKind::Object(obj) = store.type_kind(result) else {
    panic!("expected object, got {:?}", store.type_kind(result));
  };
  let shape = store.shape(store.object(obj).shape);
  assert_eq!(shape.properties.len(), 2);

  let mut names: Vec<_> = shape
    .properties
    .iter()
    .map(|p| match p.key {
      PropKey::String(id) => store.name(id),
      _ => panic!("unexpected key {:?}", p.key),
    })
    .collect();
  names.sort();
  assert_eq!(names, vec!["a_done".to_string(), "b_done".to_string()]);

  for prop in shape.properties.iter() {
    assert!(prop.data.readonly);
    assert_eq!(prop.data.ty, primitives.boolean);
    if let PropKey::String(id) = prop.key {
      if store.name(id) == "b_done" {
        assert!(prop.data.optional);
      } else {
        assert!(!prop.data.optional);
      }
    }
  }
}

#[test]
fn template_literal_distributes_over_union_parts() {
  let store = TypeStore::new();

  let tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "foo".into(),
    spans: vec![TemplateChunk {
      literal: "bar".into(),
      ty: store.union(vec![
        store.intern_type(TypeKind::StringLiteral(store.intern_name("x"))),
        store.intern_type(TypeKind::StringLiteral(store.intern_name("y"))),
      ]),
    }],
  }));

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander).with_max_template_strings(2);
  let result = eval.evaluate(tpl);
  let TypeKind::Union(members) = store.type_kind(result) else {
    panic!("expected union, got {:?}", store.type_kind(result));
  };
  let strings: Vec<_> = members
    .iter()
    .map(|m| match store.type_kind(*m) {
      TypeKind::StringLiteral(id) => store.name(id),
      other => panic!("unexpected member {:?}", other),
    })
    .collect();
  assert!(strings.contains(&"fooxbar".to_string()));
  assert!(strings.contains(&"fooybar".to_string()));
  assert_eq!(strings.len(), 2);
}

#[test]
fn template_literal_expansion_bails_out_on_blowup() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let union1 = store.union(vec![
    store.intern_type(TypeKind::StringLiteral(store.intern_name("a"))),
    store.intern_type(TypeKind::StringLiteral(store.intern_name("b"))),
    store.intern_type(TypeKind::StringLiteral(store.intern_name("c"))),
  ]);
  let union2 = store.union(vec![
    store.intern_type(TypeKind::StringLiteral(store.intern_name("x"))),
    store.intern_type(TypeKind::StringLiteral(store.intern_name("y"))),
    store.intern_type(TypeKind::StringLiteral(store.intern_name("z"))),
  ]);

  // 3×3 = 9 possible strings; with a low limit, we should bail out and widen to
  // `string` rather than enumerating the full cross-product.
  let tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "".into(),
    spans: vec![
      TemplateChunk {
        literal: "".into(),
        ty: union1,
      },
      TemplateChunk {
        literal: "".into(),
        ty: union2,
      },
    ],
  }));

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander).with_max_template_strings(4);
  let result = eval.evaluate(tpl);
  assert_eq!(result, primitives.string);
}

#[test]
fn indexed_access_collects_optional_properties() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");
  let shape_id = store.intern_shape(Shape {
    properties: vec![
      Property {
        key: PropKey::String(name_a),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
      Property {
        key: PropKey::String(name_b),
        data: PropData {
          ty: primitives.number,
          optional: true,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let obj_ty = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let index_ty = store.union(vec![
    store.intern_type(TypeKind::StringLiteral(name_a)),
    store.intern_type(TypeKind::StringLiteral(name_b)),
  ]);
  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: obj_ty,
    index: index_ty,
  });

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);
  let result = eval.evaluate(indexed);
  let TypeKind::Union(members) = store.type_kind(result) else {
    panic!("expected union, got {:?}", store.type_kind(result));
  };
  assert!(members.contains(&primitives.string));
  assert!(members.contains(&primitives.number));
  assert!(members.contains(&primitives.undefined));
}

#[test]
fn indexed_access_over_union_collects_member_properties() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");

  let shape1 = store.intern_shape(Shape {
    properties: vec![Property {
      key: PropKey::String(name_a),
      data: PropData {
        ty: primitives.string,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let shape2 = store.intern_shape(Shape {
    properties: vec![Property {
      key: PropKey::String(name_b),
      data: PropData {
        ty: primitives.number,
        optional: false,
        readonly: false,
        accessibility: None,
        is_method: false,
        origin: None,
        declared_on: None,
      },
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });

  let union_obj = store.union(vec![
    store.intern_type(TypeKind::Object(
      store.intern_object(ObjectType { shape: shape1 }),
    )),
    store.intern_type(TypeKind::Object(
      store.intern_object(ObjectType { shape: shape2 }),
    )),
  ]);
  let index = store.intern_type(TypeKind::KeyOf(union_obj));
  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: union_obj,
    index,
  });

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);
  let result = eval.evaluate(indexed);
  let TypeKind::Union(members) = store.type_kind(result) else {
    panic!("expected union, got {:?}", store.type_kind(result));
  };
  assert!(members.contains(&primitives.string));
  assert!(members.contains(&primitives.number));
  assert_eq!(members.len(), 2);
}

#[test]
fn keyof_respects_union_and_intersection_semantics() {
  let store = TypeStore::new();

  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");
  let name_c = store.intern_name("c");

  let shape1 = store.intern_shape(Shape {
    properties: vec![
      Property {
        key: PropKey::String(name_a),
        data: PropData {
          ty: store.primitive_ids().string,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
      Property {
        key: PropKey::String(name_b),
        data: PropData {
          ty: store.primitive_ids().number,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let shape2 = store.intern_shape(Shape {
    properties: vec![
      Property {
        key: PropKey::String(name_b),
        data: PropData {
          ty: store.primitive_ids().boolean,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
      Property {
        key: PropKey::String(name_c),
        data: PropData {
          ty: store.primitive_ids().boolean,
          optional: false,
          readonly: false,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });

  let obj1 = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape1 }),
  ));
  let obj2 = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape2 }),
  ));

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);

  let union_keys = eval.evaluate(store.intern_type(TypeKind::KeyOf(store.union(vec![obj1, obj2]))));
  let union_kind = store.type_kind(union_keys);
  let mut union_names: Vec<String> = match union_kind {
    TypeKind::Union(members) => members
      .iter()
      .map(|m| match store.type_kind(*m) {
        TypeKind::StringLiteral(id) => store.name(id),
        other => panic!("unexpected {:?}", other),
      })
      .collect(),
    TypeKind::StringLiteral(id) => vec![store.name(id)],
    other => panic!("unexpected {:?}", other),
  };
  union_names.sort();
  assert_eq!(
    union_names,
    vec!["a".to_string(), "b".to_string(), "c".to_string()]
  );

  let inter_keys =
    eval.evaluate(store.intern_type(TypeKind::KeyOf(store.intersection(vec![obj1, obj2]))));
  let TypeKind::Union(inter_members) = store.type_kind(inter_keys) else {
    panic!("expected union");
  };
  let mut names: Vec<_> = inter_members
    .iter()
    .map(|m| match store.type_kind(*m) {
      TypeKind::StringLiteral(id) => store.name(id),
      other => panic!("unexpected {:?}", other),
    })
    .collect();
  names.sort();
  assert_eq!(
    names,
    vec!["a".to_string(), "b".to_string(), "c".to_string()]
  );
}

#[test]
fn recursive_conditional_terminates() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let self_ref = store.intern_type(TypeKind::Ref {
    def: DefId(0),
    args: vec![store.intern_type(TypeKind::TypeParam(TypeParamId(0)))],
  });
  let cond = store.intern_type(TypeKind::Conditional {
    check: store.intern_type(TypeKind::TypeParam(TypeParamId(0))),
    extends: primitives.string,
    true_ty: self_ref,
    false_ty: primitives.boolean,
    distributive: false,
  });

  let mut expander = MockExpander::default();
  expander.insert(
    DefId(0),
    ExpandedType {
      params: vec![TypeParamId(0)],
      ty: cond,
    },
  );

  let arg = store.intern_type(TypeKind::StringLiteral(store.intern_name("loop")));
  let ref_ty = store.intern_type(TypeKind::Ref {
    def: DefId(0),
    args: vec![arg],
  });

  let mut eval = evaluator(store.clone(), &expander).with_depth_limit(32);
  let result = eval.evaluate(ref_ty);

  // The evaluator should break the cycle and return a stable type without
  // overflowing the stack.
  assert!(matches!(
    store.type_kind(result),
    TypeKind::Ref { .. } | TypeKind::Boolean | TypeKind::Union(_)
  ));
}

#[test]
fn keyof_includes_symbol_index_signature() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let shape_id = store.intern_shape(Shape {
    properties: Vec::new(),
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: vec![Indexer {
      key_type: primitives.symbol,
      value_type: primitives.string,
      readonly: false,
    }],
  });
  let obj_ty = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);
  let result = eval.evaluate(store.intern_type(TypeKind::KeyOf(obj_ty)));
  assert_eq!(result, primitives.symbol);
}

#[test]
fn indexed_access_uses_symbol_indexer_value_type() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let shape_id = store.intern_shape(Shape {
    properties: Vec::new(),
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: vec![Indexer {
      key_type: primitives.symbol,
      value_type: primitives.string,
      readonly: false,
    }],
  });
  let obj_ty = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: obj_ty,
    index: primitives.symbol,
  });

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);
  let result = eval.evaluate(indexed);
  assert_eq!(result, primitives.string);
}

#[test]
fn mapped_type_preserves_symbol_indexer() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let shape_id = store.intern_shape(Shape {
    properties: Vec::new(),
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: vec![Indexer {
      key_type: primitives.symbol,
      value_type: primitives.string,
      readonly: true,
    }],
  });
  let obj_ty = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let mapped = store.intern_type(TypeKind::Mapped(MappedType {
    param: TypeParamId(0),
    source: store.intern_type(TypeKind::KeyOf(obj_ty)),
    value: primitives.boolean,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Preserve,
    name_type: None,
    as_type: None,
  }));

  let default_expander = MockExpander::default();
  let mut eval = evaluator(store.clone(), &default_expander);
  let result = eval.evaluate(mapped);
  let TypeKind::Object(obj) = store.type_kind(result) else {
    panic!("expected object, got {:?}", store.type_kind(result));
  };
  let shape = store.shape(store.object(obj).shape);
  assert!(shape.properties.is_empty());
  assert_eq!(shape.indexers.len(), 1);
  assert_eq!(shape.indexers[0].key_type, primitives.symbol);
  assert_eq!(shape.indexers[0].value_type, primitives.boolean);
  assert!(shape.indexers[0].readonly);
}
