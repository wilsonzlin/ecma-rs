use std::collections::BTreeMap;
use std::sync::Arc;

use ordered_float::OrderedFloat;
use proptest::prelude::*;
use typecheck_ts::{codes, Diagnostic, FileId, Label, Severity, Span, TextRange};
use types_ts_interned::{
  ObjectType, PropData, PropKey, Property, Shape, TupleElem, TypeDisplay, TypeId, TypeKind,
  TypeStore,
};

#[derive(Clone, Debug)]
enum SimpleType {
  Any,
  Unknown,
  Never,
  Boolean,
  Number,
  String,
  BooleanLiteral(bool),
  NumberLiteral(i64),
  StringLiteral(String),
  Array(Box<SimpleType>),
  Tuple(Vec<SimpleType>),
  Union(Vec<SimpleType>),
  Intersection(Vec<SimpleType>),
  Object(Vec<(String, SimpleType)>),
}

fn small_string() -> impl Strategy<Value = String> {
  const ALLOWED: &[u8] = b"abcdefghijklmnopqrstuvwxyz";
  prop::collection::vec(prop::sample::select(ALLOWED.to_vec()), 0..6)
    .prop_map(|bytes| String::from_utf8(bytes).unwrap())
}

fn span_strategy() -> impl Strategy<Value = Span> {
  (0u32..4, 0u32..64, 0u32..64).prop_map(|(file, start, len)| {
    let end = start.saturating_add(len);
    Span::new(FileId(file), TextRange::new(start, end))
  })
}

fn label_strategy() -> impl Strategy<Value = Label> {
  (span_strategy(), small_string(), any::<bool>()).prop_map(|(span, message, is_primary)| Label {
    span,
    message,
    is_primary,
  })
}

fn primary_label_strategy() -> impl Strategy<Value = Label> {
  (span_strategy(), small_string()).prop_map(|(span, message)| Label {
    span,
    message,
    is_primary: true,
  })
}

fn diagnostic_strategy() -> impl Strategy<Value = Diagnostic> {
  (
    small_string(),
    small_string(),
    span_strategy(),
    primary_label_strategy(),
    prop::collection::vec(label_strategy(), 0..4),
    prop::collection::vec(small_string(), 0..4),
    prop_oneof![
      Just(Severity::Error),
      Just(Severity::Warning),
      Just(Severity::Note),
      Just(Severity::Help)
    ],
  )
    .prop_map(
      |(code, message, primary_span, primary_label, mut labels, notes, severity)| {
        labels.push(primary_label);
        Diagnostic {
          code: code.into(),
          severity,
          message,
          primary: primary_span,
          labels,
          notes,
        }
      },
    )
}

fn simple_type_strategy() -> impl Strategy<Value = SimpleType> {
  let leaf = prop_oneof![
    Just(SimpleType::Any),
    Just(SimpleType::Unknown),
    Just(SimpleType::Never),
    Just(SimpleType::Boolean),
    Just(SimpleType::Number),
    Just(SimpleType::String),
    any::<bool>().prop_map(SimpleType::BooleanLiteral),
    (-5i64..5).prop_map(SimpleType::NumberLiteral),
    small_string().prop_map(SimpleType::StringLiteral),
  ];

  leaf.prop_recursive(3, 32, 4, |inner| {
    prop_oneof![
      inner.clone().prop_map(|ty| SimpleType::Array(Box::new(ty))),
      prop::collection::vec(inner.clone(), 0..4).prop_map(SimpleType::Tuple),
      prop::collection::vec(inner.clone(), 1..4).prop_map(SimpleType::Union),
      prop::collection::vec(inner.clone(), 1..4).prop_map(SimpleType::Intersection),
      prop::collection::btree_map(small_string(), inner, 0..4).prop_map(|map: BTreeMap<_, _>| {
        let mut props: Vec<_> = map.into_iter().collect();
        props.reverse();
        SimpleType::Object(props)
      }),
    ]
  })
}

fn build_type(desc: &SimpleType, store: &Arc<TypeStore>) -> TypeId {
  match desc {
    SimpleType::Any => store.primitive_ids().any,
    SimpleType::Unknown => store.primitive_ids().unknown,
    SimpleType::Never => store.primitive_ids().never,
    SimpleType::Boolean => store.primitive_ids().boolean,
    SimpleType::Number => store.primitive_ids().number,
    SimpleType::String => store.primitive_ids().string,
    SimpleType::BooleanLiteral(value) => store.intern_type(TypeKind::BooleanLiteral(*value)),
    SimpleType::NumberLiteral(value) => {
      store.intern_type(TypeKind::NumberLiteral(OrderedFloat::from(*value as f64)))
    }
    SimpleType::StringLiteral(value) => {
      let name = store.intern_name(value);
      store.intern_type(TypeKind::StringLiteral(name))
    }
    SimpleType::Array(inner) => store.intern_type(TypeKind::Array {
      ty: build_type(inner, store),
      readonly: false,
    }),
    SimpleType::Tuple(items) => {
      let elems: Vec<_> = items
        .iter()
        .map(|item| TupleElem {
          ty: build_type(item, store),
          optional: false,
          rest: false,
          readonly: false,
        })
        .collect();
      store.intern_type(TypeKind::Tuple(elems))
    }
    SimpleType::Union(members) => {
      let members: Vec<_> = members.iter().map(|m| build_type(m, store)).collect();
      store.union(members)
    }
    SimpleType::Intersection(members) => {
      let members: Vec<_> = members.iter().map(|m| build_type(m, store)).collect();
      store.intersection(members)
    }
    SimpleType::Object(props) => {
      let mut shape = Shape::new();
      for (name, ty) in props.iter() {
        shape.properties.push(Property {
          key: PropKey::String(store.intern_name(name)),
          data: PropData {
            ty: build_type(ty, store),
            optional: false,
            readonly: false,
            accessibility: None,
            is_method: false,
            origin: None,
            declared_on: None,
          },
        });
      }
      let shape_id = store.intern_shape(shape);
      let obj_id = store.intern_object(ObjectType { shape: shape_id });
      store.intern_type(TypeKind::Object(obj_id))
    }
  }
}

proptest! {
  #![proptest_config(ProptestConfig::with_cases(64))]

  #[test]
  fn diagnostic_normalization_is_idempotent(diags in prop::collection::vec(diagnostic_strategy(), 0..16)) {
    let mut normalized = diags.clone();
    codes::normalize_diagnostics(&mut normalized);

    let mut normalized_twice = normalized.clone();
    codes::normalize_diagnostics(&mut normalized_twice);

    prop_assert_eq!(normalized, normalized_twice);
  }

  #[test]
  fn type_display_is_deterministic(desc in simple_type_strategy()) {
    let store_a = TypeStore::new();
    let ty_a = build_type(&desc, &store_a);
    let rendered_a = TypeDisplay::new(&store_a, ty_a).to_string();

    let store_b = TypeStore::new();
    let ty_b = build_type(&desc, &store_b);
    let rendered_b = TypeDisplay::new(&store_b, ty_b).to_string();

    prop_assert_eq!(rendered_a, rendered_b);
  }

  #[test]
  fn canonicalization_is_idempotent(desc in simple_type_strategy()) {
    let store = TypeStore::new();
    let ty = build_type(&desc, &store);

    let canon = store.canon(ty);
    let canon_again = store.canon(canon);

    prop_assert_eq!(canon, canon_again);
  }
}
