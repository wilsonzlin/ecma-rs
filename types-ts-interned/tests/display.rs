use types_ts_interned::Accessibility;
use types_ts_interned::Indexer;
use types_ts_interned::ObjectType;
use types_ts_interned::PropData;
use types_ts_interned::PropKey;
use types_ts_interned::Property;
use types_ts_interned::Shape;
use types_ts_interned::Signature;
use types_ts_interned::TemplateChunk;
use types_ts_interned::TemplateLiteralType;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeStore;

fn make_object_type(store: &TypeStore) -> (types_ts_interned::TypeId, Shape) {
  let primitives = store.primitive_ids();
  let name_a = store.intern_name("a");
  let name_b = store.intern_name("b");
  let shape = Shape {
    properties: vec![
      types_ts_interned::Property {
        key: PropKey::String(name_b),
        data: PropData {
          ty: primitives.number,
          optional: true,
          readonly: false,
          accessibility: None,
        },
      },
      types_ts_interned::Property {
        key: PropKey::String(name_a),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: true,
          accessibility: Some(Accessibility::Public),
        },
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: vec![Indexer {
      key_type: primitives.string,
      value_type: primitives.number,
      readonly: false,
    }],
  };

  let shape_id = store.intern_shape(shape.clone());
  let obj = store.intern_object(ObjectType { shape: shape_id });
  let type_id = store.intern_type(TypeKind::Object(obj));
  (type_id, shape)
}

#[test]
fn formats_complex_object_shape() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let (object_ty, _shape) = make_object_type(&store);

  let call_sig = store.intern_signature(Signature::new(
    vec![types_ts_interned::Param {
      name: Some(store.intern_name("arg")),
      ty: primitives.boolean,
      optional: false,
      rest: false,
    }],
    primitives.symbol,
  ));

  let mut shape = store.shape(
    store
      .object(match store.type_kind(object_ty) {
        TypeKind::Object(id) => id,
        _ => unreachable!(),
      })
      .shape,
  );
  shape.call_signatures.push(call_sig);
  let shape_id = store.intern_shape(shape);
  let object_ty = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  let formatted = format!("{}", store.display(object_ty));
  assert_eq!(
    formatted,
    "{ public readonly a: string; b?: number; [string]: number; (arg: boolean) => symbol }",
  );
}

#[test]
fn formats_nested_combinations() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let (object_ty, _) = make_object_type(&store);

  let template = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "foo".into(),
    spans: vec![TemplateChunk {
      literal: "bar".into(),
      ty: primitives.string,
    }],
  }));

  let keyof_obj = store.intern_type(TypeKind::KeyOf(object_ty));
  let intersection = store.intersection(vec![keyof_obj, template]);
  let indexed = store.intern_type(TypeKind::IndexedAccess {
    obj: object_ty,
    index: keyof_obj,
  });
  let true_lit = store.intern_type(TypeKind::BooleanLiteral(true));
  let union = store.union(vec![intersection, indexed, true_lit]);

  let formatted = format!("{}", store.display(union));
  assert_eq!(
    formatted,
    "true | `foo${string}bar` & keyof { public readonly a: string; b?: number; [string]: number } | { public readonly a: string; b?: number; [string]: number }[keyof { public readonly a: string; b?: number; [string]: number }]",
  );
}

#[test]
fn escapes_string_literals_and_property_keys() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let name = store.intern_name("line\"one\"\nline\\two");

  let shape_id = store.intern_shape(Shape {
    properties: vec![Property {
      key: PropKey::String(name),
      data: PropData {
        ty: primitives.string,
        optional: false,
        readonly: false,
        accessibility: None,
      },
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let obj = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  assert_eq!(
    format!("{}", store.display(obj)),
    "{ \"line\\\"one\\\"\\nline\\\\two\": string }"
  );

  let str_lit = store.intern_type(TypeKind::StringLiteral(name));
  assert_eq!(
    format!("{}", store.display(str_lit)),
    "\"line\\\"one\\\"\\nline\\\\two\""
  );
}

#[test]
fn escapes_template_literal_chunks() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let tpl = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
    head: "start`".into(),
    spans: vec![TemplateChunk {
      literal: "`and ${finish}".into(),
      ty: primitives.number,
    }],
  }));

  let formatted = format!("{}", store.display(tpl));
  assert_eq!(formatted, "`start\\`${number}\\`and \\${finish}`");
}

#[test]
fn formats_unicode_identifier_property() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();
  let pi = store.intern_name("π");

  let shape_id = store.intern_shape(Shape {
    properties: vec![Property {
      key: PropKey::String(pi),
      data: PropData {
        ty: primitives.number,
        optional: false,
        readonly: false,
        accessibility: None,
      },
    }],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  });
  let obj = store.intern_type(TypeKind::Object(
    store.intern_object(ObjectType { shape: shape_id }),
  ));

  assert_eq!(format!("{}", store.display(obj)), "{ π: number }");
}
