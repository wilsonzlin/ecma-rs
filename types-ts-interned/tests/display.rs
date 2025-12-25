use types_ts_interned::Accessibility;
use types_ts_interned::Indexer;
use types_ts_interned::MappedModifier;
use types_ts_interned::MappedType;
use types_ts_interned::ObjectType;
use types_ts_interned::Param;
use types_ts_interned::PropData;
use types_ts_interned::PropKey;
use types_ts_interned::Property;
use types_ts_interned::Shape;
use types_ts_interned::Signature;
use types_ts_interned::TemplateChunk;
use types_ts_interned::TemplateLiteralType;
use types_ts_interned::TupleElem;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeParamId;
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
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
      types_ts_interned::Property {
        key: PropKey::String(name_a),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: true,
          accessibility: Some(Accessibility::Public),
          is_method: false,
          origin: None,
          declared_on: None,
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
        is_method: false,
        origin: None,
        declared_on: None,
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
        is_method: false,
        origin: None,
        declared_on: None,
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

#[test]
fn formats_new_type_variants() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let this_ty = store.intern_type(TypeKind::This);
  assert_eq!(format!("{}", store.display(this_ty)), "this");

  let infer_ty = store.intern_type(TypeKind::Infer(TypeParamId(3)));
  assert_eq!(format!("{}", store.display(infer_ty)), "infer T3");

  let array = store.intern_type(TypeKind::Array {
    ty: primitives.boolean,
    readonly: false,
  });
  assert_eq!(format!("{}", store.display(array)), "boolean[]");

  let ro_array = store.intern_type(TypeKind::Array {
    ty: store.union(vec![primitives.string, primitives.number]),
    readonly: true,
  });
  assert_eq!(
    format!("{}", store.display(ro_array)),
    "readonly (number | string)[]"
  );

  let tuple = store.intern_type(TypeKind::Tuple(vec![
    TupleElem {
      ty: primitives.string,
      optional: false,
      rest: false,
      readonly: false,
    },
    TupleElem {
      ty: primitives.number,
      optional: true,
      rest: false,
      readonly: false,
    },
    TupleElem {
      ty: store.intern_type(TypeKind::Array {
        ty: primitives.boolean,
        readonly: false,
      }),
      optional: false,
      rest: true,
      readonly: true,
    },
  ]));
  assert_eq!(
    format!("{}", store.display(tuple)),
    "[string, number?, ...readonly boolean[]]"
  );
}

#[test]
fn formats_mapped_type_modifiers() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let make_mapped = |readonly, optional| {
    store.intern_type(TypeKind::Mapped(MappedType {
      param: TypeParamId(0),
      source: primitives.string,
      value: primitives.number,
      readonly,
      optional,
      name_type: None,
      as_type: None,
    }))
  };

  let expected = |readonly: MappedModifier, optional: MappedModifier| {
    let readonly_prefix = match readonly {
      MappedModifier::Preserve => "",
      MappedModifier::Add => "readonly ",
      MappedModifier::Remove => "-readonly ",
    };
    let optional_suffix = match optional {
      MappedModifier::Preserve => "]: number }",
      MappedModifier::Add => "]?: number }",
      MappedModifier::Remove => "]-?: number }",
    };

    let mut out = String::from("{ ");
    out.push_str(readonly_prefix);
    out.push_str("[K in string");
    out.push_str(optional_suffix);
    out
  };

  for readonly in [
    MappedModifier::Preserve,
    MappedModifier::Add,
    MappedModifier::Remove,
  ]
  .iter()
  .cloned()
  {
    for optional in [
      MappedModifier::Preserve,
      MappedModifier::Add,
      MappedModifier::Remove,
    ]
    .iter()
    .cloned()
    {
      let mapped = make_mapped(readonly.clone(), optional.clone());
      assert_eq!(
        format!("{}", store.display(mapped)),
        expected(readonly.clone(), optional.clone())
      );
    }
  }
}

#[test]
fn formats_mapped_type_as_clause() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let mapped = store.intern_type(TypeKind::Mapped(MappedType {
    param: TypeParamId(0),
    source: primitives.string,
    value: primitives.number,
    readonly: MappedModifier::Preserve,
    optional: MappedModifier::Add,
    name_type: None,
    as_type: Some(primitives.boolean),
  }));

  assert_eq!(
    format!("{}", store.display(mapped)),
    "{ [K in string as boolean]?: number }"
  );
}

#[test]
fn formats_signature_with_this_param() {
  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let sig = store.intern_signature(Signature {
    params: vec![Param {
      name: Some(store.intern_name("value")),
      ty: primitives.number,
      optional: false,
      rest: false,
    }],
    ret: primitives.string,
    type_params: Vec::new(),
    this_param: Some(primitives.boolean),
  });

  let callable = store.intern_type(TypeKind::Callable {
    overloads: vec![sig],
  });

  assert_eq!(
    format!("{}", store.display(callable)),
    "(this: boolean, value: number) => string"
  );
}
