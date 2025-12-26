use std::collections::HashMap;
use std::sync::Arc;

use typecheck_ts::{FileId, Host, HostError, Program, PropertyKey, TypeKindSummary, TypeQueries};
use types_ts_interned::{
  DefId, ExpandedType, Indexer, ObjectType, Param, PropData, PropKey, Property, Shape, Signature,
  TypeExpander, TypeId, TypeKind, TypeStore,
};

#[derive(Debug)]
struct NoopExpander;

impl TypeExpander for NoopExpander {
  fn expand(
    &self,
    _store: &TypeStore,
    _def: types_ts_interned::DefId,
    _args: &[TypeId],
  ) -> Option<ExpandedType> {
    None
  }
}

fn object_type(store: &Arc<TypeStore>, shape: Shape) -> TypeId {
  let shape_id = store.intern_shape(shape);
  let obj_id = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj_id))
}

#[derive(Default)]
struct TestHost {
  files: HashMap<FileId, Arc<str>>,
  resolutions: HashMap<String, FileId>,
}

impl TestHost {
  fn insert(&mut self, file: FileId, src: &str) {
    self.files.insert(file, Arc::from(src.to_string()));
  }

  fn resolve_to(&mut self, specifier: &str, target: FileId) {
    self.resolutions.insert(specifier.to_string(), target);
  }
}

impl Host for TestHost {
  fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
    self
      .files
      .get(&file)
      .cloned()
      .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
  }

  fn resolve(&self, _from: FileId, specifier: &str) -> Option<FileId> {
    self.resolutions.get(specifier).copied()
  }
}

#[test]
fn object_properties_include_modifiers() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let shape = Shape {
    properties: vec![
      Property {
        key: PropKey::String(store.intern_name("a")),
        data: PropData {
          ty: prim.number,
          optional: false,
          readonly: true,
          accessibility: None,
          is_method: false,
          origin: None,
          declared_on: None,
        },
      },
      Property {
        key: PropKey::String(store.intern_name("maybe")),
        data: PropData {
          ty: prim.string,
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
  };
  let ty = object_type(&store, shape);
  let expander = NoopExpander;
  let queries = TypeQueries::new(Arc::clone(&store), &expander);
  let mut props = queries.properties_of(ty);
  props.sort_by_key(|p| match &p.key {
    PropertyKey::String(name) => name.clone(),
    _ => String::new(),
  });
  assert_eq!(props.len(), 2);

  let a = props
    .iter()
    .find(|p| p.key == PropertyKey::String("a".into()))
    .unwrap();
  assert!(!a.optional, "required property should not be optional");
  assert!(a.readonly, "readonly flag should be preserved");
  assert!(matches!(store.type_kind(a.ty), TypeKind::Number));

  let maybe = props
    .iter()
    .find(|p| p.key == PropertyKey::String("maybe".into()))
    .unwrap();
  assert!(maybe.optional, "optional property should be marked");
  match store.type_kind(maybe.ty) {
    TypeKind::Union(members) => {
      assert!(members.contains(&prim.string));
      assert!(members.contains(&prim.undefined));
    }
    other => panic!("expected union for optional property, got {other:?}"),
  }
}

#[test]
fn property_lookup_through_unions_and_intersections() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let required = object_type(
    &store,
    Shape {
      properties: vec![Property {
        key: PropKey::String(store.intern_name("value")),
        data: PropData {
          ty: prim.number,
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
    },
  );
  let optional = object_type(
    &store,
    Shape {
      properties: vec![Property {
        key: PropKey::String(store.intern_name("value")),
        data: PropData {
          ty: prim.number,
          optional: true,
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
    },
  );

  let expander = NoopExpander;
  let queries = TypeQueries::new(Arc::clone(&store), &expander);

  let union_ty = store.union(vec![required, optional]);
  let union_prop = queries
    .property_type(union_ty, PropertyKey::String("value".into()))
    .expect("property present on union");
  match store.type_kind(union_prop) {
    TypeKind::Union(members) => {
      assert!(members.contains(&prim.number));
      assert!(members.contains(&prim.undefined));
    }
    other => panic!("expected union with undefined, got {other:?}"),
  }
  let union_props = queries.properties_of(union_ty);
  assert!(
    union_props.iter().any(|p| p.optional),
    "union should expose optional flag when any member is optional"
  );

  let intersection_ty = store.intersection(vec![required, optional]);
  let intersection_prop = queries
    .property_type(intersection_ty, PropertyKey::String("value".into()))
    .expect("property present on intersection");
  assert!(
    matches!(store.type_kind(intersection_prop), TypeKind::Number),
    "intersection should keep base property type without undefined"
  );
  let intersection_props = queries.properties_of(intersection_ty);
  assert!(
    intersection_props.iter().all(|p| !p.optional),
    "intersection should require the property if any member does"
  );
}

#[test]
fn call_signatures_are_sorted() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let sig_string = store.intern_signature(Signature {
    params: vec![Param {
      name: None,
      ty: prim.string,
      optional: false,
      rest: false,
    }],
    ret: prim.string,
    type_params: Vec::new(),
    this_param: None,
  });
  let sig_number = store.intern_signature(Signature {
    params: vec![Param {
      name: None,
      ty: prim.number,
      optional: false,
      rest: false,
    }],
    ret: prim.number,
    type_params: Vec::new(),
    this_param: None,
  });

  let callable_a = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_string],
  });
  let callable_b = store.intern_type(TypeKind::Callable {
    overloads: vec![sig_number],
  });
  let combined = store.intersection(vec![callable_a, callable_b]);
  let expander = NoopExpander;
  let queries = TypeQueries::new(Arc::clone(&store), &expander);
  let sigs = queries.call_signatures(combined);
  assert_eq!(sigs.len(), 2);
  assert_eq!(
    sigs[0].signature.params[0].ty, prim.number,
    "number overload should sort before string overload"
  );
  assert_eq!(sigs[1].signature.params[0].ty, prim.string);
}

#[test]
fn index_signatures_are_exposed() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();
  let shape = Shape {
    properties: Vec::new(),
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: vec![
      Indexer {
        key_type: prim.string,
        value_type: prim.number,
        readonly: false,
      },
      Indexer {
        key_type: prim.number,
        value_type: prim.string,
        readonly: true,
      },
    ],
  };
  let ty = object_type(&store, shape);
  let expander = NoopExpander;
  let queries = TypeQueries::new(Arc::clone(&store), &expander);
  let mut indexers = queries.indexers(ty);
  assert_eq!(indexers.len(), 2);
  indexers.sort_by_key(|i| i.readonly);

  let string_idx = indexers
    .iter()
    .find(|i| matches!(store.type_kind(i.key_type), TypeKind::String))
    .expect("string indexer present");
  assert_eq!(string_idx.value_type, prim.number);
  assert!(!string_idx.readonly);

  let number_idx = indexers
    .iter()
    .find(|i| matches!(store.type_kind(i.key_type), TypeKind::Number))
    .expect("number indexer present");
  assert_eq!(number_idx.value_type, prim.string);
  assert!(number_idx.readonly);

  let prop_via_indexer = queries
    .property_type(ty, PropertyKey::String("dynamic".into()))
    .expect("string indexer should expose property types");
  assert_eq!(prop_via_indexer, prim.number);
}

#[test]
fn reference_types_expand_before_querying() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let shape = Shape {
    properties: vec![Property {
      key: PropKey::String(store.intern_name("value")),
      data: PropData {
        ty: prim.number,
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
  };
  let aliased = object_type(&store, shape);
  let def = DefId(1);
  let reference = store.intern_type(TypeKind::Ref {
    def,
    args: Vec::new(),
  });

  #[derive(Default)]
  struct MapExpander {
    map: HashMap<DefId, TypeId>,
  }

  impl TypeExpander for MapExpander {
    fn expand(&self, _store: &TypeStore, def: DefId, _args: &[TypeId]) -> Option<ExpandedType> {
      self.map.get(&def).copied().map(|ty| ExpandedType {
        params: Vec::new(),
        ty,
      })
    }
  }

  let expander = MapExpander {
    map: HashMap::from([(def, aliased)]),
  };
  let queries = TypeQueries::new(Arc::clone(&store), &expander);
  let prop = queries
    .property_type(reference, PropertyKey::String("value".into()))
    .expect("expanded ref exposes properties");
  assert_eq!(prop, prim.number);
}

#[test]
fn index_signatures_are_sorted_by_key() {
  let store = TypeStore::new();
  let prim = store.primitive_ids();

  let number_index = Indexer {
    key_type: prim.number,
    value_type: prim.number,
    readonly: false,
  };
  let string_index = Indexer {
    key_type: prim.string,
    value_type: prim.string,
    readonly: false,
  };

  let number_only = object_type(
    &store,
    Shape {
      properties: Vec::new(),
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      indexers: vec![number_index],
    },
  );
  let string_only = object_type(
    &store,
    Shape {
      properties: Vec::new(),
      call_signatures: Vec::new(),
      construct_signatures: Vec::new(),
      indexers: vec![string_index],
    },
  );

  let intersection = store.intersection(vec![number_only, string_only]);
  let expander = NoopExpander;
  let queries = TypeQueries::new(Arc::clone(&store), &expander);
  let indexers = queries.indexers(intersection);

  assert_eq!(indexers.len(), 2);
  assert!(
    matches!(store.type_kind(indexers[0].key_type), TypeKind::Number),
    "number indexer should sort before string"
  );
  assert!(matches!(
    store.type_kind(indexers[1].key_type),
    TypeKind::String
  ));
}

#[test]
fn program_structural_queries_expand_refs() {
  #[derive(Default)]
  struct MemoryHost {
    files: HashMap<FileId, Arc<str>>,
  }

  impl MemoryHost {
    fn insert(&mut self, file: FileId, src: &str) {
      self.files.insert(file, Arc::from(src.to_string()));
    }
  }

  impl Host for MemoryHost {
    fn file_text(&self, file: FileId) -> Result<Arc<str>, HostError> {
      self
        .files
        .get(&file)
        .cloned()
        .ok_or_else(|| HostError::new(format!("missing file {file:?}")))
    }

    fn resolve(&self, _from: FileId, _specifier: &str) -> Option<FileId> {
      None
    }
  }

  let mut host = MemoryHost::default();
  host.insert(
    FileId(0),
    r#"
interface Thing {
  readonly a: number;
  maybe?: string;
  (value: number): number;
  (value: string): string;
  new (flag: boolean): Thing;
  [key: string]: boolean;
}

type Alias = Thing;
"#,
  );

  let program = Program::new(host, vec![FileId(0)]);
  let diagnostics = program.check();
  assert!(
    diagnostics.is_empty(),
    "expected no diagnostics, got {diagnostics:?}"
  );

  let alias_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Alias"))
    .expect("alias definition present");
  let alias_ty = program.type_of_def_interned(alias_def);
  assert!(
    matches!(program.type_kind(alias_ty), TypeKindSummary::Object),
    "expanded alias should expose object shape"
  );

  let props = program.properties_of(alias_ty);
  assert_eq!(props.len(), 2);

  let a_prop = props
    .iter()
    .find(|p| p.key == PropertyKey::String("a".into()))
    .expect("a property present");
  assert!(a_prop.readonly);
  assert!(!a_prop.optional);
  assert!(matches!(
    program.interned_type_kind(a_prop.ty),
    TypeKind::Number
  ));

  let maybe_prop = props
    .iter()
    .find(|p| p.key == PropertyKey::String("maybe".into()))
    .expect("maybe property present");
  assert!(maybe_prop.optional);
  match program.interned_type_kind(maybe_prop.ty) {
    TypeKind::Union(members) => {
      assert!(members
        .iter()
        .any(|m| matches!(program.interned_type_kind(*m), TypeKind::String)));
      assert!(members
        .iter()
        .any(|m| matches!(program.interned_type_kind(*m), TypeKind::Undefined)));
    }
    other => panic!("expected union including undefined, got {other:?}"),
  }

  let prop_via_lookup = program
    .property_type(alias_ty, PropertyKey::String("a".into()))
    .expect("property lookup should succeed");
  assert!(matches!(
    program.interned_type_kind(prop_via_lookup),
    TypeKind::Number
  ));

  let dynamic = program
    .property_type(alias_ty, PropertyKey::String("dynamic".into()))
    .expect("string indexer should allow dynamic properties");
  assert!(matches!(
    program.interned_type_kind(dynamic),
    TypeKind::Boolean
  ));

  let call_sigs = program.call_signatures(alias_ty);
  assert_eq!(call_sigs.len(), 2);
  assert!(matches!(
    program.interned_type_kind(call_sigs[0].signature.params[0].ty),
    TypeKind::Number
  ));
  assert!(matches!(
    program.interned_type_kind(call_sigs[1].signature.params[0].ty),
    TypeKind::String
  ));

  let construct_sigs = program.construct_signatures(alias_ty);
  assert_eq!(construct_sigs.len(), 1);
  assert!(matches!(
    program.interned_type_kind(construct_sigs[0].signature.params[0].ty),
    TypeKind::Boolean
  ));

  let indexers = program.indexers(alias_ty);
  assert_eq!(indexers.len(), 1);
  assert!(matches!(
    program.interned_type_kind(indexers[0].key_type),
    TypeKind::String
  ));
  assert!(matches!(
    program.interned_type_kind(indexers[0].value_type),
    TypeKind::Boolean
  ));
  assert!(!indexers[0].readonly);
}

#[test]
fn type_alias_recursion_is_cycle_safe() {
  let mut host = TestHost::default();
  host.insert(FileId(0), "type Alias = Alias | number;");
  let program = Program::new(host, vec![FileId(0)]);
  let alias_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Alias"))
    .expect("alias definition present");
  let ty = program.type_of_def(alias_def);
  match program.type_kind(ty) {
    TypeKindSummary::Union { members } => assert_eq!(members, 2),
    other => panic!("expected union for recursive alias, got {other:?}"),
  }
  let rendered = program.display_type(ty).to_string();
  assert!(
    rendered.contains("Alias") || rendered.contains("number"),
    "display should render recursive alias, got {rendered}"
  );
}

#[test]
fn interface_extends_and_intersections_merge_shapes() {
  let mut host = TestHost::default();
  host.insert(
    FileId(0),
    r#"
interface Base { a: string; }
interface Extra { b: number; }
interface Derived extends Base { c: boolean; }
type Combined = Derived & Extra;
"#,
  );
  let program = Program::new(host, vec![FileId(0)]);
  let combined_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Combined"))
    .expect("combined alias present");
  let ty = program.type_of_def(combined_def);
  let props = program.properties_of(ty);
  let prop = |name: &str| {
    props
      .iter()
      .find(|p| p.key == PropertyKey::String(name.to_string()))
      .cloned()
      .expect("property present")
  };
  assert!(matches!(
    program.interned_type_kind(prop("a").ty),
    TypeKind::String
  ));
  assert!(matches!(
    program.interned_type_kind(prop("b").ty),
    TypeKind::Number
  ));
  assert!(matches!(
    program.interned_type_kind(prop("c").ty),
    TypeKind::Boolean
  ));
}

#[test]
fn function_signature_is_lowered_from_type_alias() {
  let mut host = TestHost::default();
  host.insert(
    FileId(0),
    "type FnAlias = (value: string, count?: number) => boolean;",
  );
  let program = Program::new(host, vec![FileId(0)]);
  let fn_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("FnAlias"))
    .expect("function alias present");
  let ty = program.type_of_def(fn_def);
  let sigs = program.call_signatures(ty);
  assert_eq!(sigs.len(), 1);
  let sig = &sigs[0].signature;
  assert_eq!(sig.params.len(), 2);
  assert!(matches!(
    program.interned_type_kind(sig.params[0].ty),
    TypeKind::String
  ));
  assert!(matches!(
    program.interned_type_kind(sig.params[1].ty),
    TypeKind::Number
  ));
  assert!(sig.params[1].optional);
  assert!(matches!(
    program.interned_type_kind(sig.ret),
    TypeKind::Boolean
  ));
}

#[test]
fn recursive_alias_properties_preserve_references() {
  let mut host = TestHost::default();
  host.insert(
    FileId(0),
    r#"
type List = { value: number; next: List | null };
"#,
  );
  let program = Program::new(host, vec![FileId(0)]);
  let list_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("List"))
    .expect("List alias present");
  let ty = program.type_of_def(list_def);
  let props = program.properties_of(ty);
  let value = props
    .iter()
    .find(|p| p.key == PropertyKey::String("value".into()))
    .expect("value property present");
  assert_eq!(program.display_type(value.ty).to_string(), "number");
  let next = props
    .iter()
    .find(|p| p.key == PropertyKey::String("next".into()))
    .expect("next property present");
  assert_eq!(program.display_type(next.ty).to_string(), "List | null");
}

#[test]
fn recursive_type_alias_expands_through_refs() {
  let mut host = TestHost::default();
  host.insert(
    FileId(0),
    r#"
type Node = { value: number; next?: Node };
"#,
  );
  let program = Program::new(host, vec![FileId(0)]);
  let node_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Node"))
    .expect("Node definition present");
  let node_ty = program.type_of_def(node_def);
  let next_ty = program
    .property_type(node_ty, PropertyKey::String("next".into()))
    .expect("next property available");
  match program.interned_type_kind(next_ty) {
    TypeKind::Union(members) => {
      assert!(
        members
          .iter()
          .any(|member| match program.interned_type_kind(*member) {
            TypeKind::Ref { def, .. } => def.0 == node_def.0,
            _ => false,
          }),
        "union should include self reference"
      );
      assert!(
        members
          .iter()
          .any(|member| matches!(program.type_kind(*member), TypeKindSummary::Undefined)),
        "optional property should include undefined"
      );
    }
    TypeKind::Ref { def, .. } => assert_eq!(def.0, node_def.0),
    other => panic!("expected ref or union to self, got {other:?}"),
  }
}

#[test]
fn interface_extends_and_intersections_merge_members() {
  let mut host = TestHost::default();
  host.insert(
    FileId(0),
    r#"
interface Base { base: number }
interface Derived extends Base { derived: string }
type Combined = Derived & { extra: boolean };
"#,
  );
  let program = Program::new(host, vec![FileId(0)]);
  let derived_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Derived"))
    .expect("Derived interface present");
  let combined_def = program
    .definitions_in_file(FileId(0))
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some("Combined"))
    .expect("Combined alias present");

  let derived_ty = program.type_of_def(derived_def);
  let base_prop = program
    .property_type(derived_ty, PropertyKey::String("base".into()))
    .expect("base property present");
  assert!(matches!(
    program.type_kind(base_prop),
    TypeKindSummary::Number
  ));
  let derived_prop = program
    .property_type(derived_ty, PropertyKey::String("derived".into()))
    .expect("derived property present");
  assert!(matches!(
    program.type_kind(derived_prop),
    TypeKindSummary::String
  ));

  let combined_ty = program.type_of_def(combined_def);
  for (name, expected) in [
    ("base", TypeKindSummary::Number),
    ("derived", TypeKindSummary::String),
    ("extra", TypeKindSummary::Boolean),
  ] {
    let prop = program
      .property_type(combined_ty, PropertyKey::String(name.into()))
      .unwrap_or_else(|| panic!("{name} property missing"));
    assert!(
      matches!(program.type_kind(prop), k if k == expected),
      "{name} property should match expected kind"
    );
  }
}
