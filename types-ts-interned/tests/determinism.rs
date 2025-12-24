use std::sync::Arc;
use std::thread;

use types_ts_interned::Accessibility;
use types_ts_interned::Indexer;
use types_ts_interned::NameId;
use types_ts_interned::ObjectId;
use types_ts_interned::ObjectType;
use types_ts_interned::Param;
use types_ts_interned::PropData;
use types_ts_interned::PropKey;
use types_ts_interned::Property;
use types_ts_interned::Shape;
use types_ts_interned::ShapeId;
use types_ts_interned::Signature;
use types_ts_interned::SignatureId;
use types_ts_interned::TemplateChunk;
use types_ts_interned::TemplateLiteralType;
use types_ts_interned::TypeId;
use types_ts_interned::TypeKind;
use types_ts_interned::TypeStore;

#[derive(Debug, Clone, PartialEq, Eq)]
struct ResolvedSnapshot {
  alpha: NameId,
  beta: NameId,
  sig_number: SignatureId,
  sig_string: SignatureId,
  callable: TypeId,
  shape: ShapeId,
  object: ObjectId,
  object_type: TypeId,
  union: TypeId,
  intersection: TypeId,
  indexed_access: TypeId,
  template: TypeId,
}

#[derive(Debug, Default)]
struct Snapshot {
  alpha: Option<NameId>,
  beta: Option<NameId>,
  sig_number: Option<SignatureId>,
  sig_string: Option<SignatureId>,
  callable: Option<TypeId>,
  shape: Option<ShapeId>,
  object: Option<ObjectId>,
  object_type: Option<TypeId>,
  union: Option<TypeId>,
  intersection: Option<TypeId>,
  indexed_access: Option<TypeId>,
  template: Option<TypeId>,
}

impl Snapshot {
  fn ensure_alpha(&mut self, store: &TypeStore) -> NameId {
    *self.alpha.get_or_insert_with(|| store.intern_name("alpha"))
  }

  fn ensure_beta(&mut self, store: &TypeStore) -> NameId {
    *self.beta.get_or_insert_with(|| store.intern_name("beta"))
  }

  fn ensure_sig_number(&mut self, store: &TypeStore) -> SignatureId {
    if let Some(id) = self.sig_number {
      id
    } else {
      let primitives = store.primitive_ids();
      let param_name = Some(self.ensure_alpha(store));
      let id = store.intern_signature(Signature::new(
        vec![Param {
          name: param_name,
          ty: primitives.number,
          optional: false,
          rest: false,
        }],
        primitives.string,
      ));
      self.sig_number = Some(id);
      id
    }
  }

  fn ensure_sig_string(&mut self, store: &TypeStore) -> SignatureId {
    if let Some(id) = self.sig_string {
      id
    } else {
      let primitives = store.primitive_ids();
      let param_name = Some(self.ensure_beta(store));
      let id = store.intern_signature(Signature::new(
        vec![Param {
          name: param_name,
          ty: primitives.string,
          optional: false,
          rest: false,
        }],
        primitives.void,
      ));
      self.sig_string = Some(id);
      id
    }
  }

  fn ensure_callable(&mut self, store: &TypeStore) -> TypeId {
    if let Some(id) = self.callable {
      id
    } else {
      let sig_a = self.ensure_sig_number(store);
      let sig_b = self.ensure_sig_string(store);
      let id = store.intern_type(TypeKind::Callable {
        overloads: vec![sig_a, sig_b],
      });
      self.callable = Some(id);
      id
    }
  }

  fn ensure_template(&mut self, store: &TypeStore) -> TypeId {
    if let Some(id) = self.template {
      id
    } else {
      let primitives = store.primitive_ids();
      let id = store.intern_type(TypeKind::TemplateLiteral(TemplateLiteralType {
        head: "template_head".into(),
        spans: vec![TemplateChunk {
          literal: "tail".into(),
          ty: primitives.boolean,
        }],
      }));
      self.template = Some(id);
      id
    }
  }

  fn ensure_shape(&mut self, store: &TypeStore) -> ShapeId {
    if let Some(id) = self.shape {
      id
    } else {
      let primitives = store.primitive_ids();
      let alpha = self.ensure_alpha(store);
      let beta = self.ensure_beta(store);
      let sig = self.ensure_sig_number(store);
      let mut shape = Shape::new();
      shape.properties.push(Property {
        key: PropKey::String(alpha),
        data: PropData {
          ty: primitives.string,
          optional: false,
          readonly: true,
          accessibility: Some(Accessibility::Public),
        },
      });
      shape.properties.push(Property {
        key: PropKey::String(beta),
        data: PropData {
          ty: primitives.number,
          optional: true,
          readonly: false,
          accessibility: Some(Accessibility::Private),
        },
      });
      shape.call_signatures.push(sig);
      shape.indexers.push(Indexer {
        key_type: primitives.string,
        value_type: primitives.boolean,
        readonly: true,
      });
      let id = store.intern_shape(shape);
      self.shape = Some(id);
      id
    }
  }

  fn ensure_object(&mut self, store: &TypeStore) -> ObjectId {
    if let Some(id) = self.object {
      id
    } else {
      let shape = self.ensure_shape(store);
      let id = store.intern_object(ObjectType { shape });
      self.object = Some(id);
      id
    }
  }

  fn ensure_object_type(&mut self, store: &TypeStore) -> TypeId {
    if let Some(id) = self.object_type {
      id
    } else {
      let obj = self.ensure_object(store);
      let id = store.intern_type(TypeKind::Object(obj));
      self.object_type = Some(id);
      id
    }
  }

  fn ensure_union(&mut self, store: &TypeStore) -> TypeId {
    if let Some(id) = self.union {
      id
    } else {
      let primitives = store.primitive_ids();
      let template = self.ensure_template(store);
      let id = store.union(vec![primitives.boolean, primitives.number, template]);
      self.union = Some(id);
      id
    }
  }

  fn ensure_intersection(&mut self, store: &TypeStore) -> TypeId {
    if let Some(id) = self.intersection {
      id
    } else {
      let callable = self.ensure_callable(store);
      let object_type = self.ensure_object_type(store);
      let union = self.ensure_union(store);
      let id = store.intersection(vec![callable, object_type, union]);
      self.intersection = Some(id);
      id
    }
  }

  fn ensure_indexed_access(&mut self, store: &TypeStore) -> TypeId {
    if let Some(id) = self.indexed_access {
      id
    } else {
      let object_type = self.ensure_object_type(store);
      let index = self.ensure_union(store);
      let id = store.intern_type(TypeKind::IndexedAccess {
        obj: object_type,
        index,
      });
      self.indexed_access = Some(id);
      id
    }
  }

  fn into_resolved(mut self, store: &TypeStore) -> ResolvedSnapshot {
    ResolvedSnapshot {
      alpha: self.ensure_alpha(store),
      beta: self.ensure_beta(store),
      sig_number: self.ensure_sig_number(store),
      sig_string: self.ensure_sig_string(store),
      callable: self.ensure_callable(store),
      shape: self.ensure_shape(store),
      object: self.ensure_object(store),
      object_type: self.ensure_object_type(store),
      union: self.ensure_union(store),
      intersection: self.ensure_intersection(store),
      indexed_access: self.ensure_indexed_access(store),
      template: self.ensure_template(store),
    }
  }
}

#[derive(Clone, Copy)]
enum Operation {
  Names,
  Signatures,
  Callable,
  Shape,
  Union,
  Intersection,
  IndexedAccess,
  Template,
}

fn shuffle<T>(items: &mut [T], mut seed: u64) {
  if items.is_empty() {
    return;
  }
  for i in (1..items.len()).rev() {
    seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
    let j = (seed >> 32) as usize % (i + 1);
    items.swap(i, j);
  }
}

fn run_thread(store: Arc<TypeStore>, seed: u64) -> ResolvedSnapshot {
  let mut ops = [
    Operation::Names,
    Operation::Signatures,
    Operation::Callable,
    Operation::Shape,
    Operation::Union,
    Operation::Intersection,
    Operation::IndexedAccess,
    Operation::Template,
  ];
  shuffle(&mut ops, seed);

  let mut snapshot = Snapshot::default();
  for op in ops {
    match op {
      Operation::Names => {
        snapshot.ensure_alpha(&store);
        snapshot.ensure_beta(&store);
      }
      Operation::Signatures => {
        snapshot.ensure_sig_number(&store);
        snapshot.ensure_sig_string(&store);
      }
      Operation::Callable => {
        snapshot.ensure_callable(&store);
      }
      Operation::Shape => {
        snapshot.ensure_object_type(&store);
      }
      Operation::Union => {
        snapshot.ensure_union(&store);
      }
      Operation::Intersection => {
        snapshot.ensure_intersection(&store);
      }
      Operation::IndexedAccess => {
        snapshot.ensure_indexed_access(&store);
      }
      Operation::Template => {
        snapshot.ensure_template(&store);
      }
    }
  }

  snapshot.into_resolved(&store)
}

#[test]
fn deterministic_ids_under_parallel_interning() {
  const THREADS: usize = 8;
  const RUNS: usize = 5;

  let mut previous: Option<ResolvedSnapshot> = None;

  for run in 0..RUNS {
    let store = TypeStore::new();
    let mut handles = Vec::new();
    for thread_idx in 0..THREADS {
      let store = Arc::clone(&store);
      let seed = (run as u64).wrapping_mul(0x517c_c1b7_2722_0a95)
        ^ (thread_idx as u64 + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15);
      handles.push(thread::spawn(move || run_thread(store, seed)));
    }

    let snapshots: Vec<ResolvedSnapshot> = handles
      .into_iter()
      .map(|handle| handle.join().expect("thread panicked"))
      .collect();

    let reference = snapshots.first().expect("no snapshots produced").clone();
    for snapshot in snapshots.iter().skip(1) {
      assert_eq!(snapshot, &reference, "snapshots diverged within run {run}");
    }

    if let Some(prev) = previous.as_ref() {
      assert_eq!(reference, *prev, "snapshots diverged across runs");
    }
    previous = Some(reference);
  }
}
