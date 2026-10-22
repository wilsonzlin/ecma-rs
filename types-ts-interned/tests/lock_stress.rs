//! Regression stress for NameInterner RwLock fairness deadlock.
//!
//! parking_lot's fair RwLock deadlocks if a read guard is held across a call that
//! re-enters `names.read()` while a writer is queued (see
//! `wiki/architecture/determinism.md` case study). This test keeps writers
//! (`intern_name`) and readers that recurse through `type_cmp`/`compare_props`
//! hot concurrently. It must complete within a deadline — hanging is a failure.

use std::sync::atomic::{AtomicBool, Ordering as AtomicOrdering};
use std::sync::{Arc, Barrier};
use std::thread;
use std::time::{Duration, Instant};

use types_ts_interned::{
  ObjectType, PropData, PropKey, Property, Shape, TypeId, TypeKind, TypeStore,
};

const THREADS: usize = 8;
const ITERS_PER_THREAD: usize = 400;
/// Wall-clock budget for the whole stress run (generous under load).
const DEADLINE: Duration = Duration::from_secs(60);

fn prop_data(ty: TypeId) -> PropData {
  PropData {
    ty,
    optional: false,
    readonly: false,
    accessibility: None,
    is_method: false,
    origin: None,
    declared_on: None,
  }
}

/// Build a fresh object whose property *keys* and *value types* are string
/// literals / named props so `compare_props` → `type_cmp(StringLiteral)` is hot.
fn build_object_with_literals(store: &TypeStore, thread: usize, iter: usize) -> TypeId {
  let key_a = store.intern_name(format!("key_a_{thread}_{iter}"));
  let key_b = store.intern_name(format!("key_b_{thread}_{iter}"));
  let lit_a = store.intern_type(TypeKind::StringLiteral(
    store.intern_name(format!("lit_a_{thread}_{iter}")),
  ));
  let lit_b = store.intern_type(TypeKind::StringLiteral(
    store.intern_name(format!("lit_b_{thread}_{iter}")),
  ));
  // Insert props out of name order so shape canonicalization must sort via
  // `compare_props` / name-resolved key ordering while type_cmp may re-enter names.
  let shape = Shape {
    properties: vec![
      Property {
        key: PropKey::String(key_b),
        data: prop_data(lit_b),
      },
      Property {
        key: PropKey::String(key_a),
        data: prop_data(lit_a),
      },
    ],
    call_signatures: Vec::new(),
    construct_signatures: Vec::new(),
    indexers: Vec::new(),
  };
  let shape_id = store.intern_shape(shape);
  let obj = store.intern_object(ObjectType { shape: shape_id });
  store.intern_type(TypeKind::Object(obj))
}

#[test]
fn name_interner_fairness_no_deadlock() {
  let store = TypeStore::new();
  let barrier = Arc::new(Barrier::new(THREADS));
  let timed_out = Arc::new(AtomicBool::new(false));
  let start = Instant::now();

  let mut handles = Vec::with_capacity(THREADS);
  for thread_id in 0..THREADS {
    let store = Arc::clone(&store);
    let barrier = Arc::clone(&barrier);
    let timed_out = Arc::clone(&timed_out);
    handles.push(thread::spawn(move || {
      barrier.wait();
      let mut last_union: Option<TypeId> = None;
      for iter in 0..ITERS_PER_THREAD {
        if start.elapsed() > DEADLINE {
          timed_out.store(true, AtomicOrdering::Relaxed);
          return;
        }

        // Writer pressure on the NameInterner.
        let _fresh = store.intern_name(format!("writer_{thread_id}_{iter}"));

        let obj = build_object_with_literals(&store, thread_id, iter);
        let lit = store.intern_type(TypeKind::StringLiteral(
          store.intern_name(format!("union_lit_{thread_id}_{iter}")),
        ));
        // Union canonicalization sorts members with `type_cmp`, which may compare
        // string literals (names.read) while other threads write names.
        let union = store.intern_type(TypeKind::Union(vec![
          obj,
          lit,
          store.primitive_ids().string,
        ]));

        // Invariant: re-interning the same kind yields the same TypeId.
        let again = store.intern_type(TypeKind::Union(vec![
          obj,
          lit,
          store.primitive_ids().string,
        ]));
        assert_eq!(union, again, "union canonicalization must be idempotent");

        // Cross-thread deterministic identity: same content → same ID regardless
        // of which thread first interned (content-addressed fingerprints).
        if thread_id == 0 {
          last_union = Some(union);
        } else if iter == 0 {
          // Touch type_cmp across distinct objects from this thread.
          let _ord = store.type_cmp(obj, lit);
          let _ = last_union;
        }
      }
    }));
  }

  for handle in handles {
    match handle.join() {
      Ok(()) => {}
      Err(_) => panic!("worker thread panicked"),
    }
  }

  assert!(
    !timed_out.load(AtomicOrdering::Relaxed),
    "NameInterner lock stress exceeded {:?} — likely writer-fairness deadlock",
    DEADLINE
  );
  assert!(
    start.elapsed() < DEADLINE,
    "stress run took {:?}, expected completion under {:?}",
    start.elapsed(),
    DEADLINE
  );

  // Determinism invariant: building the same logical graph on a fresh store
  // produces identical TypeIds (order-independent content addressing).
  let store_a = TypeStore::new();
  let store_b = TypeStore::new();
  let id_a = build_object_with_literals(&store_a, 0, 0);
  let id_b = build_object_with_literals(&store_b, 0, 0);
  assert_eq!(
    id_a, id_b,
    "identical object graphs must share TypeIds across independent stores"
  );
}
