use rand::rngs::StdRng;
use rand::seq::SliceRandom;
use rand::SeedableRng;
use std::collections::BTreeMap;
use std::thread;
use types_ts_interned::{NameId, TypeStore};

#[test]
fn name_interning_is_deterministic_under_parallelism() {
  const THREADS: usize = 8;
  const ITERATIONS: usize = 5;

  let names: Vec<String> = (0..256).map(|i| format!("name_{i}")).collect();

  let baseline_store = TypeStore::new();
  let expected: BTreeMap<String, NameId> = names
    .iter()
    .map(|name| (name.clone(), baseline_store.intern_name(name.clone())))
    .collect();

  for iter in 0..ITERATIONS {
    let store = TypeStore::new();
    let shared = store.clone();
    let mut handles = Vec::new();

    for thread_index in 0..THREADS {
      let store = shared.clone();
      let mut local_names = names.clone();
      let mut rng = StdRng::seed_from_u64((iter as u64) << 32 | thread_index as u64);
      local_names.shuffle(&mut rng);

      handles.push(thread::spawn(move || {
        let mut seen = Vec::with_capacity(local_names.len());
        for name in local_names {
          seen.push((name.clone(), store.intern_name(name)));
        }
        seen
      }));
    }

    for handle in handles {
      for (name, id) in handle.join().expect("thread panicked") {
        assert_eq!(id, *expected.get(&name).unwrap());
      }
    }

    let final_map: BTreeMap<_, _> = names
      .iter()
      .map(|name| (name.clone(), shared.intern_name(name.clone())))
      .collect();
    assert_eq!(final_map, expected);

    for (name, id) in &expected {
      assert_eq!(shared.name(*id), *name);
    }
  }
}
