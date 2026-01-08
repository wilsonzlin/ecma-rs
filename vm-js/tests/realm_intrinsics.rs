use vm_js::{Heap, HeapLimits, Realm, VmError};

#[test]
fn realm_allocates_and_roots_global_object_and_well_known_symbols() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut heap)?;

  // Drop any temporary initialization scopes and ensure the realm's allocations survive GC.
  heap.collect_garbage();

  assert!(heap.is_valid_object(realm.global_object()));

  let wks = *realm.well_known_symbols();
  let cases = [
    (wks.async_iterator, "Symbol.asyncIterator"),
    (wks.has_instance, "Symbol.hasInstance"),
    (wks.is_concat_spreadable, "Symbol.isConcatSpreadable"),
    (wks.iterator, "Symbol.iterator"),
    (wks.match_, "Symbol.match"),
    (wks.match_all, "Symbol.matchAll"),
    (wks.replace, "Symbol.replace"),
    (wks.search, "Symbol.search"),
    (wks.species, "Symbol.species"),
    (wks.split, "Symbol.split"),
    (wks.to_primitive, "Symbol.toPrimitive"),
    (wks.to_string_tag, "Symbol.toStringTag"),
    (wks.unscopables, "Symbol.unscopables"),
  ];

  for (sym, expected_desc) in cases {
    assert!(heap.is_valid_symbol(sym));
    let desc = heap
      .get_symbol_description(sym)?
      .expect("well-known symbols should have descriptions");
    assert_eq!(heap.get_string(desc)?.to_utf8_lossy(), expected_desc);
  }

  // Avoid leaking persistent roots (and tripping the Realm drop assertion).
  realm.teardown(&mut heap);
  Ok(())
}

#[test]
fn realm_remove_roots_allows_collection() -> Result<(), VmError> {
  let mut heap = Heap::new(HeapLimits::new(1024 * 1024, 1024 * 1024));
  let mut realm = Realm::new(&mut heap)?;

  heap.collect_garbage();
  assert!(heap.is_valid_object(realm.global_object()));

  let wks = *realm.well_known_symbols();
  realm.remove_roots(&mut heap);

  heap.collect_garbage();

  assert!(!heap.is_valid_object(realm.global_object()));
  assert!(!heap.is_valid_symbol(wks.async_iterator));
  assert!(!heap.is_valid_symbol(wks.has_instance));
  assert!(!heap.is_valid_symbol(wks.is_concat_spreadable));
  assert!(!heap.is_valid_symbol(wks.iterator));
  assert!(!heap.is_valid_symbol(wks.match_));
  assert!(!heap.is_valid_symbol(wks.match_all));
  assert!(!heap.is_valid_symbol(wks.replace));
  assert!(!heap.is_valid_symbol(wks.search));
  assert!(!heap.is_valid_symbol(wks.species));
  assert!(!heap.is_valid_symbol(wks.split));
  assert!(!heap.is_valid_symbol(wks.to_primitive));
  assert!(!heap.is_valid_symbol(wks.to_string_tag));
  assert!(!heap.is_valid_symbol(wks.unscopables));

  Ok(())
}

