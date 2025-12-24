use std::cell::RefCell;
use std::collections::HashMap;

use hir_js::lower_from_source;
use types_ts_interned::TypeId;
use types_ts_interned::{DefId, TypeKind, TypeStore};

trait TypeExpander {
  fn expand_ref(&self, def: DefId, args: &[TypeId]) -> Option<TypeId>;
}

#[derive(Default)]
struct RecordingExpander {
  map: HashMap<DefId, TypeId>,
  seen: RefCell<Vec<(DefId, Vec<TypeId>)>>,
}

impl RecordingExpander {
  fn new(map: HashMap<DefId, TypeId>) -> Self {
    Self {
      map,
      seen: RefCell::default(),
    }
  }
}

impl TypeExpander for RecordingExpander {
  fn expand_ref(&self, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    self.seen.borrow_mut().push((def, args.to_vec()));
    self.map.get(&def).copied()
  }
}

fn expand_once(expander: &impl TypeExpander, store: &TypeStore, ty: TypeId) -> Option<TypeId> {
  match store.type_kind(ty) {
    TypeKind::Ref { def, args } => expander.expand_ref(def, &args),
    _ => None,
  }
}

#[test]
fn refs_use_hir_def_id_for_expansion() {
  let lowered = lower_from_source("function foo() {}").expect("lowering should succeed");
  let def_id = lowered.defs[0].id;

  let store = TypeStore::new();
  let primitives = store.primitive_ids();

  let ref_ty = store.intern_type(TypeKind::Ref {
    def: def_id,
    args: vec![primitives.string],
  });
  let target_ty = store.intern_type(TypeKind::Array {
    ty: primitives.number,
    readonly: false,
  });

  let expander = RecordingExpander::new(HashMap::from([(def_id, target_ty)]));
  let expanded = expand_once(&expander, &store, ref_ty).expect("expansion should succeed");

  assert_eq!(expanded, target_ty);

  let seen = expander.seen.borrow();
  assert_eq!(seen.as_slice(), &[(def_id, vec![primitives.string])]);
}
