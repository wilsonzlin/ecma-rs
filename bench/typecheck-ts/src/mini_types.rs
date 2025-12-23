use ahash::AHashMap;
use serde::Serialize;

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Serialize)]
pub struct TypeId(u32);

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum SimpleType {
  Any,
  Never,
  Number,
  String,
  Boolean,
  Null,
  Undefined,
  LiteralStr(&'static str),
  LiteralNum(i64),
  Array(TypeId),
  Tuple(Vec<TypeId>),
  Union(Vec<TypeId>),
  Intersection(Vec<TypeId>),
  #[allow(dead_code)]
  Generic(u8),
}

#[derive(Debug)]
pub struct TypeStore {
  types: Vec<SimpleType>,
  intern: AHashMap<SimpleType, TypeId>,
  pub any: TypeId,
  pub never: TypeId,
  pub number: TypeId,
  pub string: TypeId,
  pub boolean: TypeId,
  pub null: TypeId,
  pub undefined: TypeId,
}

impl TypeStore {
  pub fn new() -> Self {
    let mut store = TypeStore {
      types: Vec::new(),
      intern: AHashMap::new(),
      any: TypeId(0),
      never: TypeId(0),
      number: TypeId(0),
      string: TypeId(0),
      boolean: TypeId(0),
      null: TypeId(0),
      undefined: TypeId(0),
    };

    store.any = store.intern(SimpleType::Any);
    store.never = store.intern(SimpleType::Never);
    store.number = store.intern(SimpleType::Number);
    store.string = store.intern(SimpleType::String);
    store.boolean = store.intern(SimpleType::Boolean);
    store.null = store.intern(SimpleType::Null);
    store.undefined = store.intern(SimpleType::Undefined);
    store
  }

  fn get(&self, id: TypeId) -> &SimpleType {
    &self.types[id.0 as usize]
  }

  fn intern(&mut self, typ: SimpleType) -> TypeId {
    if let Some(existing) = self.intern.get(&typ) {
      return *existing;
    }
    let id = TypeId(self.types.len() as u32);
    self.types.push(typ.clone());
    self.intern.insert(typ, id);
    id
  }

  pub fn literal_str(&mut self, value: &'static str) -> TypeId {
    self.intern(SimpleType::LiteralStr(value))
  }

  pub fn literal_num(&mut self, value: i64) -> TypeId {
    self.intern(SimpleType::LiteralNum(value))
  }

  pub fn array(&mut self, element: TypeId) -> TypeId {
    self.intern(SimpleType::Array(element))
  }

  pub fn tuple(&mut self, elements: Vec<TypeId>) -> TypeId {
    self.intern(SimpleType::Tuple(elements))
  }

  pub fn union(&mut self, members: Vec<TypeId>) -> TypeId {
    let mut flat: Vec<TypeId> = Vec::new();
    for member in members {
      match self.get(member) {
        SimpleType::Union(existing) => flat.extend(existing.iter().copied()),
        SimpleType::Never => {}
        _ => flat.push(member),
      }
    }

    flat.sort_unstable_by_key(|id| id.0);
    flat.dedup();

    if flat.is_empty() {
      return self.never;
    }

    if flat.len() == 1 {
      return flat[0];
    }

    self.intern(SimpleType::Union(flat))
  }

  pub fn intersection(&mut self, members: Vec<TypeId>) -> TypeId {
    let mut flat: Vec<TypeId> = Vec::new();
    for member in members {
      match self.get(member) {
        SimpleType::Intersection(existing) => flat.extend(existing.iter().copied()),
        SimpleType::Never => return self.never,
        _ => flat.push(member),
      }
    }

    flat.sort_unstable_by_key(|id| id.0);
    flat.dedup();

    if flat.len() == 1 {
      return flat[0];
    }

    self.intern(SimpleType::Intersection(flat))
  }
}

#[derive(Default, Debug)]
pub struct Relations {
  cache: AHashMap<(TypeId, TypeId), bool>,
}

impl Relations {
  pub fn new() -> Self {
    Relations {
      cache: AHashMap::new(),
    }
  }

  pub fn clear(&mut self) {
    self.cache.clear();
  }

  pub fn cache_size(&self) -> usize {
    self.cache.len()
  }

  pub fn assignable(&mut self, store: &TypeStore, src: TypeId, dst: TypeId) -> bool {
    if src == dst {
      return true;
    }

    if let Some(result) = self.cache.get(&(src, dst)) {
      return *result;
    }

    // Insert a provisional value to avoid accidental cycles.
    self.cache.insert((src, dst), true);

    let result = match (store.get(src), store.get(dst)) {
      (_, SimpleType::Any) => true,
      (SimpleType::Never, _) => true,
      (_, SimpleType::Never) => false,
      (SimpleType::LiteralStr(a), SimpleType::LiteralStr(b)) => a == b,
      (SimpleType::LiteralNum(a), SimpleType::LiteralNum(b)) => a == b,
      (SimpleType::LiteralStr(_), SimpleType::String) => true,
      (SimpleType::LiteralNum(_), SimpleType::Number) => true,
      (SimpleType::String, SimpleType::LiteralStr(_)) => false,
      (SimpleType::Number, SimpleType::LiteralNum(_)) => false,
      (SimpleType::Union(members), target) => members
        .iter()
        .all(|member| self.assignable(store, *member, dst) && target != &SimpleType::Never),
      (source, SimpleType::Union(members)) => members
        .iter()
        .any(|member| self.assignable(store, src, *member) || matches!(source, SimpleType::Never)),
      (SimpleType::Intersection(members), _) => members
        .iter()
        .all(|member| self.assignable(store, *member, dst)),
      (_, SimpleType::Intersection(members)) => members
        .iter()
        .all(|member| self.assignable(store, src, *member)),
      (SimpleType::Array(src_elem), SimpleType::Array(dst_elem)) => {
        self.assignable(store, *src_elem, *dst_elem)
      }
      (SimpleType::Tuple(src), SimpleType::Tuple(dst)) if src.len() == dst.len() => src
        .iter()
        .zip(dst.iter())
        .all(|(s, d)| self.assignable(store, *s, *d)),
      (SimpleType::Tuple(src), SimpleType::Array(dst_elem)) => src
        .iter()
        .all(|s| self.assignable(store, *s, *dst_elem)),
      (SimpleType::Array(src_elem), SimpleType::Tuple(dst)) => dst
        .iter()
        .all(|d| self.assignable(store, *src_elem, *d)),
      (SimpleType::Generic(a), SimpleType::Generic(b)) => a == b,
      (SimpleType::Generic(_), _) => true,
      (SimpleType::Boolean, SimpleType::Boolean)
      | (SimpleType::Number, SimpleType::Number)
      | (SimpleType::String, SimpleType::String)
      | (SimpleType::Null, SimpleType::Null)
      | (SimpleType::Undefined, SimpleType::Undefined) => true,
      _ => false,
    };

    if let Some(slot) = self.cache.get_mut(&(src, dst)) {
      *slot = result;
    }

    result
  }
}

#[derive(Clone, Copy, Debug, Serialize)]
pub struct CheckStats {
  pub steps: usize,
  pub successes: usize,
}

#[derive(Clone)]
struct Signature {
  params: Vec<TypePattern>,
  ret: TypePattern,
}

#[derive(Clone)]
enum TypePattern {
  Concrete(TypeId),
  Generic(u8),
  Array(Box<TypePattern>),
  Union(Vec<TypePattern>),
}

fn match_pattern(
  store: &TypeStore,
  relations: &mut Relations,
  pattern: &TypePattern,
  arg: TypeId,
  mapping: &mut AHashMap<u8, TypeId>,
  steps: &mut usize,
) -> bool {
  match pattern {
    TypePattern::Concrete(expected) => {
      *steps += 1;
      relations.assignable(store, arg, *expected)
    }
    TypePattern::Generic(id) => match mapping.get(id) {
      Some(existing) => {
        *steps += 1;
        relations.assignable(store, arg, *existing)
      }
      None => {
        mapping.insert(*id, arg);
        true
      }
    },
    TypePattern::Array(inner) => match store.get(arg) {
      SimpleType::Array(elem) => match_pattern(store, relations, inner, *elem, mapping, steps),
      SimpleType::Tuple(elements) => elements
        .iter()
        .all(|el| match_pattern(store, relations, inner, *el, mapping, steps)),
      _ => false,
    },
    TypePattern::Union(options) => options
      .iter()
      .any(|opt| match_pattern(store, relations, opt, arg, mapping, steps)),
  }
}

fn instantiate_pattern(store: &mut TypeStore, mapping: &AHashMap<u8, TypeId>, pattern: &TypePattern) -> TypeId {
  match pattern {
    TypePattern::Concrete(id) => *id,
    TypePattern::Generic(id) => mapping.get(id).copied().unwrap_or(store.any),
    TypePattern::Array(inner) => {
      let elem = instantiate_pattern(store, mapping, inner);
      store.array(elem)
    }
    TypePattern::Union(parts) => {
      let resolved: Vec<TypeId> = parts
        .iter()
        .map(|p| instantiate_pattern(store, mapping, p))
        .collect();
      store.union(resolved)
    }
  }
}

fn resolve_overload(
  store: &mut TypeStore,
  relations: &mut Relations,
  signatures: &[Signature],
  args: &[TypeId],
  steps: &mut usize,
) -> Option<TypeId> {
  for sig in signatures {
    if sig.params.len() != args.len() {
      continue;
    }

    let mut mapping = AHashMap::new();
    let mut matched = true;
    for (pattern, arg) in sig.params.iter().zip(args.iter()) {
      if !match_pattern(store, relations, pattern, *arg, &mut mapping, steps) {
        matched = false;
        break;
      }
    }

    if matched {
      return Some(instantiate_pattern(store, &mapping, &sig.ret));
    }
  }

  None
}

pub fn control_flow_body(iterations: usize) -> CheckStats {
  let mut steps = 0;
  let mut successes = 0;

  for i in 0..iterations {
    let mut store = TypeStore::new();
    let mut relations = Relations::new();

    let mut value = store.union(vec![store.string, store.number, store.boolean, store.null]);
    let tag_literal = store.literal_str("flag");
    let numeric_literal = store.literal_num(i as i64);

    for branch in 0..6 {
      steps += 1;
      if branch % 2 == 0 {
        let narrowed = store.union(vec![tag_literal, store.string]);
        if relations.assignable(&store, value, narrowed) {
          successes += 1;
        }
        value = store.union(vec![narrowed, store.boolean]);
      } else {
        let widened = store.union(vec![store.number, numeric_literal]);
        if relations.assignable(&store, widened, value) {
          successes += 1;
        }
        value = store.union(vec![widened, store.null]);
      }
    }

    steps += relations.cache_size();
  }

  CheckStats { steps, successes }
}

pub fn union_intersection_body(iterations: usize) -> CheckStats {
  let mut steps = 0;
  let mut successes = 0;

  for _ in 0..iterations {
    let mut store = TypeStore::new();
    let mut relations = Relations::new();

    let numeric_literals: Vec<TypeId> = (0..12).map(|n| store.literal_num(n)).collect();
    let string_literals: Vec<TypeId> = ["a", "b", "c", "d"]
      .iter()
      .map(|s| store.literal_str(s))
      .collect();

    let wide_union = store.union(numeric_literals.clone());
    let tagged_union = store.union(string_literals.clone());
    let merged = store.union(vec![wide_union, tagged_union, store.boolean]);
    let numeric_or_string = store.union(vec![store.number, store.string]);
    let required = store.intersection(vec![merged, numeric_or_string]);

    steps += 1;
    if relations.assignable(&store, wide_union, required) {
      successes += 1;
    }

    steps += 1;
    if relations.assignable(&store, tagged_union, required) {
      successes += 1;
    }

    let extra_str = store.literal_str("extra");
    let extra_num = store.literal_num(99);
    let nested = store.union(vec![required, extra_str, extra_num]);
    for lit in numeric_literals.iter().take(6) {
      steps += 1;
      if relations.assignable(&store, *lit, nested) {
        successes += 1;
      }
    }

    steps += relations.cache_size();
  }

  CheckStats { steps, successes }
}

pub fn generic_overload_body(iterations: usize) -> CheckStats {
  let mut steps = 0;
  let mut successes = 0;

  for _ in 0..iterations {
    let mut store = TypeStore::new();
    let mut relations = Relations::new();

    let signatures = vec![
      Signature {
        params: vec![TypePattern::Generic(0)],
        ret: TypePattern::Generic(0),
      },
      Signature {
        params: vec![TypePattern::Concrete(store.string)],
        ret: TypePattern::Concrete(store.string),
      },
      Signature {
        params: vec![TypePattern::Array(Box::new(TypePattern::Generic(0)))],
        ret: TypePattern::Generic(0),
      },
      Signature {
        params: vec![TypePattern::Generic(0), TypePattern::Generic(1)],
        ret: TypePattern::Union(vec![TypePattern::Generic(0), TypePattern::Generic(1)]),
      },
    ];

    let alpha = store.literal_str("alpha");
    let lit_three = store.literal_num(3);
    let array_num_3 = store.array(lit_three);
    let lit_one = store.literal_num(1);
    let lit_two = store.literal_num(2);
    let lit_five = store.literal_num(5);
    let array_num_5 = store.array(lit_five);
    let lit_six = store.literal_num(6);
    let array_num_6 = store.array(lit_six);

    let calls: Vec<Vec<TypeId>> = vec![
      vec![alpha],
      vec![array_num_3],
      vec![lit_one, lit_two],
      vec![store.string, store.number],
      vec![array_num_5, array_num_6],
    ];

    for args in calls {
      if let Some(resolved) = resolve_overload(&mut store, &mut relations, &signatures, &args, &mut steps) {
        steps += 1;
        if relations.assignable(&store, resolved, store.any) {
          successes += 1;
        }
      }
    }

    steps += relations.cache_size();
  }

  CheckStats { steps, successes }
}

pub fn assignability_stress(iterations: usize, warm_cache: bool) -> CheckStats {
  let mut store = TypeStore::new();
  let mut primary_members = Vec::new();
  for n in 0..24 {
    primary_members.push(store.literal_num(n));
  }
  let primary_union = store.union(primary_members);

  let mut secondary_members = Vec::new();
  for n in 12..36 {
    secondary_members.push(store.literal_num(n));
  }
  let secondary_union = store.union(secondary_members);

  let narrow_a = store.literal_num(3);
  let narrow_b = store.literal_num(7);
  let narrow_c = store.literal_num(15);
  let narrow_union = store.union(vec![narrow_a, narrow_b, narrow_c]);
  let guarded = store.intersection(vec![primary_union, store.number]);

  let mut successes = 0;
  let mut steps = 0;

  if warm_cache {
    let mut relations = Relations::new();
    for _ in 0..3 {
      relations.assignable(&store, primary_union, guarded);
      relations.assignable(&store, secondary_union, guarded);
      relations.assignable(&store, narrow_union, primary_union);
    }

    for i in 0..iterations {
      steps += 2;
      let pick = if i % 2 == 0 { primary_union } else { secondary_union };
      if relations.assignable(&store, pick, guarded) {
        successes += 1;
      }
      if relations.assignable(&store, narrow_union, pick) {
        successes += 1;
      }
    }

    steps += relations.cache_size();
  } else {
    for i in 0..iterations {
      let mut relations = Relations::new();
      steps += 2;
      let pick = if i % 2 == 0 { primary_union } else { secondary_union };
      if relations.assignable(&store, pick, guarded) {
        successes += 1;
      }
      if relations.assignable(&store, narrow_union, pick) {
        successes += 1;
      }
    }
  }

  CheckStats { steps, successes }
}
