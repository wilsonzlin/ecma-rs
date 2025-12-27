use crate::cache::{CacheConfig, CacheStats, ShardedCache};
use crate::eval::ExpandedType;
use crate::eval::TypeEvaluator;
use crate::eval::TypeExpander as EvalTypeExpander;
use crate::shape::Indexer;
use crate::shape::Property;
use crate::shape::Shape;
use crate::signature::Signature;
use crate::Accessibility;
use crate::DefId;
use crate::ObjectId;
use crate::PropData;
use crate::PropKey;
use crate::SignatureId;
use crate::TypeId;
use crate::TypeKind;
use crate::TypeOptions;
use crate::TypeStore;
use bitflags::bitflags;
use std::cell::RefCell;
use std::collections::HashSet;
use std::fmt;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelationKind {
  Assignable,
  Comparable,
  StrictSubtype,
}

bitflags! {
  #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
  pub struct RelationMode: u8 {
    const NONE = 0;
    const BIVARIANT_PARAMS = 1 << 0;
  }
}

#[derive(Debug, Clone)]
pub struct RelationResult {
  pub result: bool,
  pub reason: Option<ReasonNode>,
}

#[derive(Debug, Clone)]
pub struct ReasonNode {
  pub src: TypeId,
  pub dst: TypeId,
  pub relation: RelationKind,
  pub outcome: bool,
  pub note: Option<String>,
  pub children: Vec<ReasonNode>,
}

const MAX_REASON_DEPTH: usize = 12;
const MAX_REASON_NODES: usize = 256;

#[derive(Default, Debug)]
struct ReasonBudget {
  nodes: usize,
}

#[derive(Clone, Copy, Debug)]
enum OptionalFlavor {
  Property,
  Parameter,
  TupleElement,
  IndexerValue,
}

pub struct RelateHooks<'a> {
  pub expander: Option<&'a dyn RelateTypeExpander>,
  pub is_same_origin_private_member: Option<&'a dyn Fn(&Property, &Property) -> bool>,
}

impl<'a> fmt::Debug for RelateHooks<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RelateHooks")
      .field(
        "expander",
        &self.expander.as_ref().map(|_| "RelateTypeExpander"),
      )
      .field(
        "is_same_origin_private_member",
        &self.is_same_origin_private_member.as_ref().map(|_| "Fn"),
      )
      .finish()
  }
}

impl<'a> Default for RelateHooks<'a> {
  fn default() -> Self {
    Self {
      expander: None,
      is_same_origin_private_member: None,
    }
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RelationKey {
  src: TypeId,
  dst: TypeId,
  kind: RelationKind,
  mode: RelationMode,
}

#[derive(Clone, Debug)]
pub struct RelationCache {
  inner: Arc<ShardedCache<RelationKey, bool>>,
}

impl Default for RelationCache {
  fn default() -> Self {
    Self::new(CacheConfig::default())
  }
}

impl RelationCache {
  pub fn new(config: CacheConfig) -> Self {
    Self {
      inner: Arc::new(ShardedCache::new(config)),
    }
  }

  pub fn stats(&self) -> CacheStats {
    self.inner.stats()
  }

  pub fn len(&self) -> usize {
    self.inner.len()
  }

  fn get(&self, key: &RelationKey) -> Option<bool> {
    self.inner.get(key)
  }

  fn insert(&self, key: RelationKey, value: bool) {
    self.inner.insert(key, value);
  }

  pub fn clear(&self) {
    self.inner.clear();
  }
}

pub trait RelateTypeExpander {
  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId>;
}

struct RelateExpanderAdapter<'a> {
  hook: Option<&'a dyn RelateTypeExpander>,
}

impl<'a> EvalTypeExpander for RelateExpanderAdapter<'a> {
  fn expand(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<ExpandedType> {
    self
      .hook
      .and_then(|expander| expander.expand_ref(store, def, args))
      .map(|ty| ExpandedType {
        params: Vec::new(),
        ty,
      })
  }
}

pub struct RelateCtx<'a> {
  store: Arc<TypeStore>,
  pub options: TypeOptions,
  hooks: RelateHooks<'a>,
  cache: RelationCache,
  in_progress: RefCell<HashSet<RelationKey>>,
  reason_budget: RefCell<ReasonBudget>,
}

impl<'a> fmt::Debug for RelateCtx<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RelateCtx")
      .field("options", &self.options)
      .finish()
  }
}

impl<'a> RelateCtx<'a> {
  pub fn new(store: Arc<TypeStore>, options: TypeOptions) -> Self {
    Self::with_options(store, options)
  }

  pub fn with_options(store: Arc<TypeStore>, options: TypeOptions) -> Self {
    Self::with_hooks(store, options, RelateHooks::default())
  }

  pub fn with_hooks(store: Arc<TypeStore>, options: TypeOptions, hooks: RelateHooks<'a>) -> Self {
    Self::with_hooks_and_cache(store, options, hooks, RelationCache::default())
  }

  pub fn with_cache(store: Arc<TypeStore>, options: TypeOptions, cache: RelationCache) -> Self {
    Self::with_hooks_and_cache(store, options, RelateHooks::default(), cache)
  }

  pub fn with_cache_config(
    store: Arc<TypeStore>,
    options: TypeOptions,
    cache: CacheConfig,
  ) -> Self {
    Self::with_hooks_and_cache(
      store,
      options,
      RelateHooks::default(),
      RelationCache::new(cache),
    )
  }

  pub fn with_hooks_and_cache(
    store: Arc<TypeStore>,
    options: TypeOptions,
    hooks: RelateHooks<'a>,
    cache: RelationCache,
  ) -> Self {
    Self {
      store,
      options,
      hooks,
      cache,
      in_progress: RefCell::new(HashSet::new()),
      reason_budget: RefCell::new(ReasonBudget::default()),
    }
  }

  pub fn cache_stats(&self) -> CacheStats {
    self.cache.stats()
  }

  pub fn clear_cache(&self) {
    self.cache.clear();
  }

  pub fn cache_len(&self) -> usize {
    self.cache.len()
  }

  pub fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    self
      .relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::NONE,
        false,
        0,
      )
      .result
  }

  pub fn explain_assignable(&self, src: TypeId, dst: TypeId) -> RelationResult {
    self.reset_reason_budget();
    self.relate_internal(
      src,
      dst,
      RelationKind::Assignable,
      RelationMode::NONE,
      true,
      0,
    )
  }

  pub fn is_comparable(&self, a: TypeId, b: TypeId) -> bool {
    self
      .relate_internal(a, b, RelationKind::Comparable, RelationMode::NONE, false, 0)
      .result
  }

  pub fn is_strict_subtype(&self, src: TypeId, dst: TypeId) -> bool {
    self
      .relate_internal(
        src,
        dst,
        RelationKind::StrictSubtype,
        RelationMode::NONE,
        false,
        0,
      )
      .result
  }

  fn relate_internal(
    &self,
    src: TypeId,
    dst: TypeId,
    kind: RelationKind,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind,
      mode,
    };
    if let Some(hit) = self.cache.get(&key) {
      return RelationResult {
        result: hit,
        reason: record
          .then(|| self.cached_reason(key, hit, depth))
          .flatten(),
      };
    }
    if self.in_progress.borrow().contains(&key) {
      // Structural relations in TypeScript assume success on cycles to break
      // infinite recursion. We mirror that here.
      return RelationResult {
        result: true,
        reason: record.then(|| self.cycle_reason(key, depth)).flatten(),
      };
    }

    self.in_progress.borrow_mut().insert(key);

    let outcome = match kind {
      RelationKind::Assignable => self.assignable(src, dst, mode, record, depth),
      RelationKind::Comparable => {
        let src_kind = self.store.type_kind(src);
        let dst_kind = self.store.type_kind(dst);
        if matches!(src_kind, TypeKind::TypeParam(_)) || matches!(dst_kind, TypeKind::TypeParam(_)) {
          let res = matches!(
            (&src_kind, &dst_kind),
            (TypeKind::TypeParam(a), TypeKind::TypeParam(b)) if a == b
          );
          RelationResult {
            result: res,
            reason: self.join_reasons(
              record,
              key,
              Vec::new(),
              res,
              Some("type parameter comparable".into()),
              depth,
            ),
          }
        } else {
          let forward = self.assignable(src, dst, mode, record, depth + 1);
          if !forward.result {
            forward
          } else {
            let backward = self.assignable(dst, src, mode, record, depth + 1);
            RelationResult {
              result: backward.result,
              reason: self.join_reasons(
                record,
                key,
                vec![forward.reason, backward.reason],
                backward.result,
                Some("comparable".into()),
                depth,
              ),
            }
          }
        }
      }
      RelationKind::StrictSubtype => {
        let forward = self.assignable(src, dst, mode, record, depth + 1);
        if !forward.result {
          forward
        } else {
          let backward = self.assignable(dst, src, mode, record, depth + 1);
          let res = forward.result && !backward.result;
          RelationResult {
            result: res,
            reason: self.join_reasons(
              record,
              key,
              vec![forward.reason, backward.reason],
              res,
              Some("strict subtype".into()),
              depth,
            ),
          }
        }
      }
    };

    self.cache.insert(key, outcome.result);
    self.in_progress.borrow_mut().remove(&key);
    outcome
  }

  fn cached_reason(&self, key: RelationKey, result: bool, depth: usize) -> Option<ReasonNode> {
    self.join_reasons(true, key, Vec::new(), result, Some("cached".into()), depth)
  }

  fn cycle_reason(&self, key: RelationKey, depth: usize) -> Option<ReasonNode> {
    self.join_reasons(true, key, Vec::new(), true, Some("cycle".into()), depth)
  }

  fn join_reasons(
    &self,
    record: bool,
    key: RelationKey,
    children: Vec<Option<ReasonNode>>,
    outcome: bool,
    note: Option<String>,
    depth: usize,
  ) -> Option<ReasonNode> {
    if !record || !self.take_reason_slot() {
      return None;
    }
    let mut note = note;
    let child_nodes = if depth >= MAX_REASON_DEPTH {
      note.get_or_insert_with(|| "max depth".into());
      Vec::new()
    } else {
      children.into_iter().flatten().collect()
    };
    Some(ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome,
      note,
      children: child_nodes,
    })
  }

  fn reset_reason_budget(&self) {
    *self.reason_budget.borrow_mut() = ReasonBudget::default();
  }

  fn take_reason_slot(&self) -> bool {
    let mut budget = self.reason_budget.borrow_mut();
    if budget.nodes >= MAX_REASON_NODES {
      return false;
    }
    budget.nodes += 1;
    true
  }

  fn assignable(
    &self,
    src: TypeId,
    dst: TypeId,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind: RelationKind::Assignable,
      mode,
    };

    if src == dst {
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          true,
          Some("identical".into()),
          depth,
        ),
      };
    }

    let normalized_src = self.normalize_type(src);
    let normalized_dst = self.normalize_type(dst);
    if normalized_src != src || normalized_dst != dst {
      let related = self.relate_internal(
        normalized_src,
        normalized_dst,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      return RelationResult {
        result: related.result,
        reason: self.join_reasons(
          record,
          key,
          vec![related.reason],
          related.result,
          Some("normalized".into()),
          depth,
        ),
      };
    }

    let src_kind = self.store.type_kind(src);
    let dst_kind = self.store.type_kind(dst);

    if let Some(res) = self.assignable_special(&src_kind, &dst_kind) {
      return RelationResult {
        result: res,
        reason: self.join_reasons(record, key, Vec::new(), res, Some("special".into()), depth),
      };
    }

    if let TypeKind::Ref { def, args } = &src_kind {
      if let Some(expanded) = self.expand_ref(*def, args) {
        let related = self.relate_internal(
          expanded,
          dst,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("expand src".into()),
            depth,
          ),
        };
      }
    }
    if let TypeKind::Ref { def, args } = &dst_kind {
      if let Some(expanded) = self.expand_ref(*def, args) {
        let related = self.relate_internal(
          src,
          expanded,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("expand dst".into()),
            depth,
          ),
        };
      }
    }

    // Unions
    if let TypeKind::Union(srcs) = &src_kind {
      let mut children = Vec::new();
      for member in srcs {
        let related = self.relate_internal(
          *member,
          dst,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("union source".into()),
              depth,
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          children,
          true,
          Some("union source".into()),
          depth,
        ),
      };
    }
    if let TypeKind::Union(dsts) = &dst_kind {
      let mut attempts = Vec::new();
      for member in dsts {
        let related = self.relate_internal(
          src,
          *member,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        let reason = related.reason;
        if record {
          attempts.push(reason.clone());
        }
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![reason],
              true,
              Some("union target".into()),
              depth,
            ),
          };
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          attempts,
          false,
          Some("union target".into()),
          depth,
        ),
      };
    }

    // Intersections
    if let TypeKind::Intersection(dsts) = &dst_kind {
      let mut children = Vec::new();
      for member in dsts {
        let related = self.relate_internal(
          src,
          *member,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("intersection target".into()),
              depth,
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          children,
          true,
          Some("intersection target".into()),
          depth,
        ),
      };
    }

    if let TypeKind::Intersection(srcs) = &src_kind {
      if let TypeKind::Object(dst_obj) = &dst_kind {
        if let Some(merged) = self.merge_intersection(srcs) {
          let related = self.relate_object(src, dst, merged, *dst_obj, mode, record, depth + 1);
          return RelationResult {
            result: related.result,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              related.result,
              Some("intersection merge".into()),
              depth,
            ),
          };
        }
      }

      let mut children = Vec::new();
      for member in srcs {
        let related = self.relate_internal(
          *member,
          dst,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              true,
              Some("intersection source".into()),
              depth,
            ),
          };
        }
        if record {
          children.push(related.reason);
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          children,
          false,
          Some("intersection source".into()),
          depth,
        ),
      };
    }

    match (&src_kind, &dst_kind) {
      (TypeKind::BooleanLiteral(a), TypeKind::BooleanLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (TypeKind::NumberLiteral(a), TypeKind::NumberLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (TypeKind::StringLiteral(a), TypeKind::StringLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (TypeKind::BigIntLiteral(a), TypeKind::BigIntLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into()), depth),
        }
      }
      (
        TypeKind::Array {
          ty: src_elem,
          readonly: src_ro,
        },
        TypeKind::Array {
          ty: dst_elem,
          readonly: dst_ro,
        },
      ) => self.relate_array(
        *src_elem,
        *dst_elem,
        *src_ro,
        *dst_ro,
        key,
        mode,
        record,
        depth + 1,
      ),
      (TypeKind::Array { ty: src_elem, .. }, TypeKind::Object(dst_obj)) => {
        let dst_shape = self.store.shape(self.store.object(*dst_obj).shape);
        if let Some(idx) = dst_shape
          .indexers
          .iter()
          .find(|idx| matches!(self.store.type_kind(idx.key_type), TypeKind::Number))
        {
          let related = self.relate_internal(
            *src_elem,
            idx.value_type,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          let reason = self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("array to object indexer".into()),
            depth,
          );
          return RelationResult {
            result: related.result,
            reason,
          };
        }
        RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            false,
            Some("array to object".into()),
            depth,
          ),
        }
      }
      (TypeKind::Tuple(src_elems), TypeKind::Tuple(dst_elems)) => {
        self.relate_tuple(src_elems, dst_elems, key, mode, record, depth + 1)
      }
      (TypeKind::Array { ty, .. }, TypeKind::Tuple(dst_elems)) => {
        self.relate_array_to_tuple(*ty, dst_elems, key, mode, record, depth + 1)
      }
      (TypeKind::Tuple(src_elems), TypeKind::Array { ty, readonly }) => {
        self.relate_tuple_to_array(src_elems, *ty, *readonly, key, mode, record, depth + 1)
      }
      (TypeKind::Callable { overloads: s }, TypeKind::Callable { overloads: d }) => {
        self.relate_callable(src, dst, s, d, mode, record, depth + 1)
      }
      (TypeKind::Callable { overloads }, TypeKind::Object(obj)) => {
        self.relate_callable_to_object(src, dst, overloads, *obj, key, mode, record, depth + 1)
      }
      (TypeKind::Object(obj), TypeKind::Callable { overloads }) => {
        self.relate_object_to_callable(src, dst, *obj, overloads, key, mode, record, depth + 1)
      }
      (TypeKind::Object(src_obj), TypeKind::Object(dst_obj)) => {
        self.relate_object(src, dst, *src_obj, *dst_obj, mode, record, depth + 1)
      }
      _ => RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("structural".into()),
          depth,
        ),
      },
    }
  }

  fn assignable_special(&self, src: &TypeKind, dst: &TypeKind) -> Option<bool> {
    let opts = &self.options;
    match (src, dst) {
      (TypeKind::TypeParam(a), TypeKind::TypeParam(b)) => Some(a == b),
      // Unresolved type parameters are treated conservatively as `unknown` to
      // avoid spurious incompatibilities during overload checking. They accept
      // any source but are only assignable to top types when used as sources.
      (_, TypeKind::TypeParam(_)) => Some(true),
      (TypeKind::TypeParam(_), _) => Some(matches!(dst, TypeKind::Any | TypeKind::Unknown)),
      (TypeKind::Any, _) | (_, TypeKind::Any) => Some(true),
      (TypeKind::Unknown, TypeKind::Unknown) => Some(true),
      (_, TypeKind::Unknown) => Some(true),
      (TypeKind::Unknown, _) => Some(false),
      (TypeKind::Never, _) => Some(true),
      (_, TypeKind::Never) => Some(matches!(src, TypeKind::Never)),
      (TypeKind::Void, TypeKind::Void) => Some(true),
      (TypeKind::Void, TypeKind::Undefined) | (TypeKind::Undefined, TypeKind::Void) => Some(true),
      (TypeKind::Void, _) => Some(false),
      (TypeKind::Null, _)
      | (TypeKind::Undefined, _)
      | (_, TypeKind::Null)
      | (_, TypeKind::Undefined) => {
        if !opts.strict_null_checks {
          Some(true)
        } else {
          match (src, dst) {
            (TypeKind::Null, TypeKind::Null) => Some(true),
            (TypeKind::Undefined, TypeKind::Undefined) => Some(true),
            (TypeKind::Undefined, TypeKind::Void) => Some(true),
            (TypeKind::Null, TypeKind::Any | TypeKind::Unknown) => Some(true),
            (TypeKind::Undefined, TypeKind::Any | TypeKind::Unknown) => Some(true),
            _ => Some(false),
          }
        }
      }
      (TypeKind::BooleanLiteral(_), TypeKind::Boolean) => Some(true),
      (TypeKind::NumberLiteral(_), TypeKind::Number) => Some(true),
      (TypeKind::StringLiteral(_), TypeKind::String) => Some(true),
      (TypeKind::BigIntLiteral(_), TypeKind::BigInt) => Some(true),
      (TypeKind::TemplateLiteral(_), TypeKind::String) => Some(true),
      (TypeKind::UniqueSymbol, TypeKind::Symbol) => Some(true),
      (TypeKind::Predicate { .. }, TypeKind::Boolean) => Some(true),
      (TypeKind::Boolean, TypeKind::Predicate { .. }) => Some(true),
      (TypeKind::Predicate { .. }, TypeKind::Predicate { .. }) => Some(true),
      _ => None,
    }
  }

  fn relate_array(
    &self,
    src_elem: TypeId,
    dst_elem: TypeId,
    src_readonly: bool,
    dst_readonly: bool,
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    if !dst_readonly && src_readonly {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("readonly array".into()),
          depth,
        ),
      };
    }
    let related = self.relate_internal(
      src_elem,
      dst_elem,
      RelationKind::Assignable,
      mode,
      record,
      depth + 1,
    );
    RelationResult {
      result: related.result,
      reason: self.join_reasons(
        record,
        key,
        vec![related.reason],
        related.result,
        Some("array element".into()),
        depth,
      ),
    }
  }

  fn relate_array_to_tuple(
    &self,
    src_elem: TypeId,
    dst_elems: &[crate::TupleElem],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let mut children = Vec::new();
    for dst_elem in dst_elems {
      let dst_ty = self.optional_type(dst_elem.ty, dst_elem.optional, OptionalFlavor::TupleElement);
      let related = self.relate_internal(
        src_elem,
        dst_ty,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("array to tuple".into()),
            depth,
          ),
        };
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(
        record,
        key,
        children,
        true,
        Some("array to tuple".into()),
        depth,
      ),
    }
  }

  fn relate_tuple_to_array(
    &self,
    src_elems: &[crate::TupleElem],
    dst_elem: TypeId,
    dst_readonly: bool,
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    if !dst_readonly && src_elems.iter().any(|e| e.readonly) {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("tuple readonly element".into()),
          depth,
        ),
      };
    }
    let mut children = Vec::new();
    for src_elem in src_elems {
      let src_ty = self.optional_type(src_elem.ty, src_elem.optional, OptionalFlavor::TupleElement);
      let related = self.relate_internal(
        src_ty,
        dst_elem,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("tuple to array".into()),
            depth,
          ),
        };
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(
        record,
        key,
        children,
        true,
        Some("tuple to array".into()),
        depth,
      ),
    }
  }

  fn relate_tuple(
    &self,
    src_elems: &[crate::TupleElem],
    dst_elems: &[crate::TupleElem],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let mut children = Vec::new();
    let src_required = src_elems.iter().filter(|e| !e.optional && !e.rest).count();
    let dst_required = dst_elems.iter().filter(|e| !e.optional && !e.rest).count();

    if src_required > dst_elems.len()
      && !src_elems.iter().any(|e| e.rest)
      && dst_required == dst_elems.len()
    {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("tuple arity".into()),
          depth,
        ),
      };
    }

    if dst_required > src_elems.len() && !src_elems.iter().any(|e| e.rest) {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("tuple required elements".into()),
          depth,
        ),
      };
    }

    let mut s_idx = 0usize;
    let mut d_idx = 0usize;
    while d_idx < dst_elems.len() {
      let dst_elem = &dst_elems[d_idx];
      let src_elem = src_elems.get(s_idx);
      match src_elem {
        None => {
          if dst_elem.rest || dst_elem.optional {
            d_idx += 1;
            continue;
          }
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("tuple length".into()),
              depth,
            ),
          };
        }
        Some(src_elem) => {
          if dst_elem.rest {
            for rem in src_elems.iter().skip(s_idx) {
              let src_ty = self.optional_type(
                rem.ty,
                rem.optional || rem.rest,
                OptionalFlavor::TupleElement,
              );
              let dst_ty = self.optional_type(
                dst_elem.ty,
                dst_elem.optional || dst_elem.rest,
                OptionalFlavor::TupleElement,
              );
              if !dst_elem.readonly && rem.readonly {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple readonly".into()),
                    depth,
                  ),
                };
              }
              let related = self.relate_internal(
                src_ty,
                dst_ty,
                RelationKind::Assignable,
                mode,
                record,
                depth + 1,
              );
              if record {
                children.push(related.reason);
              }
              if !related.result {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple rest".into()),
                    depth,
                  ),
                };
              }
            }
            return RelationResult {
              result: true,
              reason: self.join_reasons(
                record,
                key,
                children,
                true,
                Some("tuple rest".into()),
                depth,
              ),
            };
          }

          if src_elem.rest {
            let src_ty = self.optional_type(
              src_elem.ty,
              src_elem.optional || src_elem.rest,
              OptionalFlavor::TupleElement,
            );
            for d in dst_elems.iter().skip(d_idx) {
              if !d.readonly && src_elem.readonly {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple rest readonly".into()),
                    depth,
                  ),
                };
              }
              let dst_ty =
                self.optional_type(d.ty, d.optional || d.rest, OptionalFlavor::TupleElement);
              let related = self.relate_internal(
                src_ty,
                dst_ty,
                RelationKind::Assignable,
                mode,
                record,
                depth + 1,
              );
              if record {
                children.push(related.reason);
              }
              if !related.result {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple rest spread".into()),
                    depth,
                  ),
                };
              }
            }
            return RelationResult {
              result: true,
              reason: self.join_reasons(
                record,
                key,
                children,
                true,
                Some("tuple rest spread".into()),
                depth,
              ),
            };
          }

          if !dst_elem.optional && src_elem.optional {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("tuple optional".into()),
                depth,
              ),
            };
          }
          if !dst_elem.readonly && src_elem.readonly {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("tuple readonly".into()),
                depth,
              ),
            };
          }
          let src_ty =
            self.optional_type(src_elem.ty, src_elem.optional, OptionalFlavor::TupleElement);
          let dst_ty =
            self.optional_type(dst_elem.ty, dst_elem.optional, OptionalFlavor::TupleElement);
          let related = self.relate_internal(
            src_ty,
            dst_ty,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("tuple element".into()),
                depth,
              ),
            };
          }
        }
      }

      s_idx += 1;
      d_idx += 1;
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("tuple".into()), depth),
    }
  }

  fn relate_callable(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_overloads: &[SignatureId],
    dst_overloads: &[SignatureId],
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children = Vec::new();
    for dst_sig in dst_overloads {
      let dst_sig_data = self.store.signature(*dst_sig);
      let mut matched = None;
      for src_sig in src_overloads {
        let src_sig_data = self.store.signature(*src_sig);
        let related = self.relate_signature(
          *src_sig,
          *dst_sig,
          &src_sig_data,
          &dst_sig_data,
          mode,
          record,
          depth + 1,
        );
        if related.result {
          matched = Some(related.reason);
          break;
        }
        if record {
          children.push(related.reason);
        }
      }
      if matched.is_none() {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("call signature".into()),
            depth,
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("callable".into()), depth),
    }
  }

  fn relate_callable_to_object(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    overloads: &[SignatureId],
    dst_obj: ObjectId,
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let dst_shape = self.store.shape(self.store.object(dst_obj).shape);
    if !dst_shape.properties.is_empty()
      || !dst_shape.construct_signatures.is_empty()
      || !dst_shape.indexers.is_empty()
    {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("callable to object".into()),
          depth,
        ),
      };
    }
    self.relate_callable(
      src_id,
      dst_id,
      overloads,
      &dst_shape.call_signatures,
      mode | RelationMode::BIVARIANT_PARAMS,
      record,
      depth + 1,
    )
  }

  fn relate_object_to_callable(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_obj: ObjectId,
    overloads: &[SignatureId],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let src_shape = self.store.shape(self.store.object(src_obj).shape);
    if !src_shape.properties.is_empty()
      || !src_shape.construct_signatures.is_empty()
      || !src_shape.indexers.is_empty()
    {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("object to callable".into()),
          depth,
        ),
      };
    }
    self.relate_callable(
      src_id,
      dst_id,
      &src_shape.call_signatures,
      overloads,
      mode | RelationMode::BIVARIANT_PARAMS,
      record,
      depth + 1,
    )
  }

  fn relate_signature(
    &self,
    src_id: SignatureId,
    dst_id: SignatureId,
    src: &Signature,
    dst: &Signature,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src: TypeId(src_id.0),
      dst: TypeId(dst_id.0),
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children = Vec::new();
    let allow_bivariance =
      !self.options.strict_function_types || mode.contains(RelationMode::BIVARIANT_PARAMS);

    if src.type_params.len() != dst.type_params.len() {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("type parameters".into()),
          depth,
        ),
      };
    }

    match (&src.this_param, &dst.this_param) {
      (Some(s), Some(d)) => {
        let related =
          self.relate_internal(*d, *s, RelationKind::Assignable, mode, record, depth + 1);
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("this parameter".into()),
              depth,
            ),
          };
        }
      }
      (Some(_), None) => {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("this parameter".into()),
            depth,
          ),
        }
      }
      (None, Some(_)) => {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            Vec::new(),
            false,
            Some("missing this".into()),
            depth,
          ),
        }
      }
      _ => {}
    }

    let src_required = src.params.iter().filter(|p| !p.optional && !p.rest).count();
    let dst_required = dst.params.iter().filter(|p| !p.optional && !p.rest).count();
    if src_required > dst_required {
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          false,
          Some("parameter count".into()),
          depth,
        ),
      };
    }

    let paired = src.params.iter().zip(dst.params.iter());
    for (s_param, d_param) in paired {
      if !d_param.optional && s_param.optional {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("optional parameter".into()),
            depth,
          ),
        };
      }
      let s_ty = self.optional_type(s_param.ty, s_param.optional, OptionalFlavor::Parameter);
      let d_ty = self.optional_type(d_param.ty, d_param.optional, OptionalFlavor::Parameter);
      let related = if allow_bivariance {
        let forward = self.relate_internal(
          s_ty,
          d_ty,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if forward.result {
          forward
        } else {
          self.relate_internal(
            d_ty,
            s_ty,
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          )
        }
      } else {
        self.relate_internal(
          d_ty,
          s_ty,
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        )
      };
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("parameter".into()),
            depth,
          ),
        };
      }
    }

    if dst.params.len() > src.params.len() {
      if let Some(rest) = src.params.iter().find(|p| p.rest) {
        let rest_ty = self.optional_type(rest.ty, rest.optional, OptionalFlavor::Parameter);
        for extra in dst.params.iter().skip(src.params.len()) {
          if !extra.optional && !rest.rest {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("rest coverage".into()),
                depth,
              ),
            };
          }
          let extra_ty = self.optional_type(extra.ty, extra.optional, OptionalFlavor::Parameter);
          let related = if allow_bivariance {
            let forward = self.relate_internal(
              rest_ty,
              extra_ty,
              RelationKind::Assignable,
              mode,
              record,
              depth + 1,
            );
            if forward.result {
              forward
            } else {
              self.relate_internal(
                extra_ty,
                rest_ty,
                RelationKind::Assignable,
                mode,
                record,
                depth + 1,
              )
            }
          } else {
            self.relate_internal(
              extra_ty,
              rest_ty,
              RelationKind::Assignable,
              mode,
              record,
              depth + 1,
            )
          };
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("rest parameter".into()),
                depth,
              ),
            };
          }
        }
      } else {
        for extra in dst.params.iter().skip(src.params.len()) {
          if !extra.optional {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("parameter count".into()),
                depth,
              ),
            };
          }
        }
      }
    }

    let ret_related = self.relate_internal(
      src.ret,
      dst.ret,
      RelationKind::Assignable,
      mode,
      record,
      depth + 1,
    );
    if record {
      children.push(ret_related.reason);
    }
    if !ret_related.result {
      return RelationResult {
        result: false,
        reason: self.join_reasons(record, key, children, false, Some("return".into()), depth),
      };
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("signature".into()), depth),
    }
  }

  fn merge_intersection(&self, members: &[TypeId]) -> Option<ObjectId> {
    let mut shape = Shape::new();
    for member in members {
      match self.store.type_kind(*member) {
        TypeKind::Object(obj) => {
          let obj = self.store.object(obj);
          let obj_shape = self.store.shape(obj.shape);
          shape.properties.extend(obj_shape.properties.clone());
          shape.indexers.extend(obj_shape.indexers.clone());
          shape
            .call_signatures
            .extend(obj_shape.call_signatures.clone());
          shape
            .construct_signatures
            .extend(obj_shape.construct_signatures.clone());
        }
        _ => return None,
      }
    }
    let shape_id = self.store.intern_shape(shape);
    Some(
      self
        .store
        .intern_object(crate::ObjectType { shape: shape_id }),
    )
  }

  fn optional_type(&self, ty: TypeId, optional: bool, flavor: OptionalFlavor) -> TypeId {
    if !optional && !matches!(flavor, OptionalFlavor::IndexerValue) {
      return ty;
    }

    let include_undefined = match flavor {
      OptionalFlavor::Property => !self.options.exact_optional_property_types && optional,
      OptionalFlavor::Parameter | OptionalFlavor::TupleElement => optional,
      OptionalFlavor::IndexerValue => optional || self.options.no_unchecked_indexed_access,
    };

    if include_undefined {
      self
        .store
        .union(vec![ty, self.store.primitive_ids().undefined])
    } else {
      ty
    }
  }

  fn normalize_type(&self, ty: TypeId) -> TypeId {
    let adapter = RelateExpanderAdapter {
      hook: self.hooks.expander,
    };
    let mut evaluator = TypeEvaluator::new(self.store.clone(), &adapter);
    evaluator.evaluate(ty)
  }

  fn is_method_like(&self, data: &PropData) -> bool {
    data.is_method
  }

  fn relate_object(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_obj: ObjectId,
    dst_obj: ObjectId,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children: Vec<Option<ReasonNode>> = Vec::new();

    let src_shape = self.store.shape(self.store.object(src_obj).shape);
    let dst_shape = self.store.shape(self.store.object(dst_obj).shape);

    for dst_prop in &dst_shape.properties {
      match self.find_property(&src_shape, &dst_prop.key) {
        Some(src_prop) => {
          if !self.private_compatible(src_prop, dst_prop) {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("private/protected property".into()),
                depth,
              ),
            };
          }
          if !dst_prop.data.readonly && src_prop.data.readonly {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("readonly property".into()),
                depth,
              ),
            };
          }

          if !dst_prop.data.optional && src_prop.data.optional {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("missing required property".into()),
                depth,
              ),
            };
          }

          let next_mode =
            if self.is_method_like(&src_prop.data) || self.is_method_like(&dst_prop.data) {
              mode | RelationMode::BIVARIANT_PARAMS
            } else {
              mode
            };
          let src_ty = self.optional_type(
            src_prop.data.ty,
            src_prop.data.optional,
            OptionalFlavor::Property,
          );
          let dst_ty = self.optional_type(
            dst_prop.data.ty,
            dst_prop.data.optional,
            OptionalFlavor::Property,
          );
          let related = self.relate_internal(
            src_ty,
            dst_ty,
            RelationKind::Assignable,
            next_mode,
            record,
            depth + 1,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("property type".into()),
                depth,
              ),
            };
          }
        }
        None => {
          if dst_prop.data.optional {
            continue;
          }
          if let Some(index) = self.indexer_for_prop(&src_shape, &dst_prop.key) {
            if !dst_prop.data.readonly && index.readonly {
              return RelationResult {
                result: false,
                reason: self.join_reasons(
                  record,
                  key,
                  children,
                  false,
                  Some("indexer readonly".into()),
                  depth,
                ),
              };
            }
            let related = self.relate_internal(
              self.optional_type(index.value_type, false, OptionalFlavor::IndexerValue),
              self.optional_type(
                dst_prop.data.ty,
                dst_prop.data.optional,
                OptionalFlavor::Property,
              ),
              RelationKind::Assignable,
              mode,
              record,
              depth + 1,
            );
            if record {
              children.push(related.reason);
            }
            if !related.result {
              return RelationResult {
                result: false,
                reason: self.join_reasons(
                  record,
                  key,
                  children,
                  false,
                  Some("indexer property".into()),
                  depth,
                ),
              };
            }
          } else {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("missing property".into()),
                depth,
              ),
            };
          }
        }
      }
    }

    for dst_index in &dst_shape.indexers {
      if let Some(src_idx) =
        self.find_matching_indexer(&src_shape, dst_index, mode, record, depth + 1)
      {
        if !dst_index.readonly && src_idx.readonly {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("readonly indexer".into()),
              depth,
            ),
          };
        }
        let related = self.relate_internal(
          self.optional_type(src_idx.value_type, false, OptionalFlavor::IndexerValue),
          self.optional_type(dst_index.value_type, false, OptionalFlavor::IndexerValue),
          RelationKind::Assignable,
          mode,
          record,
          depth + 1,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(record, key, children, false, Some("indexer".into()), depth),
          };
        }
      } else {
        for prop in &src_shape.properties {
          if !self.indexer_accepts_prop(dst_index, &prop.key) {
            continue;
          }
          let related = self.relate_internal(
            self.optional_type(prop.data.ty, prop.data.optional, OptionalFlavor::Property),
            self.optional_type(dst_index.value_type, false, OptionalFlavor::IndexerValue),
            RelationKind::Assignable,
            mode,
            record,
            depth + 1,
          );
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some("property vs indexer".into()),
                depth,
              ),
            };
          }
        }
      }
    }

    for dst_sig in &dst_shape.call_signatures {
      let dst_sig_data = self.store.signature(*dst_sig);
      let mut matched = None;
      for src_sig in &src_shape.call_signatures {
        let src_sig_data = self.store.signature(*src_sig);
        let related = self.relate_signature(
          *src_sig,
          *dst_sig,
          &src_sig_data,
          &dst_sig_data,
          mode | RelationMode::BIVARIANT_PARAMS,
          record,
          depth + 1,
        );
        if related.result {
          matched = Some(related.reason);
          break;
        }
        if record {
          children.push(related.reason);
        }
      }
      if matched.is_none() {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("call signature".into()),
            depth,
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }

    for dst_sig in &dst_shape.construct_signatures {
      let dst_sig_data = self.store.signature(*dst_sig);
      let mut matched = None;
      for src_sig in &src_shape.construct_signatures {
        let src_sig_data = self.store.signature(*src_sig);
        let related = self.relate_signature(
          *src_sig,
          *dst_sig,
          &src_sig_data,
          &dst_sig_data,
          mode | RelationMode::BIVARIANT_PARAMS,
          record,
          depth + 1,
        );
        if related.result {
          matched = Some(related.reason);
          break;
        }
        if record {
          children.push(related.reason);
        }
      }
      if matched.is_none() {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("construct signature".into()),
            depth,
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("object".into()), depth),
    }
  }

  fn private_compatible(&self, src: &Property, dst: &Property) -> bool {
    let src_access = src
      .data
      .accessibility
      .as_ref()
      .cloned()
      .unwrap_or(Accessibility::Public);
    let dst_access = dst
      .data
      .accessibility
      .as_ref()
      .cloned()
      .unwrap_or(Accessibility::Public);
    match (src_access, dst_access) {
      (Accessibility::Public, Accessibility::Public) => true,
      (Accessibility::Public, _) | (_, Accessibility::Public) => false,
      (a, b) if a != b => false,
      _ => self
        .hooks
        .is_same_origin_private_member
        .map(|cb| cb(src, dst))
        .unwrap_or(false),
    }
  }

  fn indexer_for_prop<'b>(&self, shape: &'b Shape, name: &PropKey) -> Option<&'b Indexer> {
    let key_ty = self.prop_key_type(name);
    shape
      .indexers
      .iter()
      .find(|idx| self.is_assignable(key_ty, idx.key_type))
  }

  fn indexer_accepts_prop(&self, idx: &Indexer, key: &PropKey) -> bool {
    let key_ty = self.prop_key_type(key);
    self.is_assignable(key_ty, idx.key_type)
  }

  fn find_matching_indexer<'b>(
    &self,
    shape: &'b Shape,
    dst: &Indexer,
    mode: RelationMode,
    record: bool,
    depth: usize,
  ) -> Option<&'b Indexer> {
    shape.indexers.iter().find(|src_idx| {
      let key_related = self.relate_internal(
        dst.key_type,
        src_idx.key_type,
        RelationKind::Assignable,
        mode,
        record,
        depth + 1,
      );
      key_related.result
    })
  }

  fn prop_key_type(&self, key: &PropKey) -> TypeId {
    let prim = self.store.primitive_ids();
    match key {
      PropKey::String(_) => prim.string,
      PropKey::Number(_) => prim.number,
      PropKey::Symbol(_) => prim.symbol,
    }
  }

  fn find_property<'b>(&self, shape: &'b Shape, key: &PropKey) -> Option<&'b Property> {
    shape
      .properties
      .binary_search_by(|p| p.key.cmp_with(key, &|id| self.store.name(id)))
      .ok()
      .map(|idx| &shape.properties[idx])
  }

  fn expand_ref(&self, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    self
      .hooks
      .expander
      .and_then(|expander| expander.expand_ref(self.store.as_ref(), def, args))
  }
}
