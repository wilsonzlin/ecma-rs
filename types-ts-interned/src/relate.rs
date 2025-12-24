use crate::ids::DefId;
use crate::ids::TypeId;
use crate::kind::TypeKind;
use crate::shape::Accessibility;
use crate::shape::Indexer;
use crate::shape::PropData;
use crate::shape::PropKey;
use crate::shape::Property;
use crate::shape::Shape;
use crate::signature::Signature;
use crate::store::TypeStore;
use crate::TypeOptions;
use bitflags::bitflags;
use std::cell::RefCell;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum RelationKind {
  Assignable,
  Comparable,
  StrictSubtype,
}

bitflags! {
  #[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
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

pub struct RelateHooks<'a> {
  pub expander: Option<&'a dyn TypeExpander>,
  pub is_same_origin_private_member: Option<&'a dyn Fn(&Property, &Property) -> bool>,
}

impl Default for RelateHooks<'_> {
  fn default() -> Self {
    Self {
      expander: None,
      is_same_origin_private_member: None,
    }
  }
}

impl std::fmt::Debug for RelateHooks<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("RelateHooks")
      .field("expander", &self.expander.as_ref().map(|_| "TypeExpander"))
      .field(
        "is_same_origin_private_member",
        &self.is_same_origin_private_member.as_ref().map(|_| "Fn"),
      )
      .finish()
  }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
struct RelationKey {
  src: TypeId,
  dst: TypeId,
  kind: RelationKind,
  mode: RelationMode,
}

pub trait TypeExpander {
  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId>;
}

pub struct RelateCtx<'a> {
  store: Arc<TypeStore>,
  pub options: TypeOptions,
  hooks: RelateHooks<'a>,
  cache: RefCell<HashMap<RelationKey, bool>>,
  in_progress: RefCell<HashSet<RelationKey>>,
}

impl std::fmt::Debug for RelateCtx<'_> {
  fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    f.debug_struct("RelateCtx")
      .field("options", &self.options)
      .finish_non_exhaustive()
  }
}

impl<'a> RelateCtx<'a> {
  pub fn new(store: Arc<TypeStore>) -> Self {
    let options = store.options();
    Self::with_options(store, options)
  }

  pub fn with_options(store: Arc<TypeStore>, options: TypeOptions) -> Self {
    Self::with_hooks(store, options, RelateHooks::default())
  }

  pub fn with_hooks(store: Arc<TypeStore>, options: TypeOptions, hooks: RelateHooks<'a>) -> Self {
    Self {
      store,
      options,
      hooks,
      cache: RefCell::new(HashMap::new()),
      in_progress: RefCell::new(HashSet::new()),
    }
  }

  pub fn is_assignable(&self, src: TypeId, dst: TypeId) -> bool {
    self
      .relate_internal(
        src,
        dst,
        RelationKind::Assignable,
        RelationMode::NONE,
        false,
      )
      .result
  }

  pub fn is_comparable(&self, a: TypeId, b: TypeId) -> bool {
    self
      .relate_internal(a, b, RelationKind::Comparable, RelationMode::NONE, false)
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
      )
      .result
  }

  pub fn explain_assignable(&self, src: TypeId, dst: TypeId) -> RelationResult {
    self.relate_internal(src, dst, RelationKind::Assignable, RelationMode::NONE, true)
  }

  fn relate_internal(
    &self,
    src: TypeId,
    dst: TypeId,
    kind: RelationKind,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind,
      mode,
    };
    if let Some(hit) = self.cache.borrow().get(&key).copied() {
      return RelationResult {
        result: hit,
        reason: record.then(|| self.cached_reason(key, hit)),
      };
    }
    if self.in_progress.borrow().contains(&key) {
      return RelationResult {
        result: true,
        reason: record.then(|| self.cycle_reason(key)),
      };
    }

    self.in_progress.borrow_mut().insert(key);

    let outcome = match kind {
      RelationKind::Assignable => self.assignable(src, dst, mode, record),
      RelationKind::Comparable => {
        let left = self.assignable(src, dst, mode, record);
        if !left.result {
          left
        } else {
          let right = self.assignable(dst, src, mode, record);
          RelationResult {
            result: right.result,
            reason: self.join_reasons(
              record,
              key,
              vec![left.reason, right.reason],
              right.result,
              None,
            ),
          }
        }
      }
      RelationKind::StrictSubtype => {
        let forward = self.assignable(src, dst, mode, record);
        if !forward.result {
          forward
        } else {
          let backward = self.assignable(dst, src, mode, record);
          let res = forward.result && !backward.result;
          RelationResult {
            result: res,
            reason: self.join_reasons(
              record,
              key,
              vec![forward.reason, backward.reason],
              res,
              Some("strict subtype".into()),
            ),
          }
        }
      }
    };

    self.cache.borrow_mut().insert(key, outcome.result);
    self.in_progress.borrow_mut().remove(&key);
    outcome
  }

  fn cached_reason(&self, key: RelationKey, result: bool) -> ReasonNode {
    ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome: result,
      note: Some("cached".into()),
      children: Vec::new(),
    }
  }

  fn cycle_reason(&self, key: RelationKey) -> ReasonNode {
    ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome: true,
      note: Some("cycle".into()),
      children: Vec::new(),
    }
  }

  fn join_reasons(
    &self,
    record: bool,
    key: RelationKey,
    children: Vec<Option<ReasonNode>>,
    outcome: bool,
    note: Option<String>,
  ) -> Option<ReasonNode> {
    record.then(|| ReasonNode {
      src: key.src,
      dst: key.dst,
      relation: key.kind,
      outcome,
      note,
      children: children.into_iter().flatten().collect(),
    })
  }

  fn assignable(
    &self,
    src: TypeId,
    dst: TypeId,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src,
      dst,
      kind: RelationKind::Assignable,
      mode,
    };

    let mut reason_children: Vec<Option<ReasonNode>> = Vec::new();

    if src == dst {
      return RelationResult {
        result: true,
        reason: self.join_reasons(record, key, Vec::new(), true, Some("identical".into())),
      };
    }

    let src_kind = self.store.type_kind(src);
    let dst_kind = self.store.type_kind(dst);

    if let Some(res) = self.assignable_special(&src_kind, &dst_kind) {
      return RelationResult {
        result: res,
        reason: self.join_reasons(record, key, Vec::new(), res, Some("special".into())),
      };
    }

    if let TypeKind::Ref { def, args } = &src_kind {
      if let Some(expanded) = self.expand_ref(*def, args) {
        let related = self.relate_internal(expanded, dst, RelationKind::Assignable, mode, record);
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("expand src".into()),
          ),
        };
      }
    }
    if let TypeKind::Ref { def, args } = &dst_kind {
      if let Some(expanded) = self.expand_ref(*def, args) {
        let related = self.relate_internal(src, expanded, RelationKind::Assignable, mode, record);
        return RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("expand dst".into()),
          ),
        };
      }
    }

    if let TypeKind::Union(srcs) = &src_kind {
      for member in srcs {
        let related = self.relate_internal(*member, dst, RelationKind::Assignable, mode, record);
        if record {
          reason_children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              reason_children,
              false,
              Some("union source".into()),
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          reason_children,
          true,
          Some("union source".into()),
        ),
      };
    }
    if let TypeKind::Union(dsts) = &dst_kind {
      for member in dsts {
        let related = self.relate_internal(src, *member, RelationKind::Assignable, mode, record);
        let reason = related.reason;
        if record {
          reason_children.push(reason.clone());
        }
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(record, key, vec![reason], true, Some("union target".into())),
          };
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          reason_children,
          false,
          Some("union target".into()),
        ),
      };
    }

    if let TypeKind::Intersection(dsts) = &dst_kind {
      for member in dsts {
        let related = self.relate_internal(src, *member, RelationKind::Assignable, mode, record);
        if record {
          reason_children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              reason_children,
              false,
              Some("intersection target".into()),
            ),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          reason_children,
          true,
          Some("intersection target".into()),
        ),
      };
    }

    if let TypeKind::Intersection(srcs) = &src_kind {
      if let TypeKind::Object(dst_obj) = &dst_kind {
        if let Some(merged) = self.merge_intersection(srcs) {
          let related = self.relate_object_shapes(
            src,
            dst,
            &merged,
            &self.object_shape(*dst_obj),
            mode,
            record,
          );
          return RelationResult {
            result: related.result,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              related.result,
              Some("intersection merge".into()),
            ),
          };
        }
      }
      for member in srcs {
        let related = self.relate_internal(*member, dst, RelationKind::Assignable, mode, record);
        if related.result {
          return RelationResult {
            result: true,
            reason: self.join_reasons(
              record,
              key,
              vec![related.reason],
              true,
              Some("intersection source".into()),
            ),
          };
        }
        if record {
          reason_children.push(related.reason);
        }
      }
      return RelationResult {
        result: false,
        reason: self.join_reasons(
          record,
          key,
          reason_children,
          false,
          Some("intersection source".into()),
        ),
      };
    }

    match (&src_kind, &dst_kind) {
      (TypeKind::BooleanLiteral(a), TypeKind::BooleanLiteral(b)) => RelationResult {
        result: a == b,
        reason: self.join_reasons(record, key, Vec::new(), a == b, Some("literal".into())),
      },
      (TypeKind::NumberLiteral(a), TypeKind::NumberLiteral(b)) => RelationResult {
        result: a == b,
        reason: self.join_reasons(record, key, Vec::new(), a == b, Some("literal".into())),
      },
      (TypeKind::StringLiteral(a), TypeKind::StringLiteral(b)) => RelationResult {
        result: a == b,
        reason: self.join_reasons(record, key, Vec::new(), a == b, Some("literal".into())),
      },
      (TypeKind::BigIntLiteral(a), TypeKind::BigIntLiteral(b)) => RelationResult {
        result: a == b,
        reason: self.join_reasons(record, key, Vec::new(), a == b, Some("literal".into())),
      },
      (TypeKind::BooleanLiteral(_), TypeKind::Boolean)
      | (TypeKind::NumberLiteral(_), TypeKind::Number)
      | (TypeKind::StringLiteral(_), TypeKind::String)
      | (TypeKind::BigIntLiteral(_), TypeKind::BigInt) => RelationResult {
        result: true,
        reason: self.join_reasons(
          record,
          key,
          Vec::new(),
          true,
          Some("literal widening".into()),
        ),
      },
      (TypeKind::UniqueSymbol, TypeKind::Symbol) => RelationResult {
        result: true,
        reason: self.join_reasons(record, key, Vec::new(), true, Some("unique symbol".into())),
      },
      (TypeKind::Callable { overloads: src_ol }, TypeKind::Callable { overloads: dst_ol }) => {
        let related = self.relate_callable(src, dst, src_ol, dst_ol, mode, record, false);
        RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("callable".into()),
          ),
        }
      }
      (
        TypeKind::Array {
          ty: a,
          readonly: ar,
        },
        TypeKind::Array {
          ty: b,
          readonly: br,
        },
      ) => {
        let allow = !br || ar == br;
        if !allow {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              Vec::new(),
              false,
              Some("array readonly".into()),
            ),
          };
        }
        let related = self.relate_internal(*a, *b, RelationKind::Assignable, mode, record);
        RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("array element".into()),
          ),
        }
      }
      (TypeKind::Tuple(a_elems), TypeKind::Tuple(b_elems)) => {
        let related = self.relate_tuple(src, dst, a_elems, b_elems, mode, record);
        RelationResult {
          result: related.result,
          reason: self.join_reasons(
            record,
            key,
            vec![related.reason],
            related.result,
            Some("tuple".into()),
          ),
        }
      }
      (TypeKind::Object(src_obj), TypeKind::Object(dst_obj)) => self.relate_object_shapes(
        src,
        dst,
        &self.object_shape(*src_obj),
        &self.object_shape(*dst_obj),
        mode,
        record,
      ),
      _ => RelationResult {
        result: false,
        reason: self.join_reasons(record, key, Vec::new(), false, Some("structural".into())),
      },
    }
  }

  fn merge_intersection(&self, members: &[TypeId]) -> Option<Shape> {
    let mut merged = Shape::new();
    for member in members {
      match self.store.type_kind(*member) {
        TypeKind::Object(obj) => {
          let shape = self.object_shape(obj);
          for prop in shape.properties.iter() {
            if !merged.properties.iter().any(|p| p.key == prop.key) {
              merged.properties.push(prop.clone());
            }
          }
          for idx in shape.indexers.iter() {
            if !merged.indexers.iter().any(|p| p == idx) {
              merged.indexers.push(idx.clone());
            }
          }
          for sig in shape.call_signatures.iter() {
            if !merged.call_signatures.contains(sig) {
              merged.call_signatures.push(*sig);
            }
          }
          for sig in shape.construct_signatures.iter() {
            if !merged.construct_signatures.contains(sig) {
              merged.construct_signatures.push(*sig);
            }
          }
        }
        _ => return None,
      }
    }

    let shape_id = self.store.intern_shape(merged);
    Some(self.store.shape(shape_id))
  }

  fn assignable_special(&self, src: &TypeKind, dst: &TypeKind) -> Option<bool> {
    let opts = &self.options;
    match (src, dst) {
      (TypeKind::Any, _) | (_, TypeKind::Any) => Some(true),
      (TypeKind::Unknown, TypeKind::Unknown) => Some(true),
      (_, TypeKind::Unknown) => Some(true),
      (TypeKind::Unknown, _) => Some(false),
      (TypeKind::Never, _) => Some(true),
      (_, TypeKind::Never) => Some(matches!(src, TypeKind::Never)),
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
            (TypeKind::Null, TypeKind::Any | TypeKind::Unknown) => Some(true),
            (TypeKind::Undefined, TypeKind::Any | TypeKind::Unknown | TypeKind::Void) => Some(true),
            (TypeKind::Void, TypeKind::Undefined) => Some(true),
            _ => Some(false),
          }
        }
      }
      (TypeKind::Void, TypeKind::Void) => Some(true),
      _ => None,
    }
  }

  fn relate_object_shapes(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src: &Shape,
    dst: &Shape,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children: Vec<Option<ReasonNode>> = Vec::new();

    for dst_prop in &dst.properties {
      match self.find_property(src, &dst_prop.key) {
        Some(src_prop) => {
          if !self.private_compatible(&src_prop.data, &dst_prop.data, src_prop, dst_prop) {
            return RelationResult {
              result: false,
              reason: self.join_reasons(
                record,
                key,
                children,
                false,
                Some(format!(
                  "private/protected {}",
                  self.prop_name(&dst_prop.key)
                )),
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
                Some(format!(
                  "missing required {}",
                  self.prop_name(&dst_prop.key)
                )),
              ),
            };
          }

          let next_mode = if src_prop.data.is_method || dst_prop.data.is_method {
            mode | RelationMode::BIVARIANT_PARAMS
          } else {
            mode
          };
          let related = self.relate_internal(
            src_prop.data.ty,
            dst_prop.data.ty,
            RelationKind::Assignable,
            next_mode,
            record,
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
                Some(format!("property {}", self.prop_name(&dst_prop.key))),
              ),
            };
          }
        }
        None => {
          if dst_prop.data.optional {
            continue;
          }
          if let Some(index) = self.index_for_prop(src, &dst_prop.key) {
            let related = self.relate_internal(
              index.value_type,
              dst_prop.data.ty,
              RelationKind::Assignable,
              mode,
              record,
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
                  Some(format!("index {}", self.prop_name(&dst_prop.key))),
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
                Some(format!(
                  "missing property {}",
                  self.prop_name(&dst_prop.key)
                )),
              ),
            };
          }
        }
      }
    }

    for dst_index in &dst.indexers {
      if let Some(src_idx) = self.find_matching_indexer(src, dst_index, mode) {
        let related = self.relate_internal(
          src_idx.value_type,
          dst_index.value_type,
          RelationKind::Assignable,
          mode,
          record,
        );
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(record, key, children, false, Some("index signature".into())),
          };
        }
      } else {
        for prop in &src.properties {
          if self.indexer_covers_property(dst_index, &prop.key, mode) {
            let related = self.relate_internal(
              prop.data.ty,
              dst_index.value_type,
              RelationKind::Assignable,
              mode,
              record,
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
                  Some("property vs index".into()),
                ),
              };
            }
          }
        }
      }
    }

    for dst_sig in &dst.call_signatures {
      let mut matched = false;
      for src_sig in &src.call_signatures {
        let related = self.relate_signature(
          key,
          &self.store.signature(*src_sig),
          &self.store.signature(*dst_sig),
          mode,
          record,
          false,
        );
        if record {
          children.push(related.reason);
        }
        if related.result {
          matched = true;
          break;
        }
      }
      if !matched {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("call signature".into())),
        };
      }
    }

    for dst_sig in &dst.construct_signatures {
      let mut matched = false;
      for src_sig in &src.construct_signatures {
        let related = self.relate_signature(
          key,
          &self.store.signature(*src_sig),
          &self.store.signature(*dst_sig),
          mode,
          record,
          false,
        );
        if record {
          children.push(related.reason);
        }
        if related.result {
          matched = true;
          break;
        }
      }
      if !matched {
        return RelationResult {
          result: false,
          reason: self.join_reasons(
            record,
            key,
            children,
            false,
            Some("construct signature".into()),
          ),
        };
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("object".into())),
    }
  }

  fn private_compatible(
    &self,
    src: &PropData,
    dst: &PropData,
    src_prop: &Property,
    dst_prop: &Property,
  ) -> bool {
    let src_acc = self.access(src);
    let dst_acc = self.access(dst);
    match (src_acc, dst_acc) {
      (Accessibility::Public, Accessibility::Public) => true,
      (Accessibility::Public, _) | (_, Accessibility::Public) => false,
      _ => self
        .hooks
        .is_same_origin_private_member
        .map(|cb| cb(src_prop, dst_prop))
        .unwrap_or(false),
    }
  }

  fn access(&self, prop: &PropData) -> Accessibility {
    prop.accessibility.unwrap_or(Accessibility::Public)
  }

  fn index_for_prop<'b>(&self, obj: &'b Shape, key: &PropKey) -> Option<&'b Indexer> {
    let key_ty = self.prop_key_type(key);
    obj.indexers.iter().find(|idx| {
      self
        .relate_internal(
          key_ty,
          idx.key_type,
          RelationKind::Assignable,
          RelationMode::NONE,
          false,
        )
        .result
    })
  }

  fn find_matching_indexer<'b>(
    &self,
    obj: &'b Shape,
    target: &Indexer,
    mode: RelationMode,
  ) -> Option<&'b Indexer> {
    obj.indexers.iter().find(|idx| {
      self
        .relate_internal(
          target.key_type,
          idx.key_type,
          RelationKind::Assignable,
          mode,
          false,
        )
        .result
    })
  }

  fn indexer_covers_property(&self, idx: &Indexer, key: &PropKey, mode: RelationMode) -> bool {
    let key_ty = self.prop_key_type(key);
    self
      .relate_internal(key_ty, idx.key_type, RelationKind::Assignable, mode, false)
      .result
  }

  fn prop_key_type(&self, key: &PropKey) -> TypeId {
    let primitives = self.store.primitive_ids();
    match key {
      PropKey::String(_) => primitives.string,
      PropKey::Number(_) => primitives.number,
      PropKey::Symbol(_) => primitives.symbol,
    }
  }

  fn prop_name(&self, key: &PropKey) -> String {
    match key {
      PropKey::String(id) => self.store.name(*id),
      PropKey::Number(num) => num.to_string(),
      PropKey::Symbol(id) => format!("[{}]", self.store.name(*id)),
    }
  }

  fn find_property<'b>(&self, shape: &'b Shape, key: &PropKey) -> Option<&'b Property> {
    shape
      .properties
      .binary_search_by(|p| p.key.cmp_with(key, &|id| self.store.name(id)))
      .ok()
      .map(|idx| &shape.properties[idx])
  }

  fn relate_callable(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src: &[crate::ids::SignatureId],
    dst: &[crate::ids::SignatureId],
    mode: RelationMode,
    record: bool,
    treat_as_method: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src: src_id,
      dst: dst_id,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children: Vec<Option<ReasonNode>> = Vec::new();
    for dst_sig in dst {
      let mut matched = None;
      for src_sig in src {
        let related = self.relate_signature(
          key,
          &self.store.signature(*src_sig),
          &self.store.signature(*dst_sig),
          mode,
          record,
          treat_as_method,
        );
        if record {
          children.push(related.reason.clone());
        }
        if related.result {
          matched = Some(related);
          break;
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
            Some("callable signature".into()),
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
        Some("callable signatures".into()),
      ),
    }
  }

  fn relate_signature(
    &self,
    key: RelationKey,
    src: &Signature,
    dst: &Signature,
    mode: RelationMode,
    record: bool,
    treat_as_method: bool,
  ) -> RelationResult {
    let mut children: Vec<Option<ReasonNode>> = Vec::new();
    let allow_bivariance = !self.options.strict_function_types
      || treat_as_method
      || mode.contains(RelationMode::BIVARIANT_PARAMS);

    if src.params.len() < dst.params.len() && src.params.iter().all(|p| !p.rest) {
      let src_required = self.required_params(src);
      let dst_required = self.required_params(dst);
      if src_required > dst_required {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("parameter count".into())),
        };
      }
    }

    if let (Some(src_this), Some(dst_this)) = (src.this_param, dst.this_param) {
      let related = if allow_bivariance {
        let forward =
          self.relate_internal(src_this, dst_this, RelationKind::Assignable, mode, record);
        if forward.result {
          forward
        } else {
          self.relate_internal(dst_this, src_this, RelationKind::Assignable, mode, record)
        }
      } else {
        self.relate_internal(dst_this, src_this, RelationKind::Assignable, mode, record)
      };
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("this".into())),
        };
      }
    } else if dst.this_param.is_some() {
      return RelationResult {
        result: false,
        reason: self.join_reasons(record, key, children, false, Some("this param".into())),
      };
    }

    let paired = src.params.iter().zip(dst.params.iter());
    for (s_param, d_param) in paired {
      let related = if allow_bivariance {
        let forward = self.relate_internal(
          s_param.ty,
          d_param.ty,
          RelationKind::Assignable,
          mode,
          record,
        );
        if forward.result {
          forward
        } else {
          self.relate_internal(
            d_param.ty,
            s_param.ty,
            RelationKind::Assignable,
            mode,
            record,
          )
        }
      } else {
        self.relate_internal(
          d_param.ty,
          s_param.ty,
          RelationKind::Assignable,
          mode,
          record,
        )
      };

      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("parameter".into())),
        };
      }
    }

    if dst.params.len() > src.params.len() {
      if let Some(rest) = src.params.iter().find(|p| p.rest) {
        for extra in dst.params.iter().skip(src.params.len()) {
          let related = if allow_bivariance {
            let forward =
              self.relate_internal(rest.ty, extra.ty, RelationKind::Assignable, mode, record);
            if forward.result {
              forward
            } else {
              self.relate_internal(extra.ty, rest.ty, RelationKind::Assignable, mode, record)
            }
          } else {
            self.relate_internal(extra.ty, rest.ty, RelationKind::Assignable, mode, record)
          };
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(record, key, children, false, Some("rest".into())),
            };
          }
        }
      } else {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("parameter count".into())),
        };
      }
    }

    let ret_related =
      self.relate_internal(src.ret, dst.ret, RelationKind::Assignable, mode, record);
    if record {
      children.push(ret_related.reason);
    }
    if !ret_related.result {
      return RelationResult {
        result: false,
        reason: self.join_reasons(record, key, children, false, Some("return".into())),
      };
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("function".into())),
    }
  }

  fn relate_tuple(
    &self,
    key_src: TypeId,
    key_dst: TypeId,
    src: &[crate::kind::TupleElem],
    dst: &[crate::kind::TupleElem],
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let key = RelationKey {
      src: key_src,
      dst: key_dst,
      kind: RelationKind::Assignable,
      mode,
    };
    let mut children: Vec<Option<ReasonNode>> = Vec::new();
    let mut src_index = 0;
    let rest = src.iter().find(|e| e.rest);
    for dst_elem in dst.iter() {
      let src_elem = if let Some(elem) = src.get(src_index) {
        src_index += 1;
        elem
      } else if let Some(rest) = rest {
        rest
      } else {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("tuple length".into())),
        };
      };
      let related = self.relate_internal(
        src_elem.ty,
        dst_elem.ty,
        RelationKind::Assignable,
        mode,
        record,
      );
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("tuple element".into())),
        };
      }
      if !dst_elem.optional && src_elem.optional && !src_elem.rest {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("tuple required".into())),
        };
      }
      if !dst_elem.readonly && src_elem.readonly {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("tuple readonly".into())),
        };
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("tuple".into())),
    }
  }

  fn required_params(&self, sig: &Signature) -> usize {
    sig.params.iter().filter(|p| !p.optional && !p.rest).count()
  }

  fn expand_ref(&self, def: DefId, args: &[TypeId]) -> Option<TypeId> {
    self
      .hooks
      .expander
      .and_then(|expander| expander.expand_ref(&self.store, def, args))
  }

  fn object_shape(&self, obj: crate::ids::ObjectId) -> Shape {
    let object = self.store.object(obj);
    self.store.shape(object.shape)
  }
}
