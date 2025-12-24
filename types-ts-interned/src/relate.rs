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
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;

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

pub trait RelateTypeExpander {
  fn expand_ref(&self, store: &TypeStore, def: DefId, args: &[TypeId]) -> Option<TypeId>;
}

pub struct RelateCtx<'a> {
  store: &'a TypeStore,
  pub options: TypeOptions,
  hooks: RelateHooks<'a>,
  cache: RefCell<HashMap<RelationKey, bool>>,
  in_progress: RefCell<HashSet<RelationKey>>,
}

impl<'a> fmt::Debug for RelateCtx<'a> {
  fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
    f.debug_struct("RelateCtx")
      .field("options", &self.options)
      .finish()
  }
}

impl<'a> RelateCtx<'a> {
  pub fn new(store: &'a TypeStore, options: TypeOptions) -> Self {
    Self::with_options(store, options)
  }

  pub fn with_options(store: &'a TypeStore, options: TypeOptions) -> Self {
    Self::with_hooks(store, options, RelateHooks::default())
  }

  pub fn with_hooks(store: &'a TypeStore, options: TypeOptions, hooks: RelateHooks<'a>) -> Self {
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

  pub fn explain_assignable(&self, src: TypeId, dst: TypeId) -> RelationResult {
    self.relate_internal(src, dst, RelationKind::Assignable, RelationMode::NONE, true)
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
      // Structural relations in TypeScript assume success on cycles to break
      // infinite recursion. We mirror that here.
      return RelationResult {
        result: true,
        reason: record.then(|| self.cycle_reason(key)),
      };
    }

    self.in_progress.borrow_mut().insert(key);

    let outcome = match kind {
      RelationKind::Assignable => self.assignable(src, dst, mode, record),
      RelationKind::Comparable => {
        let forward = self.assignable(src, dst, mode, record);
        if !forward.result {
          forward
        } else {
          let backward = self.assignable(dst, src, mode, record);
          RelationResult {
            result: backward.result,
            reason: self.join_reasons(
              record,
              key,
              vec![forward.reason, backward.reason],
              backward.result,
              Some("comparable".into()),
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

    // Unions
    if let TypeKind::Union(srcs) = &src_kind {
      let mut children = Vec::new();
      for member in srcs {
        let related = self.relate_internal(*member, dst, RelationKind::Assignable, mode, record);
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(record, key, children, false, Some("union source".into())),
          };
        }
      }
      return RelationResult {
        result: true,
        reason: self.join_reasons(record, key, children, true, Some("union source".into())),
      };
    }
    if let TypeKind::Union(dsts) = &dst_kind {
      let mut attempts = Vec::new();
      for member in dsts {
        let related = self.relate_internal(src, *member, RelationKind::Assignable, mode, record);
        let reason = related.reason;
        if record {
          attempts.push(reason.clone());
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
        reason: self.join_reasons(record, key, attempts, false, Some("union target".into())),
      };
    }

    // Intersections
    if let TypeKind::Intersection(dsts) = &dst_kind {
      let mut children = Vec::new();
      for member in dsts {
        let related = self.relate_internal(src, *member, RelationKind::Assignable, mode, record);
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
        ),
      };
    }

    if let TypeKind::Intersection(srcs) = &src_kind {
      if let TypeKind::Object(dst_obj) = &dst_kind {
        if let Some(merged) = self.merge_intersection(srcs) {
          let related = self.relate_object(src, dst, merged, *dst_obj, mode, record);
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

      let mut children = Vec::new();
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
        ),
      };
    }

    match (&src_kind, &dst_kind) {
      (TypeKind::BooleanLiteral(a), TypeKind::BooleanLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into())),
        }
      }
      (TypeKind::NumberLiteral(a), TypeKind::NumberLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into())),
        }
      }
      (TypeKind::StringLiteral(a), TypeKind::StringLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into())),
        }
      }
      (TypeKind::BigIntLiteral(a), TypeKind::BigIntLiteral(b)) => {
        let res = a == b;
        RelationResult {
          result: res,
          reason: self.join_reasons(record, key, Vec::new(), res, Some("literal".into())),
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
      ) => self.relate_array(*src_elem, *dst_elem, *src_ro, *dst_ro, key, mode, record),
      (TypeKind::Tuple(src_elems), TypeKind::Tuple(dst_elems)) => {
        self.relate_tuple(src_elems, dst_elems, key, mode, record)
      }
      (TypeKind::Array { ty, .. }, TypeKind::Tuple(dst_elems)) => {
        self.relate_array_to_tuple(*ty, dst_elems, key, mode, record)
      }
      (TypeKind::Tuple(src_elems), TypeKind::Array { ty, readonly }) => {
        self.relate_tuple_to_array(src_elems, *ty, *readonly, key, mode, record)
      }
      (TypeKind::Callable { overloads: s }, TypeKind::Callable { overloads: d }) => {
        self.relate_callable(src, dst, s, d, mode, record)
      }
      (TypeKind::Callable { overloads }, TypeKind::Object(obj)) => {
        self.relate_callable_to_object(src, dst, overloads, *obj, key, mode, record)
      }
      (TypeKind::Object(obj), TypeKind::Callable { overloads }) => {
        self.relate_object_to_callable(src, dst, *obj, overloads, key, mode, record)
      }
      (TypeKind::Object(src_obj), TypeKind::Object(dst_obj)) => {
        self.relate_object(src, dst, *src_obj, *dst_obj, mode, record)
      }
      _ => RelationResult {
        result: false,
        reason: self.join_reasons(record, key, Vec::new(), false, Some("structural".into())),
      },
    }
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
        ),
      };
    }
    let related = self.relate_internal(src_elem, dst_elem, RelationKind::Assignable, mode, record);
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

  fn relate_array_to_tuple(
    &self,
    src_elem: TypeId,
    dst_elems: &[crate::TupleElem],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
  ) -> RelationResult {
    let mut children = Vec::new();
    for dst_elem in dst_elems {
      let dst_ty = self.optional_type(dst_elem.ty, dst_elem.optional);
      let related = self.relate_internal(src_elem, dst_ty, RelationKind::Assignable, mode, record);
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("array to tuple".into())),
        };
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("array to tuple".into())),
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
        ),
      };
    }
    let mut children = Vec::new();
    for src_elem in src_elems {
      let src_ty = self.optional_type(src_elem.ty, src_elem.optional);
      let related = self.relate_internal(src_ty, dst_elem, RelationKind::Assignable, mode, record);
      if record {
        children.push(related.reason);
      }
      if !related.result {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, children, false, Some("tuple to array".into())),
        };
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("tuple to array".into())),
    }
  }

  fn relate_tuple(
    &self,
    src_elems: &[crate::TupleElem],
    dst_elems: &[crate::TupleElem],
    key: RelationKey,
    mode: RelationMode,
    record: bool,
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
        reason: self.join_reasons(record, key, Vec::new(), false, Some("tuple arity".into())),
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
            reason: self.join_reasons(record, key, children, false, Some("tuple length".into())),
          };
        }
        Some(src_elem) => {
          if dst_elem.rest {
            for rem in src_elems.iter().skip(s_idx) {
              let src_ty = self.optional_type(rem.ty, rem.optional || rem.rest);
              let dst_ty = self.optional_type(dst_elem.ty, dst_elem.optional || dst_elem.rest);
              if !dst_elem.readonly && rem.readonly {
                return RelationResult {
                  result: false,
                  reason: self.join_reasons(
                    record,
                    key,
                    children,
                    false,
                    Some("tuple readonly".into()),
                  ),
                };
              }
              let related =
                self.relate_internal(src_ty, dst_ty, RelationKind::Assignable, mode, record);
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
                  ),
                };
              }
            }
            return RelationResult {
              result: true,
              reason: self.join_reasons(record, key, children, true, Some("tuple rest".into())),
            };
          }

          if src_elem.rest {
            let src_ty = self.optional_type(src_elem.ty, src_elem.optional || src_elem.rest);
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
                  ),
                };
              }
              let dst_ty = self.optional_type(d.ty, d.optional || d.rest);
              let related =
                self.relate_internal(src_ty, dst_ty, RelationKind::Assignable, mode, record);
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
              ),
            };
          }
          let src_ty = self.optional_type(src_elem.ty, src_elem.optional);
          let dst_ty = self.optional_type(dst_elem.ty, dst_elem.optional);
          let related =
            self.relate_internal(src_ty, dst_ty, RelationKind::Assignable, mode, record);
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(record, key, children, false, Some("tuple element".into())),
            };
          }
        }
      }

      s_idx += 1;
      d_idx += 1;
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("tuple".into())),
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
          reason: self.join_reasons(record, key, children, false, Some("call signature".into())),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }
    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("callable".into())),
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
        ),
      };
    }

    match (&src.this_param, &dst.this_param) {
      (Some(s), Some(d)) => {
        let related = self.relate_internal(*d, *s, RelationKind::Assignable, mode, record);
        if record {
          children.push(related.reason);
        }
        if !related.result {
          return RelationResult {
            result: false,
            reason: self.join_reasons(record, key, children, false, Some("this parameter".into())),
          };
        }
      }
      (None, Some(_)) => {
        return RelationResult {
          result: false,
          reason: self.join_reasons(record, key, Vec::new(), false, Some("missing this".into())),
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
          ),
        };
      }
      let s_ty = self.optional_type(s_param.ty, s_param.optional);
      let d_ty = self.optional_type(d_param.ty, d_param.optional);
      let related = if allow_bivariance {
        let forward = self.relate_internal(s_ty, d_ty, RelationKind::Assignable, mode, record);
        if forward.result {
          forward
        } else {
          self.relate_internal(d_ty, s_ty, RelationKind::Assignable, mode, record)
        }
      } else {
        self.relate_internal(d_ty, s_ty, RelationKind::Assignable, mode, record)
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
        let rest_ty = self.optional_type(rest.ty, rest.optional);
        for extra in dst.params.iter().skip(src.params.len()) {
          if !extra.optional && !rest.rest {
            return RelationResult {
              result: false,
              reason: self.join_reasons(record, key, children, false, Some("rest coverage".into())),
            };
          }
          let extra_ty = self.optional_type(extra.ty, extra.optional);
          let related = if allow_bivariance {
            let forward =
              self.relate_internal(rest_ty, extra_ty, RelationKind::Assignable, mode, record);
            if forward.result {
              forward
            } else {
              self.relate_internal(extra_ty, rest_ty, RelationKind::Assignable, mode, record)
            }
          } else {
            self.relate_internal(extra_ty, rest_ty, RelationKind::Assignable, mode, record)
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
              ),
            };
          }
        }
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
      reason: self.join_reasons(record, key, children, true, Some("signature".into())),
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

  fn optional_type(&self, ty: TypeId, optional: bool) -> TypeId {
    if optional && !self.options.exact_optional_property_types {
      self
        .store
        .union(vec![ty, self.store.primitive_ids().undefined])
    } else {
      ty
    }
  }

  fn is_method_like(&self, data: &PropData) -> bool {
    data.is_method || matches!(self.store.type_kind(data.ty), TypeKind::Callable { .. })
  }

  fn relate_object(
    &self,
    src_id: TypeId,
    dst_id: TypeId,
    src_obj: ObjectId,
    dst_obj: ObjectId,
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
              ),
            };
          }

          let next_mode =
            if self.is_method_like(&src_prop.data) || self.is_method_like(&dst_prop.data) {
              mode | RelationMode::BIVARIANT_PARAMS
            } else {
              mode
            };
          let src_ty = self.optional_type(src_prop.data.ty, src_prop.data.optional);
          let dst_ty = self.optional_type(dst_prop.data.ty, dst_prop.data.optional);
          let related =
            self.relate_internal(src_ty, dst_ty, RelationKind::Assignable, next_mode, record);
          if record {
            children.push(related.reason);
          }
          if !related.result {
            return RelationResult {
              result: false,
              reason: self.join_reasons(record, key, children, false, Some("property type".into())),
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
                ),
              };
            }
            let related = self.relate_internal(
              self.optional_type(index.value_type, false),
              self.optional_type(dst_prop.data.ty, dst_prop.data.optional),
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
                  Some("indexer property".into()),
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
              ),
            };
          }
        }
      }
    }

    for dst_index in &dst_shape.indexers {
      if let Some(src_idx) = self.find_matching_indexer(&src_shape, dst_index, mode, record) {
        if !dst_index.readonly && src_idx.readonly {
          return RelationResult {
            result: false,
            reason: self.join_reasons(
              record,
              key,
              children,
              false,
              Some("readonly indexer".into()),
            ),
          };
        }
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
            reason: self.join_reasons(record, key, children, false, Some("indexer".into())),
          };
        }
      } else {
        for prop in &src_shape.properties {
          if !self.indexer_accepts_prop(dst_index, &prop.key) {
            continue;
          }
          let related = self.relate_internal(
            self.optional_type(prop.data.ty, prop.data.optional),
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
                Some("property vs indexer".into()),
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
          reason: self.join_reasons(record, key, children, false, Some("call signature".into())),
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
          ),
        };
      } else if record {
        children.push(matched.flatten());
      }
    }

    RelationResult {
      result: true,
      reason: self.join_reasons(record, key, children, true, Some("object".into())),
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
  ) -> Option<&'b Indexer> {
    shape.indexers.iter().find(|src_idx| {
      let key_related = self.relate_internal(
        dst.key_type,
        src_idx.key_type,
        RelationKind::Assignable,
        mode,
        record,
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
      .and_then(|expander| expander.expand_ref(self.store, def, args))
  }
}
