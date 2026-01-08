/// WebIDL type descriptors used by conversion and overload algorithms.
#[derive(Clone, Debug, PartialEq)]
pub enum IdlType {
    Undefined,
    Boolean,
    Double,
    DomString,
    Object,
    Sequence(Box<IdlType>),
    AsyncSequence(Box<IdlType>),
    FrozenArray(Box<IdlType>),
    Union(Vec<IdlType>),
    Nullable(Box<IdlType>),
}

impl IdlType {
    pub fn is_string_type(&self) -> bool {
        matches!(self, IdlType::DomString)
    }

    pub fn is_sequence_like(&self) -> bool {
        matches!(self, IdlType::Sequence(_) | IdlType::FrozenArray(_))
    }

    pub fn is_async_sequence(&self) -> bool {
        matches!(self, IdlType::AsyncSequence(_))
    }

    pub fn flattened_member_types(&self) -> Vec<&IdlType> {
        fn rec<'a>(ty: &'a IdlType, out: &mut Vec<&'a IdlType>) {
            match ty {
                IdlType::Union(members) => {
                    for m in members {
                        rec(m, out);
                    }
                }
                _ => out.push(ty),
            }
        }
        let mut out = Vec::new();
        rec(self, &mut out);
        out
    }

    pub fn includes_undefined(&self) -> bool {
        match self {
            IdlType::Union(members) => members.iter().any(|m| m.includes_undefined()),
            IdlType::Undefined => true,
            _ => false,
        }
    }

    pub fn includes_nullable(&self) -> bool {
        match self {
            IdlType::Union(members) => members.iter().any(|m| m.includes_nullable()),
            IdlType::Nullable(_) => true,
            _ => false,
        }
    }

    pub fn contains_string_type(&self) -> bool {
        match self {
            IdlType::Union(members) => members.iter().any(|m| m.contains_string_type()),
            IdlType::Nullable(inner) => inner.contains_string_type(),
            _ => self.is_string_type(),
        }
    }

    pub fn contains_async_sequence_type(&self) -> bool {
        match self {
            IdlType::Union(members) => members.iter().any(|m| m.contains_async_sequence_type()),
            IdlType::Nullable(inner) => inner.contains_async_sequence_type(),
            IdlType::AsyncSequence(_) => true,
            _ => false,
        }
    }

    pub fn contains_sequence_type(&self) -> bool {
        match self {
            IdlType::Union(members) => members.iter().any(|m| m.contains_sequence_type()),
            IdlType::Nullable(inner) => inner.contains_sequence_type(),
            IdlType::Sequence(_) => true,
            _ => false,
        }
    }

    pub fn contains_frozen_array_type(&self) -> bool {
        match self {
            IdlType::Union(members) => members.iter().any(|m| m.contains_frozen_array_type()),
            IdlType::Nullable(inner) => inner.contains_frozen_array_type(),
            IdlType::FrozenArray(_) => true,
            _ => false,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AsyncSequenceKind {
    Async,
    Sync,
}

#[derive(Debug, Clone, PartialEq)]
pub struct AsyncSequence<V> {
    pub object: V,
    pub method: V,
    pub kind: AsyncSequenceKind,
}

#[derive(Debug, Clone, PartialEq)]
pub struct UnionValue<V, S> {
    pub selected_type: IdlType,
    pub value: Box<IdlValue<V, S>>,
}

#[derive(Debug, Clone, PartialEq)]
pub enum IdlValue<V, S> {
    Undefined,
    Null,
    Boolean(bool),
    Double(f64),
    DomString(S),
    Object(V),
    Sequence(Vec<IdlValue<V, S>>),
    AsyncSequence(AsyncSequence<V>),
    FrozenArray(V),
    Union(UnionValue<V, S>),
}
