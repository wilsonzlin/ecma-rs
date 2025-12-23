use crate::types::MappedModifier;
use crate::types::TemplatePart;
use crate::types::TypeId;
use crate::types::TypeKind;
use crate::types::TypeStore;
use std::collections::HashSet;

pub struct TypeDisplay<'a> {
  store: &'a TypeStore,
}

impl<'a> TypeDisplay<'a> {
  pub fn new(store: &'a TypeStore) -> Self {
    Self { store }
  }

  pub fn fmt(&self, ty: TypeId) -> String {
    let mut visiting = HashSet::new();
    self.fmt_inner(ty, &mut visiting)
  }

  fn fmt_inner(&self, ty: TypeId, visiting: &mut HashSet<TypeId>) -> String {
    if !visiting.insert(ty) {
      return "<rec>".to_string();
    }
    let res = match self.store.kind(ty) {
      TypeKind::Any => "any".to_string(),
      TypeKind::Unknown => "unknown".to_string(),
      TypeKind::Never => "never".to_string(),
      TypeKind::Boolean => "boolean".to_string(),
      TypeKind::True => "true".to_string(),
      TypeKind::False => "false".to_string(),
      TypeKind::Number => "number".to_string(),
      TypeKind::String => "string".to_string(),
      TypeKind::LiteralString(s) => format!("\"{}\"", s),
      TypeKind::LiteralNumber(n) => n.to_string(),
      TypeKind::TypeParam { name, .. } => name.clone(),
      TypeKind::Union(types) => {
        let mut parts: Vec<String> = types.iter().map(|t| self.fmt_inner(*t, visiting)).collect();
        parts.sort();
        parts.dedup();
        parts.join(" | ")
      }
      TypeKind::Intersection(types) => {
        let mut parts: Vec<String> = types.iter().map(|t| self.fmt_inner(*t, visiting)).collect();
        parts.sort();
        parts.dedup();
        parts.join(" & ")
      }
      TypeKind::Object(obj) => {
        let mut parts = Vec::new();
        for (key, prop) in obj.properties.iter() {
          let mut prefix = String::new();
          if prop.readonly {
            prefix.push_str("readonly ");
          }
          let mut piece = format!("{}{}", prefix, key);
          if prop.optional {
            piece.push('?');
          }
          piece.push_str(": ");
          piece.push_str(&self.fmt_inner(prop.ty, visiting));
          parts.push(piece);
        }
        format!("{{ {} }}", parts.join("; "))
      }
      TypeKind::Conditional {
        check_type,
        extends_type,
        true_type,
        false_type,
        ..
      } => format!(
        "({} extends {} ? {} : {})",
        self.fmt_inner(*check_type, visiting),
        self.fmt_inner(*extends_type, visiting),
        self.fmt_inner(*true_type, visiting),
        self.fmt_inner(*false_type, visiting)
      ),
      TypeKind::IndexedAccess { object, index } => {
        format!(
          "{}[{}]",
          self.fmt_inner(*object, visiting),
          self.fmt_inner(*index, visiting)
        )
      }
      TypeKind::KeyOf(inner) => format!("keyof {}", self.fmt_inner(*inner, visiting)),
      TypeKind::Mapped(mapped) => {
        let mut head = String::new();
        if mapped.readonly == MappedModifier::Add {
          head.push_str("readonly ");
        }
        head.push('[');
        head.push_str(&self.fmt_inner(mapped.param, visiting));
        head.push_str(" in ");
        head.push_str(&self.fmt_inner(mapped.keys, visiting));
        if let Some(as_type) = mapped.as_type {
          head.push_str(" as ");
          head.push_str(&self.fmt_inner(as_type, visiting));
        }
        head.push(']');
        if mapped.optional == MappedModifier::Add {
          head.push('?');
        }
        if mapped.readonly == MappedModifier::Remove {
          head.push_str(" -readonly");
        }
        if mapped.optional == MappedModifier::Remove {
          head.push_str(" -?");
        }
        format!(
          "{{ {}: {} }}",
          head,
          self.fmt_inner(mapped.value_type, visiting)
        )
      }
      TypeKind::Template(tpl) => {
        let mut buf = String::from("`");
        for part in tpl.parts.iter() {
          match part {
            TemplatePart::Literal(s) => buf.push_str(s),
            TemplatePart::Type(t) => {
              buf.push_str("${");
              buf.push_str(&self.fmt_inner(*t, visiting));
              buf.push('}');
            }
          }
        }
        buf.push('`');
        buf
      }
    };
    visiting.remove(&ty);
    res
  }
}
