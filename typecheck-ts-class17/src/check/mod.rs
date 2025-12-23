use crate::diagnostics::Diagnostic;
use crate::diagnostics::DiagnosticCode;
use crate::types::class::Accessibility;
use crate::types::class::ClassDef;
use crate::types::class::ClassInfo;
use crate::types::class::ClassMember;
use crate::types::class::ClassMemberInfo;
use crate::types::class::ClassMemberKind;
use crate::types::FunctionType;
use crate::types::InterfaceDef;
use crate::types::ObjectProperty;
use crate::types::ObjectType;
use crate::types::Type;
use crate::ClassId;
use crate::InterfaceId;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::collections::HashSet;

pub mod class;

/// Checker options controlling initialization behavior.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckOptions {
  pub strict_property_initialization: bool,
  /// Included for parity with TypeScript's option. The simplified checker does
  /// not currently distinguish the emit strategy for class fields but accepts
  /// the flag so callers can document intent.
  pub use_define_for_class_fields: bool,
}

impl Default for CheckOptions {
  fn default() -> Self {
    Self {
      strict_property_initialization: true,
      use_define_for_class_fields: false,
    }
  }
}

/// Identifier for stored definitions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum DefId {
  Class(ClassId),
  Interface(InterfaceId),
}

/// Result of checking a definition.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CheckResult {
  pub diagnostics: Vec<Diagnostic>,
}

/// Aggregate of computed instance + constructor types for a class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClassTypes {
  pub instance: Type,
  pub constructor: Type,
}

#[derive(Default)]
pub struct TypeChecker {
  classes: Vec<ClassDef>,
  interfaces: Vec<InterfaceDef>,
  class_info_cache: HashMap<ClassId, ClassInfo>,
  interface_cache: HashMap<InterfaceId, ObjectType>,
}

impl TypeChecker {
  pub fn new() -> Self {
    Self::default()
  }

  pub fn add_class(&mut self, class: ClassDef) -> ClassId {
    let id = self.classes.len();
    self.classes.push(class);
    id
  }

  pub fn add_interface(&mut self, interface: InterfaceDef) -> InterfaceId {
    let id = self.interfaces.len();
    self.interfaces.push(interface);
    id
  }

  pub fn type_of_def(&mut self, id: DefId) -> Result<Type, Diagnostic> {
    match id {
      DefId::Class(class_id) => {
        self.class_info(class_id, &mut HashSet::new())?;
        Ok(Type::ClassInstance(class_id))
      }
      DefId::Interface(interface_id) => {
        self.interface_info(interface_id, &mut HashSet::new())?;
        Ok(Type::Interface(interface_id))
      }
    }
  }

  pub fn class_types(&mut self, id: ClassId) -> Result<ClassTypes, Diagnostic> {
    self.class_info(id, &mut HashSet::new())?;
    Ok(ClassTypes {
      instance: Type::ClassInstance(id),
      constructor: Type::ClassStatics(id),
    })
  }

  pub fn check_body(&mut self, id: DefId, options: &CheckOptions) -> CheckResult {
    match id {
      DefId::Class(class_id) => self.check_class_body(class_id, options),
      DefId::Interface(_) => CheckResult {
        diagnostics: Vec::new(),
      },
    }
  }

  /// Check whether a property access is legal for the given accessor class
  /// (or `None` for unbound access such as in a free function).
  pub fn check_property_access(
    &mut self,
    receiver: &Type,
    property: &str,
    accessor: Option<ClassId>,
  ) -> Result<Type, Diagnostic> {
    match receiver {
      Type::ClassInstance(id) => {
        let info = self
          .class_info(*id, &mut HashSet::new())
          .map_err(|e| e.clone())?;
        if let Some(member) = info.instance_members.get(property) {
          self.ensure_accessible(member, accessor, false)?;
          Ok(member.ty.clone())
        } else if let Some(index) = info.instance_string_index.clone() {
          self.ensure_accessible(&index, accessor, false)?;
          Ok(index.ty.clone())
        } else {
          Err(Diagnostic::new(
            DiagnosticCode::InvalidMemberAccess,
            format!("Property `{}` does not exist", property),
          ))
        }
      }
      Type::ClassStatics(id) => {
        let info = self
          .class_info(*id, &mut HashSet::new())
          .map_err(|e| e.clone())?;
        if let Some(member) = info.static_members.get(property) {
          self.ensure_accessible(member, accessor, true)?;
          Ok(member.ty.clone())
        } else if let Some(index) = info.static_string_index.clone() {
          self.ensure_accessible(&index, accessor, true)?;
          Ok(index.ty.clone())
        } else {
          Err(Diagnostic::new(
            DiagnosticCode::InvalidMemberAccess,
            format!("Property `{}` does not exist", property),
          ))
        }
      }
      Type::Object(obj) => obj
        .properties
        .get(property)
        .map(|p| p.ty.clone())
        .ok_or_else(|| {
          Diagnostic::new(
            DiagnosticCode::InvalidMemberAccess,
            format!("Property `{}` does not exist", property),
          )
        }),
      Type::Interface(id) => {
        let info = self
          .interface_info(*id, &mut HashSet::new())
          .map_err(|e| e.clone())?;
        info
          .properties
          .get(property)
          .map(|p| p.ty.clone())
          .ok_or_else(|| {
            Diagnostic::new(
              DiagnosticCode::InvalidMemberAccess,
              format!("Property `{}` does not exist", property),
            )
          })
      }
      _ => Err(Diagnostic::new(
        DiagnosticCode::InvalidMemberAccess,
        format!("Type {:?} has no properties", receiver),
      )),
    }
  }

  pub fn is_assignable(&mut self, source: &Type, target: &Type) -> bool {
    self.is_assignable_inner(source, target, &mut HashSet::new())
  }

  /// Internal assignability that carries a recursion guard across nested calls.
  fn is_assignable_inner(
    &mut self,
    source: &Type,
    target: &Type,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    if target == &Type::Any || source == &Type::Any {
      return true;
    }
    if target == &Type::Unknown {
      return true;
    }
    if source == &Type::Unknown {
      return false;
    }
    if target == &Type::Never {
      return source == target;
    }
    if source == target {
      return true;
    }
    if !seen.insert((source.clone(), target.clone())) {
      return true;
    }
    match (source, target) {
      (Type::Boolean, Type::Boolean)
      | (Type::Number, Type::Number)
      | (Type::String, Type::String) => true,
      (Type::ClassInstance(source_id), Type::ClassInstance(target_id)) => {
        self.class_instance_assignable(*source_id, *target_id, seen)
      }
      (Type::ClassStatics(source_id), Type::ClassStatics(target_id)) => {
        self.class_statics_assignable(*source_id, *target_id, seen)
      }
      (Type::ClassInstance(source_id), Type::Interface(target_interface)) => {
        let obj = self.class_as_object(*source_id);
        obj.map_or(false, |s_obj| {
          match self.interface_info(*target_interface, &mut HashSet::new()) {
            Ok(target_obj) => self.object_assignable_types(&s_obj, &target_obj, seen),
            Err(_) => false,
          }
        })
      }
      (Type::Interface(source_interface), Type::Interface(target_interface)) => match (
        self.interface_info(*source_interface, &mut HashSet::new()),
        self.interface_info(*target_interface, &mut HashSet::new()),
      ) {
        (Ok(source_obj), Ok(target_obj)) => {
          self.object_assignable_types(&source_obj, &target_obj, seen)
        }
        _ => false,
      },
      (Type::Object(obj), Type::Interface(target_interface)) => {
        let target_obj = self.interface_info(*target_interface, &mut HashSet::new());
        match target_obj {
          Ok(target_obj) => self.object_assignable_types(obj, &target_obj, seen),
          Err(_) => false,
        }
      }
      (Type::Object(source_obj), Type::Object(target_obj)) => {
        self.object_assignable_types(source_obj, target_obj, seen)
      }
      (Type::Function(source_fn), Type::Function(target_fn)) => {
        self.function_assignable(source_fn, target_fn, seen)
      }
      _ => false,
    }
  }

  fn class_info(
    &mut self,
    id: ClassId,
    visiting: &mut HashSet<ClassId>,
  ) -> Result<ClassInfo, Diagnostic> {
    if let Some(info) = self.class_info_cache.get(&id) {
      return Ok(info.clone());
    }
    if !visiting.insert(id) {
      return Err(Diagnostic::new(
        DiagnosticCode::ExtendsIncompatible,
        format!(
          "Cycle detected while resolving base classes for class #{}",
          id
        ),
      ));
    }
    let def = self.classes[id].clone();
    let mut info = ClassInfo::new(id, def.name.clone(), def.extends);
    if let Some(base) = def.extends {
      let base_info = self.class_info(base, visiting)?;
      info.inherit(&base_info);
    }
    // Parameter properties.
    if let Some(constructor) = def.constructor.clone() {
      for param in constructor.params {
        if let Some(accessibility) = param.property {
          let ty = param.ty.clone();
          let member = ClassMemberInfo {
            name: param.name.clone(),
            ty,
            accessibility,
            declared_in: id,
            optional: param.optional,
            kind: ClassMemberKind::ParameterProperty,
          };
          info.instance_members.insert(param.name.clone(), member);
        }
      }
    }
    for member in &def.members {
      match member {
        ClassMember::Field(field) => {
          let member = ClassMemberInfo {
            name: field.name.clone(),
            ty: field.ty.clone(),
            accessibility: field.accessibility,
            declared_in: id,
            optional: field.optional,
            kind: ClassMemberKind::Field,
          };
          if field.is_static {
            info.static_members.insert(field.name.clone(), member);
          } else {
            info.instance_members.insert(field.name.clone(), member);
          }
        }
        ClassMember::Method(method) => {
          let mut fn_type = method.function.clone();
          if fn_type.this_param.is_none() {
            if method.is_static {
              fn_type.this_param = Some(Box::new(Type::ClassStatics(id)));
            } else {
              fn_type.this_param = Some(Box::new(Type::ClassInstance(id)));
            }
          }
          let member = ClassMemberInfo {
            name: method.name.clone(),
            ty: Type::Function(fn_type),
            accessibility: method.accessibility,
            declared_in: id,
            optional: method.optional,
            kind: ClassMemberKind::Method,
          };
          if method.is_static {
            info.static_members.insert(method.name.clone(), member);
          } else {
            info.instance_members.insert(method.name.clone(), member);
          }
        }
        ClassMember::Getter(getter) => {
          let member = ClassMemberInfo {
            name: getter.name.clone(),
            ty: getter.ty.clone(),
            accessibility: getter.accessibility,
            declared_in: id,
            optional: false,
            kind: ClassMemberKind::Getter,
          };
          if getter.is_static {
            info.static_members.insert(getter.name.clone(), member);
          } else {
            info.instance_members.insert(getter.name.clone(), member);
          }
        }
        ClassMember::Setter(setter) => {
          let member = ClassMemberInfo {
            name: setter.name.clone(),
            ty: setter.ty.clone(),
            accessibility: setter.accessibility,
            declared_in: id,
            optional: false,
            kind: ClassMemberKind::Setter,
          };
          if setter.is_static {
            info.static_members.insert(setter.name.clone(), member);
          } else {
            info.instance_members.insert(setter.name.clone(), member);
          }
        }
        ClassMember::IndexSignature(index) => {
          let member = ClassMemberInfo {
            name: match index.kind {
              crate::IndexKind::String => "[string]".to_string(),
              crate::IndexKind::Number => "[number]".to_string(),
            },
            ty: index.ty.clone(),
            accessibility: Accessibility::Public,
            declared_in: id,
            optional: false,
            kind: ClassMemberKind::Indexer,
          };
          match (index.is_static, index.kind) {
            (false, crate::IndexKind::String) => info.instance_string_index = Some(member),
            (false, crate::IndexKind::Number) => info.instance_number_index = Some(member),
            (true, crate::IndexKind::String) => info.static_string_index = Some(member),
            (true, crate::IndexKind::Number) => info.static_number_index = Some(member),
          }
        }
      }
    }

    self.class_info_cache.insert(id, info.clone());
    visiting.remove(&id);
    Ok(info)
  }

  fn interface_info(
    &mut self,
    id: InterfaceId,
    visiting: &mut HashSet<InterfaceId>,
  ) -> Result<ObjectType, Diagnostic> {
    if let Some(info) = self.interface_cache.get(&id) {
      return Ok(info.clone());
    }
    if !visiting.insert(id) {
      return Err(Diagnostic::new(
        DiagnosticCode::ExtendsIncompatible,
        format!("Cycle detected while resolving interfaces for #{}", id),
      ));
    }
    let def = self.interfaces[id].clone();
    let mut obj = ObjectType::new();
    for base in &def.extends {
      let base_obj = self.interface_info(*base, visiting)?;
      for (name, prop) in base_obj.properties {
        obj.properties.insert(name, prop);
      }
      if obj.string_index.is_none() {
        obj.string_index = base_obj.string_index.clone();
      }
      if obj.number_index.is_none() {
        obj.number_index = base_obj.number_index.clone();
      }
    }
    for (name, prop) in &def.properties {
      obj.properties.insert(name.clone(), prop.clone());
    }
    if def.string_index.is_some() {
      obj.string_index = def.string_index.clone();
    }
    if def.number_index.is_some() {
      obj.number_index = def.number_index.clone();
    }
    self.interface_cache.insert(id, obj.clone());
    visiting.remove(&id);
    Ok(obj)
  }

  fn class_instance_assignable(
    &mut self,
    source_id: ClassId,
    target_id: ClassId,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    let source_info = match self.class_info(source_id, &mut HashSet::new()) {
      Ok(info) => info,
      Err(_) => return false,
    };
    let target_info = match self.class_info(target_id, &mut HashSet::new()) {
      Ok(info) => info,
      Err(_) => return false,
    };
    self.members_assignable(
      &source_info.instance_members,
      source_info.instance_string_index.as_ref(),
      source_info.instance_number_index.as_ref(),
      &target_info.instance_members,
      target_info.instance_string_index.as_ref(),
      target_info.instance_number_index.as_ref(),
      seen,
    )
  }

  fn class_statics_assignable(
    &mut self,
    source_id: ClassId,
    target_id: ClassId,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    let source_info = match self.class_info(source_id, &mut HashSet::new()) {
      Ok(info) => info,
      Err(_) => return false,
    };
    let target_info = match self.class_info(target_id, &mut HashSet::new()) {
      Ok(info) => info,
      Err(_) => return false,
    };
    self.members_assignable(
      &source_info.static_members,
      source_info.static_string_index.as_ref(),
      source_info.static_number_index.as_ref(),
      &target_info.static_members,
      target_info.static_string_index.as_ref(),
      target_info.static_number_index.as_ref(),
      seen,
    )
  }

  fn members_assignable(
    &mut self,
    source: &BTreeMap<String, ClassMemberInfo>,
    source_string_index: Option<&ClassMemberInfo>,
    source_number_index: Option<&ClassMemberInfo>,
    target: &BTreeMap<String, ClassMemberInfo>,
    target_string_index: Option<&ClassMemberInfo>,
    target_number_index: Option<&ClassMemberInfo>,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    for (name, target_member) in target {
      if let Some(source_member) = source.get(name) {
        if !self.member_compatible(source_member, target_member, seen) {
          return false;
        }
      } else if target_member.optional {
        continue;
      } else {
        // Use index signatures if available.
        let use_string_index = source_string_index
          .filter(|_| source_number_index.is_none())
          .or(source_string_index);
        let provided_by_index = match use_string_index {
          Some(index) => self.is_assignable_inner(&index.ty, &target_member.ty, seen),
          None => {
            if let Some(num_index) = source_number_index {
              self.is_assignable_inner(&num_index.ty, &target_member.ty, seen)
            } else {
              false
            }
          }
        };
        if !provided_by_index {
          return false;
        }
      }
    }
    // Target index signatures must be satisfied.
    if let Some(target_index) = target_string_index {
      let compatible = match source_string_index {
        Some(source_index) => self.is_assignable_inner(&source_index.ty, &target_index.ty, seen),
        None => false,
      };
      if !compatible {
        return false;
      }
    }
    if let Some(target_index) = target_number_index {
      let compatible = match source_number_index {
        Some(source_index) => self.is_assignable_inner(&source_index.ty, &target_index.ty, seen),
        None => false,
      };
      if !compatible {
        return false;
      }
    }
    true
  }

  fn member_compatible(
    &mut self,
    source: &ClassMemberInfo,
    target: &ClassMemberInfo,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    match target.accessibility {
      Accessibility::Private => {
        if source.accessibility != Accessibility::Private
          || source.declared_in != target.declared_in
        {
          return false;
        }
      }
      Accessibility::Protected => {
        if source.accessibility != Accessibility::Protected
          || source.declared_in != target.declared_in
        {
          return false;
        }
      }
      Accessibility::Public => {}
    }
    self.is_assignable_inner(&source.ty, &target.ty, seen)
  }

  fn object_assignable_types(
    &mut self,
    source: &ObjectType,
    target: &ObjectType,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    for (name, target_prop) in &target.properties {
      if let Some(source_prop) = source.properties.get(name) {
        if !self.is_assignable_inner(&source_prop.ty, &target_prop.ty, seen) {
          return false;
        }
      } else if target_prop.optional {
        continue;
      } else if let Some(index) = &source.string_index {
        if !self.is_assignable_inner(index, &target_prop.ty, seen) {
          return false;
        }
      } else {
        return false;
      }
    }
    if let Some(target_index) = &target.string_index {
      match &source.string_index {
        Some(source_index) => {
          if !self.is_assignable_inner(source_index, target_index, seen) {
            return false;
          }
        }
        None => return false,
      }
    }
    if let Some(target_index) = &target.number_index {
      match &source.number_index {
        Some(source_index) => {
          if !self.is_assignable_inner(source_index, target_index, seen) {
            return false;
          }
        }
        None => return false,
      }
    }
    true
  }

  fn class_as_object(&mut self, class_id: ClassId) -> Option<ObjectType> {
    let info = self.class_info(class_id, &mut HashSet::new()).ok()?;
    let mut obj = ObjectType::new();
    for (name, member) in info.instance_members {
      if matches!(member.accessibility, Accessibility::Public) {
        let ty = if matches!(member.kind, ClassMemberKind::Method) {
          match member.ty.clone() {
            Type::Function(mut f) => {
              f.this_param = None;
              Type::Function(f)
            }
            other => other,
          }
        } else {
          member.ty.clone()
        };
        obj.properties.insert(name, ObjectProperty {
          ty,
          optional: member.optional,
        });
      }
    }
    obj.string_index = info.instance_string_index.map(|m| Box::new(m.ty));
    obj.number_index = info.instance_number_index.map(|m| Box::new(m.ty));
    Some(obj)
  }

  fn function_assignable(
    &mut self,
    source: &FunctionType,
    target: &FunctionType,
    seen: &mut HashSet<(Type, Type)>,
  ) -> bool {
    match (&source.this_param, &target.this_param) {
      (Some(s), Some(t)) => {
        if !self.is_assignable_inner(t, s, seen) {
          return false;
        }
      }
      (None, None) => {}
      (None, Some(_)) | (Some(_), None) => return false,
    }
    if source.params.len() != target.params.len() {
      return false;
    }
    for (s, t) in source.params.iter().zip(target.params.iter()) {
      if !self.is_assignable_inner(t, s, seen) {
        return false;
      }
    }
    self.is_assignable_inner(&source.return_type, &target.return_type, seen)
  }

  fn ensure_accessible(
    &mut self,
    member: &ClassMemberInfo,
    accessor: Option<ClassId>,
    _is_static: bool,
  ) -> Result<(), Diagnostic> {
    match member.accessibility {
      Accessibility::Public => Ok(()),
      Accessibility::Private => {
        if Some(member.declared_in) == accessor {
          Ok(())
        } else {
          Err(Diagnostic::new(
            DiagnosticCode::InvalidMemberAccess,
            format!("Cannot access private member `{}`", member.name),
          ))
        }
      }
      Accessibility::Protected => {
        if let Some(accessor) = accessor {
          if accessor == member.declared_in || self.is_subclass(accessor, member.declared_in) {
            Ok(())
          } else {
            Err(Diagnostic::new(
              DiagnosticCode::InvalidMemberAccess,
              format!(
                "Cannot access protected member `{}` from unrelated class",
                member.name
              ),
            ))
          }
        } else {
          Err(Diagnostic::new(
            DiagnosticCode::InvalidMemberAccess,
            format!(
              "Cannot access protected member `{}` without class context",
              member.name
            ),
          ))
        }
      }
    }
  }

  fn is_subclass(&mut self, sub: ClassId, sup: ClassId) -> bool {
    let mut current = Some(sub);
    let mut seen = HashSet::new();
    while let Some(id) = current {
      if id == sup {
        return true;
      }
      if !seen.insert(id) {
        break;
      }
      let info = match self.class_info(id, &mut HashSet::new()) {
        Ok(info) => info,
        Err(_) => break,
      };
      current = info.extends;
    }
    false
  }

  fn check_class_body(&mut self, class_id: ClassId, options: &CheckOptions) -> CheckResult {
    let mut diagnostics = Vec::new();
    let def = self.classes[class_id].clone();

    // Ensure base class exists and is resolved without cycles.
    if let Some(base) = def.extends {
      if self.class_info(base, &mut HashSet::new()).is_err() {
        diagnostics.push(Diagnostic::new(
          DiagnosticCode::ExtendsIncompatible,
          format!("Unable to resolve base class for `{}`", def.name),
        ));
      }
    }

    let info = self.class_info(class_id, &mut HashSet::new());
    if info.is_err() {
      diagnostics.push(Diagnostic::new(
        DiagnosticCode::ExtendsIncompatible,
        format!("Unable to compute class info for `{}`", def.name),
      ));
      return CheckResult { diagnostics };
    }
    let _info = info.unwrap();

    // Implements checks: instance side must be assignable to each interface.
    for iface in &def.implements {
      if !self.is_assignable(&Type::ClassInstance(class_id), iface) {
        diagnostics.push(Diagnostic::new(
          DiagnosticCode::ImplementsIncompatible,
          format!(
            "Class `{}` is not assignable to implemented interface",
            def.name
          ),
        ));
      }
    }

    if options.strict_property_initialization {
      let mut initialized = HashSet::new();
      if let Some(constructor) = def.constructor.clone() {
        for param in constructor.params {
          if param.property.is_some() {
            initialized.insert(param.name.clone());
          }
        }
        for assigned in constructor.assigns {
          initialized.insert(assigned);
        }
      }
      for member in &def.members {
        if let ClassMember::Field(field) = member {
          if field.is_static || field.optional {
            continue;
          }
          if field.has_initializer || field.definite || initialized.contains(&field.name) {
            continue;
          }
          diagnostics.push(Diagnostic::new(
            DiagnosticCode::PropertyNotDefinitelyAssigned,
            format!(
              "Property `{}` is not definitely assigned in the constructor",
              field.name
            ),
          ));
        }
      }
    }

    CheckResult { diagnostics }
  }
}

pub use class::check_body;
pub use class::type_of_def;
