use typecheck_ts_class17::check_body;
use typecheck_ts_class17::types::ObjectProperty;
use typecheck_ts_class17::Accessibility;
use typecheck_ts_class17::CheckOptions;
use typecheck_ts_class17::ClassDef;
use typecheck_ts_class17::ClassField;
use typecheck_ts_class17::ClassIndexSignature;
use typecheck_ts_class17::ClassMember;
use typecheck_ts_class17::ClassMethod;
use typecheck_ts_class17::Constructor;
use typecheck_ts_class17::ConstructorParam;
use typecheck_ts_class17::DefId;
use typecheck_ts_class17::DiagnosticCode;
use typecheck_ts_class17::FunctionType;
use typecheck_ts_class17::IndexKind;
use typecheck_ts_class17::InterfaceDef;
use typecheck_ts_class17::Type;
use typecheck_ts_class17::TypeChecker;

#[test]
fn private_nominal_blocks_structural_assignment() {
  let mut checker = TypeChecker::new();

  let mut class_a = ClassDef::new("A");
  let mut field_a = ClassField::new("secret", Type::Number);
  field_a.accessibility = Accessibility::Private;
  class_a.members.push(ClassMember::Field(field_a));
  let a_id = checker.add_class(class_a);

  let mut class_b = ClassDef::new("B");
  let mut field_b = ClassField::new("secret", Type::Number);
  field_b.accessibility = Accessibility::Private;
  class_b.members.push(ClassMember::Field(field_b));
  let b_id = checker.add_class(class_b);

  assert!(!checker.is_assignable(&Type::ClassInstance(a_id), &Type::ClassInstance(b_id)));
  assert!(!checker.is_assignable(&Type::ClassInstance(b_id), &Type::ClassInstance(a_id)));

  let mut derived = ClassDef::new("Derived");
  derived.extends = Some(a_id);
  let d_id = checker.add_class(derived);
  assert!(checker.is_assignable(&Type::ClassInstance(d_id), &Type::ClassInstance(a_id)));
  assert!(checker.is_assignable(&Type::ClassInstance(a_id), &Type::ClassInstance(d_id)));
}

#[test]
fn protected_members_require_shared_origin() {
  let mut checker = TypeChecker::new();

  let mut base = ClassDef::new("Base");
  let mut prot = ClassField::new("value", Type::Number);
  prot.accessibility = Accessibility::Protected;
  base.members.push(ClassMember::Field(prot));
  let base_id = checker.add_class(base);

  let mut left = ClassDef::new("Left");
  left.extends = Some(base_id);
  let left_id = checker.add_class(left);

  let mut right = ClassDef::new("Right");
  right.extends = Some(base_id);
  let right_id = checker.add_class(right);

  assert!(checker.is_assignable(
    &Type::ClassInstance(left_id),
    &Type::ClassInstance(right_id)
  ));
  assert!(checker.is_assignable(
    &Type::ClassInstance(right_id),
    &Type::ClassInstance(left_id)
  ));

  let mut other_base = ClassDef::new("OtherBase");
  let mut other_field = ClassField::new("value", Type::Number);
  other_field.accessibility = Accessibility::Protected;
  other_base.members.push(ClassMember::Field(other_field));
  let other_base_id = checker.add_class(other_base);

  let mut other = ClassDef::new("Other");
  other.extends = Some(other_base_id);
  let other_id = checker.add_class(other);

  assert!(!checker.is_assignable(
    &Type::ClassInstance(other_id),
    &Type::ClassInstance(left_id)
  ));
}

#[test]
fn implements_checks_structural_members() {
  let mut checker = TypeChecker::new();
  let mut iface = InterfaceDef::new("I");
  iface.properties.insert(
    "x".into(),
    ObjectProperty {
      ty: Type::Number,
      optional: false,
    },
  );
  iface.properties.insert(
    "m".into(),
    ObjectProperty {
      ty: Type::Function(FunctionType::new(vec![], Type::Number)),
      optional: false,
    },
  );
  let iface_id = checker.add_interface(iface);

  let mut good = ClassDef::new("Good");
  let mut field = ClassField::new("x", Type::Number);
  field.has_initializer = true;
  good.members.push(ClassMember::Field(field));
  let method = ClassMethod::new("m", FunctionType::new(vec![], Type::Number));
  good.members.push(ClassMember::Method(method));
  good.implements.push(Type::Interface(iface_id));
  let good_id = checker.add_class(good);
  let res = check_body(
    &mut checker,
    DefId::Class(good_id),
    &CheckOptions::default(),
  );
  assert!(res.diagnostics.is_empty());

  let mut bad = ClassDef::new("Bad");
  let mut bad_field = ClassField::new("x", Type::String);
  bad_field.accessibility = Accessibility::Public;
  bad_field.has_initializer = true;
  bad.members.push(ClassMember::Field(bad_field));
  bad.implements.push(Type::Interface(iface_id));
  let bad_id = checker.add_class(bad);
  let res_bad = check_body(&mut checker, DefId::Class(bad_id), &CheckOptions::default());
  assert_eq!(res_bad.diagnostics.len(), 1);
  assert_eq!(
    res_bad.diagnostics[0].code,
    DiagnosticCode::ImplementsIncompatible
  );
}

#[test]
fn strict_initialization_enforced() {
  let mut checker = TypeChecker::new();

  let mut with_ctor = ClassDef::new("WithCtor");
  let field = ClassField::new("x", Type::Number);
  with_ctor.members.push(ClassMember::Field(field));
  let mut ctor = Constructor::new(vec![]);
  ctor.assigns.push("x".to_string());
  with_ctor.constructor = Some(ctor);
  let with_ctor_id = checker.add_class(with_ctor);
  let res = check_body(
    &mut checker,
    DefId::Class(with_ctor_id),
    &CheckOptions::default(),
  );
  assert!(res.diagnostics.is_empty());

  let mut missing = ClassDef::new("Missing");
  let missing_field = ClassField::new("y", Type::Number);
  missing.members.push(ClassMember::Field(missing_field));
  let missing_id = checker.add_class(missing);
  let res_missing = check_body(
    &mut checker,
    DefId::Class(missing_id),
    &CheckOptions::default(),
  );
  assert_eq!(res_missing.diagnostics.len(), 1);
  assert_eq!(
    res_missing.diagnostics[0].code,
    DiagnosticCode::PropertyNotDefinitelyAssigned
  );

  let param_ctor = Constructor::new(vec![{
    let mut p = ConstructorParam::new("p", Type::Number);
    p.property = Some(Accessibility::Public);
    p
  }]);
  let mut param_class = ClassDef::new("ParamProp");
  param_class.constructor = Some(param_ctor);
  let param_id = checker.add_class(param_class);
  let res_param = check_body(
    &mut checker,
    DefId::Class(param_id),
    &CheckOptions::default(),
  );
  assert!(res_param.diagnostics.is_empty());
}

#[test]
fn this_parameters_are_contextual() {
  let mut checker = TypeChecker::new();
  let mut class_def = ClassDef::new("HasThis");
  let method_fn = FunctionType::new(vec![], Type::Void);
  let method = ClassMethod::new("m", method_fn);
  class_def.members.push(ClassMember::Method(method));
  let explicit_fn = FunctionType::new(vec![], Type::Void).with_this(Type::Number);
  let explicit_method = ClassMethod::new("explicit", explicit_fn);
  class_def.members.push(ClassMember::Method(explicit_method));
  let class_id = checker.add_class(class_def);

  let inferred = checker
    .check_property_access(&Type::ClassInstance(class_id), "m", Some(class_id))
    .expect("method available");
  let this_ty = match &inferred {
    Type::Function(f) => f.this_param.as_ref().map(|b| *b.clone()),
    _ => None,
  };
  assert_eq!(this_ty, Some(Type::ClassInstance(class_id)));

  let explicit = checker
    .check_property_access(&Type::ClassInstance(class_id), "explicit", Some(class_id))
    .expect("method available");
  let explicit_this = match &explicit {
    Type::Function(f) => f.this_param.as_ref().map(|b| *b.clone()),
    _ => None,
  };
  assert_eq!(explicit_this, Some(Type::Number));

  let target_callback = Type::Function(FunctionType {
    this_param: Some(Box::new(Type::Void)),
    params: vec![],
    return_type: Box::new(Type::Void),
  });
  assert!(!checker.is_assignable(&inferred, &target_callback));
}

#[test]
fn member_access_respects_visibility() {
  let mut checker = TypeChecker::new();
  let mut class_def = ClassDef::new("Secret");
  let mut secret = ClassField::new("secret", Type::Number);
  secret.accessibility = Accessibility::Private;
  class_def.members.push(ClassMember::Field(secret));
  let mut shared = ClassField::new("shared", Type::Number);
  shared.accessibility = Accessibility::Protected;
  class_def.members.push(ClassMember::Field(shared));
  let class_id = checker.add_class(class_def);

  let err = checker
    .check_property_access(&Type::ClassInstance(class_id), "secret", None)
    .unwrap_err();
  assert_eq!(err.code, DiagnosticCode::InvalidMemberAccess);

  assert!(checker
    .check_property_access(&Type::ClassInstance(class_id), "secret", Some(class_id))
    .is_ok());

  let mut subclass = ClassDef::new("Sub");
  subclass.extends = Some(class_id);
  let sub_id = checker.add_class(subclass);
  assert!(checker
    .check_property_access(&Type::ClassInstance(class_id), "shared", Some(sub_id))
    .is_ok());
  assert!(checker
    .check_property_access(&Type::ClassInstance(class_id), "secret", Some(sub_id))
    .is_err());
}

#[test]
fn class_index_signatures_used_in_assignability() {
  let mut checker = TypeChecker::new();
  let mut iface = InterfaceDef::new("Dict");
  iface.string_index = Some(Box::new(Type::Number));
  let iface_id = checker.add_interface(iface);

  let mut class_def = ClassDef::new("DictClass");
  let index = ClassIndexSignature::new(IndexKind::String, Type::Number);
  class_def.members.push(ClassMember::IndexSignature(index));
  class_def.implements.push(Type::Interface(iface_id));
  let class_id = checker.add_class(class_def);

  let res = check_body(
    &mut checker,
    DefId::Class(class_id),
    &CheckOptions::default(),
  );
  assert!(res.diagnostics.is_empty());
  assert!(checker.is_assignable(&Type::ClassInstance(class_id), &Type::Interface(iface_id)));
}
