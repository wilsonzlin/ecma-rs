use emit_js::{emit_class_decl, emit_stmt, EmitOptions, Emitter};
use parse_js::ast::class_or_object::{ClassMember, ClassOrObjKey, ClassOrObjVal};
use parse_js::ast::node::Node;
use parse_js::ast::stmt::decl::{Accessibility, ClassDecl};
use parse_js::ast::stmt::Stmt;
use parse_js::ast::stx::TopLevel;

fn emitter_output(mut f: impl FnMut(&mut Emitter)) -> String {
  let mut em = Emitter::new(EmitOptions::default());
  f(&mut em);
  String::from_utf8(em.into_bytes()).expect("emitted bytes should be valid UTF-8")
}

fn emit_class_to_string(decl: &Node<ClassDecl>) -> String {
  emitter_output(|em| emit_class_decl(em, decl).expect("emit should succeed"))
}

fn emit_stmt_to_string(stmt: &Node<Stmt>) -> String {
  emitter_output(|em| emit_stmt(em, stmt).expect("emit should succeed"))
}

fn parse_class_stmt(source: &str) -> Node<Stmt> {
  let parsed = parse_js::parse(source).expect("source should parse");
  let TopLevel { mut body } = *parsed.stx;
  body.pop().expect("expected one statement")
}

fn parse_class(source: &str) -> Node<ClassDecl> {
  let stmt = parse_class_stmt(source);
  match *stmt.stx {
    Stmt::ClassDecl(decl) => decl,
    other => panic!("unexpected statement: {other:?}"),
  }
}

fn find_member<'a>(class: &'a ClassDecl, name: &str) -> &'a ClassMember {
  class
    .members
    .iter()
    .map(|m| m.stx.as_ref())
    .find(|member| matches!(&member.key, ClassOrObjKey::Direct(k) if k.stx.key == name))
    .expect("member not found")
}

#[test]
fn roundtrips_decorated_export_default_class() {
  let source = r#"
    @dec1
    @dec2
    export default class Foo {}
  "#;
  let decl = parse_class(source);
  let emitted = emit_class_to_string(&decl);
  let reparsed = parse_class(&emitted);

  assert!(reparsed.stx.export);
  assert!(reparsed.stx.export_default);
  assert_eq!(reparsed.stx.decorators.len(), 2);

  let re_emitted = emit_class_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}

#[test]
fn emits_modifiers_and_properties() {
  let source = r#"
    class Foo {
      public readonly foo?: string;
      protected override accessor bar!: number;
      abstract baz(): void;
    }
  "#;
  let decl = parse_class(source);
  let emitted = emit_class_to_string(&decl);
  let reparsed = parse_class(&emitted);
  let class = reparsed.stx.as_ref();

  let foo = find_member(class, "foo");
  assert!(matches!(foo.accessibility, Some(Accessibility::Public)));
  assert!(foo.readonly);
  assert!(foo.optional);
  assert!(foo.type_annotation.is_some());
  assert!(matches!(foo.val, ClassOrObjVal::Prop(_)));

  let bar = find_member(class, "bar");
  assert!(matches!(bar.accessibility, Some(Accessibility::Protected)));
  assert!(bar.override_);
  assert!(bar.accessor);
  assert!(bar.definite_assignment);
  assert!(bar.type_annotation.is_some());

  let baz = find_member(class, "baz");
  assert!(baz.abstract_);
  match &baz.val {
    ClassOrObjVal::Method(method) => assert!(method.stx.func.stx.body.is_none()),
    other => panic!("expected method, got {other:?}"),
  }

  let re_emitted = emit_class_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}

#[test]
fn emits_getters_setters_and_methods_with_varied_keys() {
  let source = r#"
    class Foo {
      get "foo"() {}
      set bar(value) {}
      "baz"() {}
      *[sym]() {}
    }
  "#;
  let decl = parse_class(source);
  let emitted = emit_class_to_string(&decl);
  let reparsed = parse_class(&emitted);
  let class = reparsed.stx.as_ref();

  let original_variants: Vec<&'static str> = decl
    .stx
    .members
    .iter()
    .map(|m| match &m.stx.val {
      ClassOrObjVal::Getter(_) => "getter",
      ClassOrObjVal::Setter(_) => "setter",
      ClassOrObjVal::Method(_) => "method",
      ClassOrObjVal::Prop(_) => "prop",
      ClassOrObjVal::IndexSignature(_) => "index",
      ClassOrObjVal::StaticBlock(_) => "static",
    })
    .collect();

  let has_getter = class
    .members
    .iter()
    .any(|m| matches!(&m.stx.val, ClassOrObjVal::Getter(_)));
  let has_setter = class
    .members
    .iter()
    .any(|m| matches!(&m.stx.val, ClassOrObjVal::Setter(_)));
  let has_generator_method = class.members.iter().any(|m| {
    matches!(
      &m.stx.val,
      ClassOrObjVal::Method(method) if method.stx.func.stx.generator
    )
  });
  let has_string_key_method = class.members.iter().any(|m| {
    matches!(
      &m.stx.key,
      ClassOrObjKey::Direct(k)
        if k.stx.key == "baz" && matches!(k.stx.tt, parse_js::token::TT::LiteralString)
    )
  });

  if !(has_getter && has_setter && has_generator_method && has_string_key_method) {
    let variants: Vec<&'static str> = class
      .members
      .iter()
      .map(|m| match &m.stx.val {
        ClassOrObjVal::Getter(_) => "getter",
        ClassOrObjVal::Setter(_) => "setter",
        ClassOrObjVal::Method(_) => "method",
        ClassOrObjVal::Prop(_) => "prop",
        ClassOrObjVal::IndexSignature(_) => "index",
        ClassOrObjVal::StaticBlock(_) => "static",
      })
      .collect();
    panic!(
      "missing expected members; emitted: {emitted}; variants: {variants:?}; original: {original_variants:?}"
    );
  }

  let re_emitted = emit_class_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}

#[test]
fn emits_static_blocks_and_index_signatures() {
  let source = r#"
    class Foo {
      static { this.x = 1; }
      [key: string]: number;
    }
  "#;
  let stmt = parse_class_stmt(source);
  let emitted = emit_stmt_to_string(&stmt);
  let reparsed = parse_class(&emitted);
  let class = reparsed.stx.as_ref();

  assert!(class
    .members
    .iter()
    .any(|m| matches!(m.stx.val, ClassOrObjVal::StaticBlock(_))));
  assert!(class
    .members
    .iter()
    .any(|m| matches!(m.stx.val, ClassOrObjVal::IndexSignature(_))));

  let re_emitted = emit_class_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}

#[test]
fn emits_definite_assignment_properties_with_types() {
  let source = r#"
    class Foo {
      value!: number;
      optional?: string;
    }
  "#;
  let decl = parse_class(source);
  let emitted = emit_class_to_string(&decl);
  let reparsed = parse_class(&emitted);
  let class = reparsed.stx.as_ref();

  let value = find_member(class, "value");
  assert!(value.definite_assignment);
  assert!(value.type_annotation.is_some());

  let optional = find_member(class, "optional");
  assert!(optional.optional);
  assert!(optional.type_annotation.is_some());

  let re_emitted = emit_class_to_string(&reparsed);
  assert_eq!(emitted, re_emitted);
}

