use emit_js::emit_type_members;
use parse_js::ast::stmt::Stmt;

fn emit_members_from_interface(src: &str) -> String {
  let parsed = parse_js::parse(src).expect("parse failed");
  let interface = parsed
    .stx
    .body
    .into_iter()
    .find_map(|stmt| match *stmt.stx {
      Stmt::InterfaceDecl(interface) => Some(interface),
      _ => None,
    })
    .expect("no interface declaration");

  let mut out = String::new();
  emit_type_members(&mut out, &interface.stx.members).expect("emit members");
  out
}

#[test]
fn emits_property_signature() {
  let out = emit_members_from_interface("interface I{readonly foo?:string}");
  assert_eq!(out, "readonly foo?: string;");
}

#[test]
fn emits_method_signature_with_parameters() {
  let out = emit_members_from_interface("interface I{bar(x:number,y?:string,...rest:any[]):void}");
  assert_eq!(out, "bar(x: number, y?: string, ...rest: any[]): void;");
}

#[test]
fn emits_call_signatures() {
  let out = emit_members_from_interface("interface I{(x:T):U}");
  assert_eq!(out, "(x: T): U;");

  let generic = emit_members_from_interface("interface I{<T>(x:T):T}");
  assert_eq!(generic, "<T>(x: T): T;");
}

#[test]
fn emits_construct_signature() {
  let out = emit_members_from_interface("interface I{new(x:T):U}");
  assert_eq!(out, "new (x: T): U;");
}

#[test]
fn emits_index_signature() {
  let out = emit_members_from_interface("interface I{readonly [k:string]:number}");
  assert_eq!(out, "readonly [k: string]: number;");
}

#[test]
fn emits_accessors_with_separator() {
  let out = emit_members_from_interface("interface I{get x():string;set x(v:string)}");
  assert_eq!(out, "get x(): string; set x(v: string);");
}

#[test]
fn emits_type_predicate_return_types() {
  let predicate = emit_members_from_interface("interface I{isFoo(x:any):x is Foo}");
  assert_eq!(predicate, "isFoo(x: any): x is Foo;");

  let asserts_predicate =
    emit_members_from_interface("interface I{assertFoo(x:any):asserts x is Foo}");
  assert_eq!(asserts_predicate, "assertFoo(x: any): asserts x is Foo;");
}
