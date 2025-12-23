use std::sync::Arc;
use typecheck_ts::CompilerOptions;
use typecheck_ts::FileKind;
use typecheck_ts::Program;
use typecheck_ts::TypeDisplay;
use types_ts::TypeKind;

fn sample_program() -> (Program, semantic_js::GlobalSymbols) {
  let mut program = Program::new(CompilerOptions::default());
  let source = r#"
    type Alias = string | number;
    interface Foo { bar: Alias; baz(x: Alias): void; }
    function over(x: string): string;
    function over(x: number): number;
    function over(x: Alias) { return x as any; }
    class Klass { static s: number; value: Alias; }
  "#;
  program.add_file(FileKind::Ts, Arc::<str>::from(source));
  let globals = program.global_symbols();
  (program, globals)
}

#[test]
fn types_for_basic_decls() {
  let (program, globals) = sample_program();
  let alias = globals.lookup("Alias").unwrap()[0];
  let interface = globals.lookup("Foo").unwrap()[0];
  let class_def = globals.lookup("Klass").unwrap()[0];
  let overloads = globals.lookup("over").unwrap();

  let alias_ty = program.type_of_def(alias);
  let interface_ty = program.type_of_def(interface);
  let class_ty = program.type_of_def(class_def);
  let overload_ty = program.type_of_def(overloads[0]);

  {
    let store = program.type_store();
    let display = TypeDisplay::new(&store);
    assert_eq!(display.format(alias_ty), "string | number");
    let interface_str = display.format(interface_ty);
    assert!(interface_str.contains("bar"));
    let overload_str = display.format(overload_ty);
    assert!(overload_str.contains("(x: string)"));
    let class_str = display.format(class_ty);
    assert_eq!(class_str, "class Klass");

    if let TypeKind::Class(class) = store.get(class_ty) {
      if let TypeKind::Object(obj) = store.get(class.instance) {
        assert!(obj.properties.iter().any(|p| p.name == "value"));
      } else {
        panic!("expected class instance to be object type");
      }
    }
  }
}

#[test]
fn determinism_across_query_order() {
  let (program, globals) = sample_program();
  let alias = globals.lookup("Alias").unwrap()[0];
  let interface = globals.lookup("Foo").unwrap()[0];

  let alias_ty_first = program.type_of_def(alias);
  let interface_ty_first = program.type_of_def(interface);
  let first = {
    let store = program.type_store();
    let display = TypeDisplay::new(&store);
    (
      display.format(alias_ty_first),
      display.format(interface_ty_first),
    )
  };

  let interface_ty_second = program.type_of_def(interface);
  let alias_ty_second = program.type_of_def(alias);
  let second = {
    let store = program.type_store();
    let display = TypeDisplay::new(&store);
    (
      display.format(alias_ty_second),
      display.format(interface_ty_second),
    )
  };

  assert_eq!(first, second);
}
