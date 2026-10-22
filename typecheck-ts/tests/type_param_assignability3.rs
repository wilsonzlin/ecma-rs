use typecheck_ts::{FileKey, MemoryHost, Program};

fn diags(src: &str) -> Vec<(String, u32, String)> {
  let file = FileKey::new("mod.ts");
  let mut host = MemoryHost::default();
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file]);
  program
    .check()
    .into_iter()
    .map(|d| (d.code.to_string(), d.primary.range.start, d.message.clone()))
    .collect()
}

#[test]
fn class_field_type_params_resolve_without_arrow() {
  let d = diags(
    r#"
class Foo { foo: string; }
class C<T extends Foo, U extends Foo> {
  t: T;
  u: U;
}
"#,
  );
  eprintln!("no-arrow diags={d:?}");
  assert!(
    !d.iter().any(|(c, _, _)| c == "TC2008"),
    "field anns T/U should resolve, got {d:?}"
  );
}

#[test]
fn nested_arrow_this_assigns_reject_unrelated_type_params() {
  let src = r#"
class Foo { foo: string; }
class C<T extends Foo, U extends Foo> {
  t: T;
  u: U;
  r = () => {
    this.t = this.u; // error
    this.u = this.t; // error
  }
}
"#;
  let d = diags(src);
  eprintln!("arrow diags={d:?}");
  let starts: Vec<u32> = d
    .iter()
    .filter(|(c, _, _)| c == "TS2322")
    .map(|(_, s, _)| *s)
    .collect();
  let ttu = src.find("this.t = this.u").unwrap() as u32;
  let tut = src.find("this.u = this.t").unwrap() as u32;
  assert!(
    starts.iter().any(|&s| s >= ttu && s < ttu + 20),
    "this.t=this.u, starts={starts:?}"
  );
  assert!(
    starts.iter().any(|&s| s >= tut && s < tut + 20),
    "this.u=this.t, starts={starts:?}"
  );
  assert!(
    !d.iter().any(|(c, _, _)| c == "TC2008"),
    "unexpected TC2008: {d:?}"
  );
}
