//! Unannotated instance field initializers refine the class instance type
//! (`three = 3` → `number`; numeric keys like `1 = ''` included), so reads
//! through the declared instance type (`var c: C; c.three`, `c[1]`) are
//! precise. Previously only annotated fields carried their type and the rest
//! stayed `unknown`, cascading into TS2403 on same-name `var` redeclarations
//! (`numericIndexingResults.ts`).

use typecheck_ts::{FileKey, MemoryHost, Program};

fn run(src: &str) -> (Program, typecheck_ts::FileId) {
  let mut host = MemoryHost::default();
  let file = FileKey::new("t.ts");
  host.insert(file.clone(), src);
  let program = Program::new(host, vec![file.clone()]);
  let file_id = program.file_id(&file).expect("file id");
  (program, file_id)
}

fn def_type(program: &Program, file: typecheck_ts::FileId, name: &str) -> String {
  let def = program
    .definitions_in_file(file)
    .into_iter()
    .find(|d| program.def_name(*d).as_deref() == Some(name))
    .unwrap_or_else(|| panic!("def {name} not found"));
  program.display_type(program.type_of_def(def)).to_string()
}

#[test]
fn unannotated_field_init_types_reach_instance_reads() {
  let src = "class C {\n    three = 3;\n    word = 'w';\n}\nvar c: C;\nvar t = c.three;\nvar w = c.word;\nvar c2 = new C();\nvar t2 = c2.three;\n";
  let (program, file_id) = run(src);
  // Unassigned `var c: C` reads are TS2454 (tsc agrees); nothing else.
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  assert_eq!(codes, ["TS2454", "TS2454"]);
  assert_eq!(def_type(&program, file_id, "t"), "number");
  assert_eq!(def_type(&program, file_id, "w"), "string");
  assert_eq!(def_type(&program, file_id, "t2"), "number");
}

#[test]
fn numeric_named_field_init_types_reach_index_reads() {
  let src = "class C {\n    [x: number]: string;\n    1 = '';\n    \"2\" = ''\n}\nvar c: C;\nvar one = c[1];\nvar two = c[\"2\"];\nvar three = c[\"3\"];\n";
  let (program, file_id) = run(src);
  assert_eq!(def_type(&program, file_id, "one"), "string");
  assert_eq!(def_type(&program, file_id, "two"), "string");
  // Numeric-string read with no declared member still hits the indexer.
  assert_eq!(def_type(&program, file_id, "three"), "string");
}

#[test]
fn annotated_fields_keep_declared_type() {
  let src = "class C {\n    four: number = 4;\n}\nvar c = new C();\nvar f = c.four;\nvar bad: string = c.four;\n";
  let (program, file_id) = run(src);
  assert_eq!(def_type(&program, file_id, "f"), "number");
  let codes: Vec<_> = program
    .check()
    .into_iter()
    .map(|d| d.code.as_str().to_string())
    .collect();
  assert_eq!(codes, ["TS2322"]);
}

#[test]
fn interface_numeric_members_type_reads() {
  // Interface member types come from their annotations (no inference needed).
  let src = "interface I {\n    [x: number]: string;\n    1: string;\n    \"2\": string;\n}\nvar i: I;\nvar one = i[1];\nvar two = i[\"2\"];\nvar three = i[\"3\"];\n";
  let (program, file_id) = run(src);
  assert_eq!(def_type(&program, file_id, "one"), "string");
  assert_eq!(def_type(&program, file_id, "two"), "string");
  assert_eq!(def_type(&program, file_id, "three"), "string");
}
