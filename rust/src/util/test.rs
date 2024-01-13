use serde_json::to_string_pretty;
use serde_json::to_writer_pretty;
use serde_json::Value;
use similar::ChangeTag;
use similar::TextDiff;
use std::env;
use std::env::var;
use std::fs::read_dir;
use std::fs::File;
use std::io::Read;

pub fn evaluate_test_input_files<T: Fn(Vec<u8>) -> Value>(dir_in_src: &str, tester: T) {
  let base_dir = format!("{}/src/{}", env!("CARGO_MANIFEST_DIR"), dir_in_src);
  for f_typ in read_dir(&base_dir).unwrap() {
    let f_typ = f_typ.unwrap();
    if f_typ.file_type().unwrap().is_dir() {
      let typ = f_typ.file_name().to_str().unwrap().to_string();
      for f_name in read_dir(format!("{}/{}", base_dir, typ)).unwrap() {
        let f_name = f_name.unwrap();
        let name = f_name.file_name().to_str().unwrap().to_string();
        if name.ends_with(".js") {
          let mut input = vec![];
          File::open(format!("{}/{}/{}", base_dir, typ, name))
            .unwrap()
            .read_to_end(&mut input)
            .unwrap();
          println!("Testing {}/{}...", typ, name);
          let actual = tester(input);
          let json_out_path = format!("{}/{}/{}on", base_dir, typ, name);
          let expected: Value =
            serde_json::from_reader(File::open(&json_out_path).unwrap()).unwrap();
          if actual != expected {
            if var("PARSEJS_REGENERATE_TEST_JSON_OUTPUTS").is_ok_and(|v| v == "1") {
              to_writer_pretty(File::create(&json_out_path).unwrap(), &actual).unwrap();
            } else {
              let expected_fmt = to_string_pretty(&expected).unwrap();
              let actual_fmt = to_string_pretty(&actual).unwrap();
              let mut msg = format!("Failed {}/{}, got:\n", typ, name);
              let diff = TextDiff::from_lines(&expected_fmt, &actual_fmt);
              for change in diff.iter_all_changes() {
                let sign = match change.tag() {
                  ChangeTag::Delete => "-",
                  ChangeTag::Insert => "+",
                  ChangeTag::Equal => " ",
                };
                msg.push_str(sign);
                msg.push_str(change.as_str().unwrap());
              }
              panic!("{}", msg);
            };
          }
        }
      }
    };
  }
}
