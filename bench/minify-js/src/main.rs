use minify_js::minify;
use minify_js::TopLevelMode;
use std::env;
use std::fs::read_to_string;
use std::time::Instant;

fn main() {
  let args: Vec<String> = env::args().collect();
  let code = read_to_string(&args[1]).expect("read file");

  let iterations = u64::from_str_radix(&args[2], 10).expect("parse iterations argument");
  let mut output_len = 0;
  let mut output = Vec::new();
  let started = Instant::now();
  for _ in 0..iterations {
    output.clear();
    minify(TopLevelMode::Global, &code, &mut output).expect("minify");
    output_len = output.len();
  }
  let elapsed_ns = started.elapsed().as_nanos();

  println!("{} {}", output_len, elapsed_ns);
}
