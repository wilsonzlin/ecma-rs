use minify_js::minify_str;
use minify_js::TopLevelMode;
use std::env;
use std::fs::File;
use std::io::Read;
use std::time::Instant;

fn main() {
  let args: Vec<String> = env::args().collect();
  let mut code = Vec::new();
  File::open(&args[1])
    .expect("open file")
    .read_to_end(&mut code)
    .expect("read file");
  let src_str = std::str::from_utf8(&code).expect("input must be valid UTF-8");

  let iterations = u64::from_str_radix(&args[2], 10).expect("parse iterations argument");
  let mut output_len = 0;
  let mut output = Vec::new();
  let started = Instant::now();
  for _ in 0..iterations {
    output.clear();
    minify_str(TopLevelMode::Global, src_str, &mut output).expect("minify");
    output_len = output.len();
  }
  let elapsed_ns = started.elapsed().as_nanos();

  println!("{} {}", output_len, elapsed_ns);
}
