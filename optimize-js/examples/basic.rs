use diagnostics::render::render_diagnostic;
use diagnostics::{sort_diagnostics, SimpleFiles};
use emit_js::EmitOptions;
use optimize_js::{compile_source, program_to_js, DecompileOptions, TopLevelMode};

const SOURCE: &str = r#"
while (true) {}
"#;

fn main() {
  let program = match compile_source(SOURCE, TopLevelMode::Module, false) {
    Ok(program) => program,
    Err(mut diagnostics) => {
      sort_diagnostics(&mut diagnostics);
      let mut files = SimpleFiles::new();
      files.add("example.js", SOURCE);
      for diagnostic in diagnostics {
        print!("{}", render_diagnostic(&files, &diagnostic));
      }
      return;
    }
  };

  let decompile = DecompileOptions {
    // Ensures the emitted output declares any SSA temporaries before use,
    // producing runnable JS even when a value is referenced multiple times.
    declare_registers: true,
    ..DecompileOptions::default()
  };
  let bytes = program_to_js(&program, &decompile, EmitOptions::minified())
    .expect("decompile + emit optimized JS");
  println!("{}", String::from_utf8_lossy(&bytes));
}
