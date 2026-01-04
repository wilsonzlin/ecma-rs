use diagnostics::FileId;
use parse_js::{parse_with_options, Dialect, ParseOptions, SourceType};

use crate::js::{bind_js, TopLevelMode};

const MAX_DEPTH: usize = 4;
const MAX_STMTS_PER_BLOCK: usize = 4;
const MAX_BYTES_PER_STRING: usize = 24;

struct ByteCursor<'a> {
  data: &'a [u8],
  offset: usize,
}

impl<'a> ByteCursor<'a> {
  fn new(data: &'a [u8]) -> Self {
    Self { data, offset: 0 }
  }

  fn next_u8(&mut self) -> u8 {
    let b = self.data.get(self.offset).copied().unwrap_or(0);
    self.offset = self.offset.saturating_add(1);
    b
  }

  fn next_usize(&mut self, max_exclusive: usize) -> usize {
    if max_exclusive == 0 {
      return 0;
    }
    (self.next_u8() as usize) % max_exclusive
  }

  fn next_bool(&mut self) -> bool {
    self.next_u8() & 1 == 1
  }

  fn take_bytes(&mut self, max_len: usize) -> &'a [u8] {
    let len = self.next_usize(max_len + 1);
    let end = self.offset.saturating_add(len).min(self.data.len());
    let slice = &self.data[self.offset.min(self.data.len())..end];
    self.offset = end;
    slice
  }
}

fn escape_bytes_as_js_string(bytes: &[u8]) -> String {
  let mut out = String::new();
  for b in bytes {
    use std::fmt::Write;
    let _ = write!(&mut out, "\\x{b:02x}");
  }
  out
}

fn ident(cursor: &mut ByteCursor<'_>, prefix: &str) -> String {
  let len = cursor.next_usize(6) + 1;
  let mut out = String::with_capacity(prefix.len() + len);
  out.push_str(prefix);
  for _ in 0..len {
    let c = b'a' + (cursor.next_u8() % 26);
    out.push(c as char);
  }
  out
}

fn gen_block(cursor: &mut ByteCursor<'_>, depth: usize) -> String {
  let stmt_count = cursor.next_usize(MAX_STMTS_PER_BLOCK) + 1;
  let mut out = String::new();
  for _ in 0..stmt_count {
    out.push_str(&gen_stmt(cursor, depth));
  }
  out
}

fn gen_stmt(cursor: &mut ByteCursor<'_>, depth: usize) -> String {
  if depth == 0 {
    let name = ident(cursor, "v");
    let value = cursor.next_usize(8);
    return format!("var {name} = {value};");
  }

  match cursor.next_usize(7) {
    // Nested block scope.
    0 => format!("{{ {} }}", gen_block(cursor, depth - 1)),
    // Function declaration.
    1 => {
      let name = ident(cursor, "f");
      format!("function {name}() {{ {} }}", gen_block(cursor, depth - 1))
    }
    // Arrow function + block.
    2 => {
      let name = ident(cursor, "a");
      format!(
        "const {name} = () => {{ {} }};",
        gen_block(cursor, depth - 1)
      )
    }
    // `with` introduces dynamic scope.
    3 => format!("with ({{}}) {{ {} }}", gen_block(cursor, depth - 1)),
    // Direct eval call also introduces dynamic scope.
    4 => {
      let payload = escape_bytes_as_js_string(cursor.take_bytes(MAX_BYTES_PER_STRING));
      format!("eval(\"{payload}\");")
    }
    // Block scoped bindings.
    5 => {
      let name = ident(cursor, "l");
      let value = cursor.next_usize(16);
      if cursor.next_bool() {
        format!("let {name} = {value};")
      } else {
        format!("const {name} = {value};")
      }
    }
    // `try`/`catch` introduces additional scopes.
    _ => {
      let name = ident(cursor, "e");
      format!(
        "try {{ {} }} catch ({name}) {{ {} }}",
        gen_block(cursor, depth - 1),
        gen_block(cursor, depth - 1)
      )
    }
  }
}

/// Fuzz entry point that generates syntactically valid JavaScript with
/// scoping constructs (functions, blocks, `with`, `eval`) and runs the JS binder
/// without panicking.
#[doc(hidden)]
pub fn fuzz_js_binder(data: &[u8]) {
  let mut cursor = ByteCursor::new(data);
  let mut source = gen_block(&mut cursor, MAX_DEPTH);
  // Ensure the resulting script parses even if the generator emits only
  // declarations (e.g. function declarations).
  source.push_str(";");

  let opts = ParseOptions {
    dialect: Dialect::Js,
    source_type: SourceType::Script,
  };
  let Ok(mut ast) = parse_with_options(&source, opts) else {
    return;
  };
  let _ = bind_js(&mut ast, TopLevelMode::Global, FileId(0));
}
