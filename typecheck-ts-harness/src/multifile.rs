use crate::directives::parse_directive;
use crate::directives::HarnessDirective;
use diagnostics::paths::normalize_ts_path;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::path::Path;
use std::sync::Arc;
pub(crate) fn normalize_name(name: &str) -> String {
  normalize_ts_path(name)
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirtualFile {
  pub name: String,
  pub content: Arc<str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SplitResult {
  pub files: Vec<VirtualFile>,
  pub deduped_files: Vec<VirtualFile>,
  pub directives: Vec<HarnessDirective>,
  pub notes: Vec<String>,
}

pub fn split_test_file(path: &Path, contents: &str) -> SplitResult {
  let mut result = SplitResult::default();
  let default_name = path
    .file_name()
    .map(|p| p.to_string_lossy().to_string())
    .unwrap_or_else(|| "input.ts".to_string());

  let mut current_name = default_name;
  let mut current_content = String::new();
  let mut has_started = false;

  for (idx, raw_line) in contents.split_inclusive('\n').enumerate() {
    let line_number = idx + 1;
    let line = raw_line.trim_end_matches(|c| c == '\n' || c == '\r');

    if let Some(directive) = parse_directive(line, line_number) {
      let name = directive.name.as_str();
      if name == "filename" {
        if let Some(value) = directive.value.clone() {
          if has_started {
            result.files.push(VirtualFile {
              name: std::mem::take(&mut current_name),
              content: std::mem::take(&mut current_content).into(),
            });
            current_name = value;
          } else {
            current_name = value;
            current_content.clear();
            has_started = true;
          }
        } else {
          result.notes.push(format!(
            "missing @filename value at line {line_number}; ignoring directive"
          ));
        }
        result.directives.push(directive);
        continue;
      }

      result.directives.push(directive);
      // Directive lines are metadata and are not included in the emitted virtual files.
      continue;
    }

    has_started = true;
    current_content.push_str(raw_line);
  }

  if has_started || !current_content.is_empty() {
    result.files.push(VirtualFile {
      name: current_name,
      content: current_content.into(),
    });
  } else if result.files.is_empty() {
    result.files.push(VirtualFile {
      name: current_name,
      content: current_content.into(),
    });
  }

  let mut duplicates = BTreeMap::new();
  for file in &result.files {
    let normalized = normalize_name(&file.name);
    *duplicates.entry(normalized).or_insert(0usize) += 1;
  }

  for (name, count) in duplicates.iter() {
    if *count > 1 {
      result.notes.push(format!(
        "duplicate @filename entry for {name}; last one wins"
      ));
    }
  }

  let mut last_occurrence = HashMap::new();
  for (idx, file) in result.files.iter().enumerate() {
    last_occurrence.insert(normalize_name(&file.name), idx);
  }
  for (idx, file) in result.files.iter().enumerate() {
    let normalized = normalize_name(&file.name);
    if last_occurrence.get(&normalized).copied() == Some(idx) {
      result.deduped_files.push(file.clone());
    }
  }

  result
}

#[cfg(test)]
mod tests {
  use super::*;
  use std::path::Path;
  use std::path::PathBuf;

  #[test]
  fn splits_single_file_without_directives() {
    let source = "const x = 1;\n";
    let result = split_test_file(Path::new("input.ts"), source);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].name, "input.ts");
    assert_eq!(result.files[0].content.as_ref(), source);
  }

  #[test]
  fn splits_multiple_files_with_filename_directives() {
    let source = "// @filename: a.ts\nconst a = 1;\n// @Filename: b.ts\nconst b = a;\n";
    let result = split_test_file(Path::new("case.ts"), source);

    assert_eq!(result.files.len(), 2);
    assert_eq!(result.files[0].name, "a.ts");
    assert_eq!(result.files[0].content.as_ref(), "const a = 1;\n");
    assert_eq!(result.files[1].name, "b.ts");
    assert_eq!(result.files[1].content.as_ref(), "const b = a;\n");
  }

  #[test]
  fn records_module_directive() {
    let source = "// @module: commonjs\nconst a = 1;\n";
    let result = split_test_file(&PathBuf::from("mod.ts"), source);
    assert!(result
      .directives
      .iter()
      .any(|d| d.name == "module" && d.value.as_deref() == Some("commonjs")));
  }

  #[test]
  fn handles_empty_files_between_directives() {
    let source = "// @filename: a.ts\n// @filename: b.ts\nconst b = 2;\n";
    let result = split_test_file(Path::new("empty.ts"), source);
    assert_eq!(result.files.len(), 2);
    assert_eq!(result.files[0].name, "a.ts");
    assert_eq!(result.files[0].content.as_ref(), "");
    assert_eq!(result.files[1].name, "b.ts");
    assert_eq!(result.files[1].content.as_ref(), "const b = 2;\n");
  }

  #[test]
  fn ignores_directive_like_text_outside_comment() {
    let source = "const marker = \"@filename: should_not_split.ts\";\n";
    let result = split_test_file(Path::new("single.ts"), source);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].name, "single.ts");
    assert_eq!(result.files[0].content.as_ref(), source);
  }

  #[test]
  fn removes_module_directive_from_content() {
    let source = "// @module: amd\nconst value = 1;\n";
    let result = split_test_file(Path::new("module.ts"), source);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].content.as_ref(), "const value = 1;\n");
    assert!(result
      .directives
      .iter()
      .any(|d| d.name == "module" && d.value.as_deref() == Some("amd")));
  }

  #[test]
  fn records_duplicate_filename_entries() {
    let source = "// @filename: a.ts\nconst first = 1;\n// @filename: ./a.ts\nconst second = 2;\n";
    let result = split_test_file(Path::new("dupe.ts"), source);

    assert_eq!(result.files.len(), 2);
    assert_eq!(result.deduped_files.len(), 1);
    assert_eq!(result.deduped_files[0].name, "./a.ts");
    assert_eq!(result.deduped_files[0].content.as_ref(), "const second = 2;\n");
    assert_eq!(
      result.notes,
      vec!["duplicate @filename entry for /a.ts; last one wins"]
    );
  }

  #[test]
  fn handles_crlf_filename_directive() {
    let source = "// @filename: a.ts\r\nconst a = 1;\r\n";
    let result = split_test_file(Path::new("case.ts"), source);

    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].name, "a.ts");
    assert_eq!(result.files[0].content.as_ref(), "const a = 1;\r\n");
  }

  #[test]
  fn removes_crlf_module_directive_from_content() {
    let source = "// @module: commonjs\r\nconst value = 1;\r\n";
    let result = split_test_file(Path::new("module.ts"), source);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].content.as_ref(), "const value = 1;\r\n");
    assert!(result
      .directives
      .iter()
      .any(|d| d.name == "module" && d.value.as_deref() == Some("commonjs")));
  }

  #[test]
  fn captures_directives_across_files() {
    let source = "\
// @target: ESNext
// @filename: a.ts
const a = 1;
// @strict: true
// @filename: folder/b.ts
// @jsx: react
const b = a;
";
    let result = split_test_file(Path::new("case.ts"), source);
    let directive_names: Vec<_> = result.directives.iter().map(|d| d.name.as_str()).collect();
    assert_eq!(
      directive_names,
      vec!["target", "filename", "strict", "filename", "jsx"]
    );
    assert_eq!(result.files.len(), 2);
    assert_eq!(result.files[0].name, "a.ts");
    assert_eq!(result.files[0].content.trim(), "const a = 1;");
    assert_eq!(result.files[1].name, "folder/b.ts");
    assert_eq!(result.files[1].content.trim(), "const b = a;");
  }

  #[test]
  fn deduplicates_windows_style_paths() {
    let source = "\
// @filename: src\\\\util.ts
const first = 1;
// @filename: src/util.ts
const second = 2;
";

    let result = split_test_file(Path::new("paths.ts"), source);
    assert_eq!(result.files.len(), 2);
    assert_eq!(result.deduped_files.len(), 1);
    assert_eq!(result.deduped_files[0].name, "src/util.ts");
    assert_eq!(result.deduped_files[0].content.trim(), "const second = 2;");
    assert!(result
      .notes
      .iter()
      .any(|n| n.contains("duplicate @filename entry for /src/util.ts")));
  }
}
