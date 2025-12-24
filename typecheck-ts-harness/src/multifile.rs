use std::collections::BTreeMap;
use std::path::Path;
use std::path::PathBuf;

pub(crate) fn normalize_name(name: &str) -> String {
  use std::path::Component;
  let name = name.replace('\\', "/");
  let mut normalized = PathBuf::new();
  for component in Path::new(&name).components() {
    match component {
      Component::CurDir => {}
      Component::ParentDir => {
        normalized.pop();
      }
      other => normalized.push(other.as_os_str()),
    }
  }

  normalized.to_string_lossy().replace('\\', "/")
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct VirtualFile {
  pub name: String,
  pub content: String,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct SplitResult {
  pub files: Vec<VirtualFile>,
  pub module_directive: Option<String>,
  pub notes: Vec<String>,
}

const FILENAME_DIRECTIVE: &str = "@filename:";
const MODULE_DIRECTIVE: &str = "@module:";

pub fn split_test_file(path: &Path, contents: &str) -> SplitResult {
  let mut result = SplitResult::default();
  let default_name = path
    .file_name()
    .map(|p| p.to_string_lossy().to_string())
    .unwrap_or_else(|| "input.ts".to_string());

  let mut current_name = default_name;
  let mut current_content = String::new();
  let mut has_started = false;
  let mut seen_directive = false;

  for raw_line in contents.split_inclusive('\n') {
    let line = raw_line.trim_end_matches('\n');

    if let Some(name) = extract_directive(line, FILENAME_DIRECTIVE) {
      if has_started || seen_directive {
        result.files.push(VirtualFile {
          name: current_name.clone(),
          content: current_content.clone(),
        });
      }

      current_name = name;
      current_content.clear();
      has_started = false;
      seen_directive = true;
      continue;
    }

    if let Some(module) = extract_directive(line, MODULE_DIRECTIVE) {
      result.module_directive = Some(module.clone());
      result
        .notes
        .push(format!("module directive @module: {} ignored", module));
      continue;
    }

    has_started = true;
    current_content.push_str(raw_line);
  }

  if has_started || seen_directive || !current_content.is_empty() {
    result.files.push(VirtualFile {
      name: current_name,
      content: current_content,
    });
  } else if result.files.is_empty() {
    result.files.push(VirtualFile {
      name: current_name,
      content: current_content,
    });
  }

  let mut duplicates = BTreeMap::new();
  for file in &result.files {
    let normalized = normalize_name(&file.name);
    *duplicates.entry(normalized).or_insert(0usize) += 1;
  }

  for (name, count) in duplicates {
    if count > 1 {
      result.notes.push(format!(
        "duplicate @filename entry for {name}; last one wins"
      ));
    }
  }

  result
}

fn extract_directive(line: &str, directive: &str) -> Option<String> {
  let trimmed = line.trim_start();
  if !trimmed.starts_with("//") {
    return None;
  }

  let content = trimmed.trim_start_matches('/').trim_start();
  let lower = content.to_ascii_lowercase();
  if !lower.starts_with(directive) {
    return None;
  }

  let value = content[directive.len()..].trim();
  if value.is_empty() {
    None
  } else {
    Some(value.to_string())
  }
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
    assert_eq!(result.files[0].content, source);
  }

  #[test]
  fn splits_multiple_files_with_filename_directives() {
    let source = "// @filename: a.ts\nconst a = 1;\n// @Filename: b.ts\nconst b = a;\n";
    let result = split_test_file(Path::new("case.ts"), source);

    assert_eq!(result.files.len(), 2);
    assert_eq!(result.files[0].name, "a.ts");
    assert_eq!(result.files[0].content, "const a = 1;\n");
    assert_eq!(result.files[1].name, "b.ts");
    assert_eq!(result.files[1].content, "const b = a;\n");
  }

  #[test]
  fn records_module_directive() {
    let source = "// @module: commonjs\nconst a = 1;\n";
    let result = split_test_file(&PathBuf::from("mod.ts"), source);
    assert_eq!(result.module_directive.as_deref(), Some("commonjs"));
    assert_eq!(result.notes.len(), 1);
    assert!(result.notes[0].contains("module directive"));
  }

  #[test]
  fn handles_empty_files_between_directives() {
    let source = "// @filename: a.ts\n// @filename: b.ts\nconst b = 2;\n";
    let result = split_test_file(Path::new("empty.ts"), source);
    assert_eq!(result.files.len(), 2);
    assert_eq!(result.files[0].name, "a.ts");
    assert_eq!(result.files[0].content, "");
    assert_eq!(result.files[1].name, "b.ts");
    assert_eq!(result.files[1].content, "const b = 2;\n");
  }

  #[test]
  fn ignores_directive_like_text_outside_comment() {
    let source = "const marker = \"@filename: should_not_split.ts\";\n";
    let result = split_test_file(Path::new("single.ts"), source);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].name, "single.ts");
    assert_eq!(result.files[0].content, source);
  }

  #[test]
  fn removes_module_directive_from_content() {
    let source = "// @module: amd\nconst value = 1;\n";
    let result = split_test_file(Path::new("module.ts"), source);
    assert_eq!(result.files.len(), 1);
    assert_eq!(result.files[0].content, "const value = 1;\n");
    assert_eq!(result.module_directive.as_deref(), Some("amd"));
  }

  #[test]
  fn records_duplicate_filename_entries() {
    let source = "// @filename: a.ts\nconst first = 1;\n// @filename: ./a.ts\nconst second = 2;\n";
    let result = split_test_file(Path::new("dupe.ts"), source);

    assert_eq!(result.files.len(), 2);
    assert_eq!(
      result.notes,
      vec!["duplicate @filename entry for a.ts; last one wins"]
    );
  }
}
