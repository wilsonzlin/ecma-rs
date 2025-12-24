use crate::Diagnostic;
use crate::FileId;
use crate::Label;
use crate::TextRange;
use std::cmp::max;
use std::collections::BTreeSet;
use std::collections::HashMap;
use std::fmt::Write;

const TAB_WIDTH: usize = 2;

/// Source metadata used during rendering.
pub struct SourceFile<'a> {
  pub name: &'a str,
  pub text: &'a str,
}

/// Provides access to source text for rendering diagnostics.
pub trait SourceProvider {
  fn file_name(&self, file: FileId) -> Option<&str>;
  fn file_text(&self, file: FileId) -> Option<&str>;

  /// Convenience method to fetch both the file name and text together.
  fn source(&self, file: FileId) -> Option<SourceFile<'_>> {
    Some(SourceFile {
      name: self.file_name(file)?,
      text: self.file_text(file)?,
    })
  }
}

/// Options to control diagnostic rendering.
#[derive(Clone, Copy, Debug)]
pub struct RenderOptions {
  pub max_lines_per_label: usize,
  pub context_lines: usize,
  pub render_secondary_files: bool,
}

impl Default for RenderOptions {
  fn default() -> Self {
    Self {
      max_lines_per_label: usize::MAX,
      context_lines: 0,
      render_secondary_files: true,
    }
  }
}

/// Render a diagnostic into a human-readable string with caret highlighting.
pub fn render_diagnostic(provider: &dyn SourceProvider, diagnostic: &Diagnostic) -> String {
  render_diagnostic_with_options(provider, diagnostic, RenderOptions::default())
}

/// Render a diagnostic with explicit options.
pub fn render_diagnostic_with_options(
  provider: &dyn SourceProvider,
  diagnostic: &Diagnostic,
  options: RenderOptions,
) -> String {
  let mut output = String::new();

  let mut labels = Vec::with_capacity(diagnostic.labels.len() + 1);
  labels.push(Label {
    span: diagnostic.primary,
    message: diagnostic.message.clone(),
    is_primary: true,
  });
  labels.extend(diagnostic.labels.iter().cloned());

  labels.sort_by(|a, b| {
    b.is_primary
      .cmp(&a.is_primary)
      .then(a.span.file.cmp(&b.span.file))
      .then(a.span.range.start.cmp(&b.span.range.start))
      .then(a.span.range.end.cmp(&b.span.range.end))
      .then(a.message.cmp(&b.message))
  });

  if !options.render_secondary_files {
    let primary_file = diagnostic.primary.file;
    labels.retain(|label| label.span.file == primary_file);
  }

  let mut files: Vec<FileGroup> = Vec::new();
  for label in labels {
    match files.last_mut() {
      Some(group) if group.file == label.span.file => group.labels.push(label),
      _ => files.push(FileGroup {
        file: label.span.file,
        labels: vec![label],
      }),
    }
  }

  writeln!(
    output,
    "{}[{}]: {}",
    diagnostic.severity, diagnostic.code, diagnostic.message
  )
  .unwrap();

  for file in &files {
    render_file_group(provider, &mut output, file, &options);
  }

  for note in &diagnostic.notes {
    writeln!(output, "= note: {}", note).unwrap();
  }

  output
}

struct FileGroup {
  file: FileId,
  labels: Vec<Label>,
}

fn render_file_group(
  provider: &dyn SourceProvider,
  output: &mut String,
  file: &FileGroup,
  options: &RenderOptions,
) {
  let name = provider.file_name(file.file).unwrap_or("<unknown file>");
  let text = provider.file_text(file.file);

  match text {
    Some(text) => {
      let cache = LineCache::new(text);
      let first_offset =
        clamp_offset_to_char_boundary(text, file.labels[0].span.range.start as usize);
      let (line, col) = line_and_column(&cache, first_offset);
      writeln!(output, " --> {}:{}:{}", name, line, col).unwrap();
      let (lines_to_render, highlights) = plan_file_render(&cache, &file.labels, options);
      render_lines(&cache, &lines_to_render, &highlights, output);
    }
    None => {
      writeln!(output, " --> {}:?:?", name).unwrap();
      render_missing_source(output, file);
    }
  }
}

fn render_missing_source(output: &mut String, file: &FileGroup) {
  writeln!(output, "  | (source unavailable)").unwrap();
  for label in &file.labels {
    if !label.message.is_empty() {
      writeln!(output, "  = label: {}", label.message).unwrap();
    }
  }
}

fn render_lines<'a>(
  cache: &LineCache<'a>,
  lines: &[usize],
  highlights: &HashMap<usize, Vec<LineHighlight<'a>>>,
  output: &mut String,
) {
  if lines.is_empty() {
    writeln!(output, "  |").unwrap();
    return;
  }

  let max_line_no = lines.iter().copied().max().unwrap_or(0) + 1;
  let gutter_width = max_line_no.to_string().len().max(1);

  writeln!(output, "  |").unwrap();
  let mut prev_line: Option<usize> = None;
  for &line_idx in lines {
    if let Some(prev) = prev_line {
      if line_idx > prev + 1 {
        render_gap_line(output, gutter_width, line_idx - prev - 1);
      }
    }
    render_line(
      cache,
      line_idx,
      highlights.get(&line_idx),
      gutter_width,
      output,
    );
    prev_line = Some(line_idx);
  }
}

fn render_gap_line(output: &mut String, gutter_width: usize, skipped: usize) {
  writeln!(
    output,
    "{:>width$} | ... ({} lines elided)",
    "",
    skipped,
    width = gutter_width
  )
  .unwrap();
}

fn render_line<'a>(
  cache: &LineCache<'a>,
  line_idx: usize,
  highlights: Option<&Vec<LineHighlight<'a>>>,
  gutter_width: usize,
  output: &mut String,
) {
  let (line_start, line_end) = cache.line_bounds(line_idx);
  let raw_line = &cache.text[line_start..line_end];
  let expanded_line = expand_tabs(raw_line);

  writeln!(
    output,
    "{:>width$} | {}",
    line_idx + 1,
    expanded_line,
    width = gutter_width
  )
  .unwrap();

  if let Some(highlights) = highlights {
    for highlight in highlights {
      let mut underline_line = String::new();
      underline_line.push_str(&format!("{:>width$} | ", "", width = gutter_width));
      underline_line.push_str(&" ".repeat(highlight.start_col));
      underline_line.push_str(
        &std::iter::repeat(highlight.marker)
          .take(highlight.len)
          .collect::<String>(),
      );
      if let Some(message) = highlight.message {
        if !message.is_empty() {
          underline_line.push(' ');
          underline_line.push_str(message);
        }
      }
      underline_line.push('\n');
      output.push_str(&underline_line);
    }
  }
}

fn plan_file_render<'a>(
  cache: &LineCache<'a>,
  labels: &'a [Label],
  options: &RenderOptions,
) -> (Vec<usize>, HashMap<usize, Vec<LineHighlight<'a>>>) {
  let mut lines_to_render: BTreeSet<usize> = BTreeSet::new();
  let mut highlights: HashMap<usize, Vec<LineHighlight<'a>>> = HashMap::new();
  let max_line_index = cache.line_count().saturating_sub(1);

  for label in labels {
    let (start_offset, end_offset) = clamp_range(cache.text, label.span.range);
    let start_line = cache.line_index_at_offset(start_offset);
    let end_lookup = if end_offset > 0 {
      end_offset - 1
    } else {
      end_offset
    };
    let mut end_line = cache.line_index_at_offset(end_lookup);
    if end_line < start_line {
      end_line = start_line;
    }

    let visible_lines = visible_lines_for_span(start_line, end_line, options.max_lines_per_label);
    if visible_lines.is_empty() {
      continue;
    }

    let first_visible = *visible_lines.first().unwrap();

    for &line_idx in &visible_lines {
      lines_to_render.insert(line_idx);

      let (line_start, line_end) = cache.line_bounds(line_idx);
      let effective_start = if line_idx == start_line {
        start_offset
      } else {
        line_start
      };
      let effective_end = if line_idx == end_line {
        end_offset
      } else {
        line_end
      };

      let clamped_start = effective_start.clamp(line_start, line_end);
      let clamped_end = effective_end.clamp(clamped_start, line_end);
      let local_start = clamped_start.saturating_sub(line_start);
      let local_end = clamped_end.saturating_sub(line_start);
      let start_col = display_column(&cache.text[line_start..line_end], local_start);
      let end_col = display_column(&cache.text[line_start..line_end], local_end);
      let underline_len = max(1, end_col.saturating_sub(start_col));
      highlights.entry(line_idx).or_default().push(LineHighlight {
        start_col,
        len: underline_len,
        marker: if label.is_primary { '^' } else { '-' },
        message: if line_idx == first_visible {
          Some(label.message.as_str())
        } else {
          None
        },
      });

      let ctx_start = line_idx.saturating_sub(options.context_lines);
      let ctx_end = max_line_index.min(line_idx + options.context_lines);
      for ctx in ctx_start..=ctx_end {
        lines_to_render.insert(ctx);
      }
    }
  }

  let lines = lines_to_render.into_iter().collect::<Vec<_>>();
  (lines, highlights)
}

fn visible_lines_for_span(start_line: usize, end_line: usize, max_lines: usize) -> Vec<usize> {
  let total = end_line.saturating_sub(start_line).saturating_add(1);
  if max_lines == 0 {
    return Vec::new();
  }
  if max_lines == usize::MAX || total <= max_lines {
    return (start_line..=end_line).collect();
  }

  let head_count = (max_lines + 1) / 2;
  let tail_count = max_lines.saturating_sub(head_count);
  let mut lines = Vec::with_capacity(max_lines);

  for i in 0..head_count {
    let line_idx = start_line.saturating_add(i);
    if line_idx > end_line {
      break;
    }
    lines.push(line_idx);
  }

  if tail_count > 0 {
    let tail_start = end_line.saturating_sub(tail_count - 1);
    for idx in tail_start..=end_line {
      lines.push(idx);
    }
  }

  lines.sort_unstable();
  lines.dedup();
  lines
}

fn expand_tabs(line: &str) -> String {
  let mut expanded = String::with_capacity(line.len());
  for ch in line.chars() {
    if ch == '\t' {
      expanded.push_str(&" ".repeat(TAB_WIDTH));
    } else {
      expanded.push(ch);
    }
  }
  expanded
}

fn clamp_range(text: &str, range: TextRange) -> (usize, usize) {
  let len = text.len();
  let mut start = range.start as usize;
  let mut end = range.end as usize;
  if start > len {
    start = len;
  }
  if end > len {
    end = len;
  }
  if end < start {
    end = start;
  }
  (
    clamp_offset_to_char_boundary(text, start),
    clamp_offset_to_char_boundary(text, end),
  )
}

fn clamp_offset_to_char_boundary(text: &str, offset: usize) -> usize {
  let mut offset = offset;
  if offset > text.len() {
    offset = text.len();
  }
  while offset > 0 && !text.is_char_boundary(offset) {
    offset -= 1;
  }
  offset
}

fn display_column(line_text: &str, offset_in_line: usize) -> usize {
  let mut col = 0;
  let mut idx = 0;
  let target = offset_in_line.min(line_text.len());
  while idx < target {
    let ch = line_text[idx..].chars().next().unwrap();
    let ch_len = ch.len_utf8();
    if idx + ch_len > target {
      break;
    }
    col += if ch == '\t' { TAB_WIDTH } else { 1 };
    idx += ch_len;
  }
  col
}

fn line_and_column(cache: &LineCache<'_>, offset: usize) -> (usize, usize) {
  let line_idx = cache.line_index_at_offset(offset);
  let (line_start, line_end) = cache.line_bounds(line_idx);
  let col = display_column(
    &cache.text[line_start..line_end],
    offset.saturating_sub(line_start),
  );
  (line_idx + 1, col + 1)
}

struct LineCache<'a> {
  text: &'a str,
  starts: Vec<usize>,
}

impl<'a> LineCache<'a> {
  fn new(text: &'a str) -> Self {
    let mut starts = vec![0];
    for (idx, ch) in text.char_indices() {
      if ch == '\n' {
        starts.push(idx + 1);
      }
    }
    if starts.is_empty() {
      starts.push(0);
    }
    Self { text, starts }
  }

  fn line_count(&self) -> usize {
    self.starts.len()
  }

  fn line_bounds(&self, line_idx: usize) -> (usize, usize) {
    let start = *self.starts.get(line_idx).unwrap_or(&self.text.len());
    let end = if line_idx + 1 < self.starts.len() {
      self.starts[line_idx + 1].saturating_sub(1)
    } else {
      self.text.len()
    };
    (start, end.max(start))
  }

  fn line_index_at_offset(&self, offset: usize) -> usize {
    let clamped = offset.min(self.text.len());
    match self.starts.binary_search(&clamped) {
      Ok(idx) => idx.min(self.starts.len().saturating_sub(1)),
      Err(0) => 0,
      Err(idx) => idx - 1,
    }
  }
}

#[derive(Debug)]
struct LineHighlight<'a> {
  start_col: usize,
  len: usize,
  marker: char,
  message: Option<&'a str>,
}
