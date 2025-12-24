use crate::Diagnostic;
use crate::FileId;
use crate::Label;
use std::cmp::max;
use std::fmt::Write;

/// Provides access to source text for rendering diagnostics.
///
/// Returning `None` allows consumers to gracefully handle missing files (for
/// example, when a `FileId` has been invalidated in an incremental host).
pub trait SourceProvider {
  /// Returns the display name for a file, or `None` if the file is unknown.
  fn file_name(&self, file: FileId) -> Option<&str>;
  /// Returns the file contents, or `None` if the file is unavailable.
  fn file_text(&self, file: FileId) -> Option<&str>;
}

/// Render a diagnostic into a human-readable string with caret highlighting.
pub fn render_diagnostic(provider: &dyn SourceProvider, diagnostic: &Diagnostic) -> String {
  let mut output = String::new();

  let mut labels = Vec::with_capacity(diagnostic.labels.len() + 1);
  labels.push(Label {
    span: diagnostic.primary,
    message: diagnostic.message.clone(),
    is_primary: true,
  });
  labels.extend(diagnostic.labels.iter().cloned());

  labels.sort();

  let mut max_line_no = 1usize;
  for label in &labels {
    if let Some(text) = provider.file_text(label.span.file) {
      let starts = line_starts(text);
      let start_line = line_index_at_offset(&starts, label.span.range.start as usize) + 1;
      let end_line =
        line_index_at_offset(&starts, label.span.range.end.saturating_sub(1) as usize) + 1;
      max_line_no = max(max_line_no, max(start_line, end_line));
    }
  }
  let gutter_width = max_line_no.to_string().len().max(1);

  writeln!(
    output,
    "{}[{}]: {}",
    diagnostic.severity, diagnostic.code, diagnostic.message
  )
  .unwrap();
  let primary_text = provider.file_text(diagnostic.primary.file);
  let primary_name = provider
    .file_name(diagnostic.primary.file)
    .unwrap_or("<unknown>");
  let (line, col) = primary_text
    .as_ref()
    .map(|text| line_and_column(text, diagnostic.primary.range.start as usize))
    .unwrap_or((1, diagnostic.primary.range.start as usize + 1));
  writeln!(output, " --> {}:{}:{}", primary_name, line, col).unwrap();
  writeln!(output, "  |").unwrap();

  let mut current_file = Some(diagnostic.primary.file);

  for label in labels {
    let text = provider.file_text(label.span.file);
    if Some(label.span.file) != current_file {
      let (line, col) = text
        .as_ref()
        .map(|text| line_and_column(text, label.span.range.start as usize))
        .unwrap_or((1, label.span.range.start as usize + 1));
      let name = provider.file_name(label.span.file).unwrap_or("<unknown>");
      writeln!(output, " --> {}:{}:{}", name, line, col).unwrap();
      writeln!(output, "  |").unwrap();
      current_file = Some(label.span.file);
    }
    render_label(text, &mut output, &label, gutter_width);
  }

  for note in &diagnostic.notes {
    writeln!(output, "= note: {}", note).unwrap();
  }

  output
}

fn render_label(text: Option<&str>, output: &mut String, label: &Label, gutter_width: usize) {
  if let Some(text) = text {
    render_label_with_text(text, output, label, gutter_width);
  } else {
    render_label_without_text(output, label, gutter_width);
  }
}

fn render_label_with_text(text: &str, output: &mut String, label: &Label, gutter_width: usize) {
  let starts = line_starts(text);
  let text_len = text.len();
  let start_offset = (label.span.range.start as usize).min(text_len);
  let end_offset = (label.span.range.end as usize).min(text_len);
  let start_line = line_index_at_offset(&starts, start_offset);
  let end_line = line_index_at_offset(&starts, end_offset.saturating_sub(1));

  let marker_char = if label.is_primary { '^' } else { '-' };

  for line_idx in start_line..=end_line {
    let line_start = starts[line_idx];
    let line_end = if line_idx + 1 < starts.len() {
      starts[line_idx + 1] - 1
    } else {
      text_len
    };

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

    let underline_start = clamped_start.saturating_sub(line_start);
    let underline_len = max(1, clamped_end.saturating_sub(clamped_start));
    let line_number = line_idx + 1;
    let line_text = &text[line_start..line_end];

    writeln!(
      output,
      "{:>width$} | {}",
      line_number,
      line_text,
      width = gutter_width
    )
    .unwrap();

    let mut underline_line = String::new();
    underline_line.push_str(&format!("{:>width$} | ", "", width = gutter_width));
    underline_line.push_str(&" ".repeat(underline_start));
    underline_line.push_str(
      &std::iter::repeat(marker_char)
        .take(underline_len)
        .collect::<String>(),
    );
    if line_idx == start_line && !label.message.is_empty() {
      underline_line.push(' ');
      underline_line.push_str(&label.message);
    }
    underline_line.push('\n');
    output.push_str(&underline_line);
  }
}

fn render_label_without_text(output: &mut String, label: &Label, gutter_width: usize) {
  let marker_char = if label.is_primary { '^' } else { '-' };
  writeln!(
    output,
    "{:>width$} | <source unavailable>",
    "",
    width = gutter_width
  )
  .unwrap();
  let mut underline_line = String::new();
  underline_line.push_str(&format!("{:>width$} | ", "", width = gutter_width));
  underline_line.push(marker_char);
  underline_line.push_str(&format!(
    " [{}..{}]",
    label.span.range.start, label.span.range.end
  ));
  if !label.message.is_empty() {
    underline_line.push(' ');
    underline_line.push_str(&label.message);
  }
  underline_line.push('\n');
  output.push_str(&underline_line);
}

fn line_and_column(text: &str, offset: usize) -> (usize, usize) {
  let starts = line_starts(text);
  let line_idx = line_index_at_offset(&starts, offset.min(text.len()));
  let line_start = starts[line_idx];
  (line_idx + 1, offset.min(text.len()) - line_start + 1)
}

fn line_index_at_offset(starts: &[usize], offset: usize) -> usize {
  match starts.binary_search(&offset) {
    Ok(idx) => idx,
    Err(0) => 0,
    Err(idx) => idx - 1,
  }
}

fn line_starts(text: &str) -> Vec<usize> {
  let mut starts = vec![0];
  for (idx, ch) in text.char_indices() {
    if ch == '\n' {
      starts.push(idx + 1);
    }
  }
  starts
}
