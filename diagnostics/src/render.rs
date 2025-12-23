use crate::{Diagnostic, FileId, Label};
use std::cmp::max;
use std::fmt::Write;

/// Provides access to source text for rendering diagnostics.
pub trait SourceProvider {
  fn file_name(&self, file: FileId) -> &str;
  fn file_text(&self, file: FileId) -> &str;
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

  labels.sort_by(|a, b| {
    b
      .is_primary
      .cmp(&a.is_primary)
      .then(a.span.file.cmp(&b.span.file))
      .then(a.span.range.start.cmp(&b.span.range.start))
      .then(a.span.range.end.cmp(&b.span.range.end))
      .then(a.message.cmp(&b.message))
  });

  let mut max_line_no = 1usize;
  for label in &labels {
    let text = provider.file_text(label.span.file);
    let starts = line_starts(text);
    let start_line = line_index_at_offset(&starts, label.span.range.start as usize) + 1;
    let end_line =
      line_index_at_offset(&starts, label.span.range.end.saturating_sub(1) as usize) + 1;
    max_line_no = max(max_line_no, max(start_line, end_line));
  }
  let gutter_width = max_line_no.to_string().len().max(1);

  writeln!(
    output,
    "{}[{}]: {}",
    diagnostic.severity, diagnostic.code, diagnostic.message
  )
  .unwrap();
  let primary_text = provider.file_text(diagnostic.primary.file);
  let (line, col) = line_and_column(primary_text, diagnostic.primary.range.start as usize);
  writeln!(
    output,
    " --> {}:{}:{}",
    provider.file_name(diagnostic.primary.file),
    line,
    col
  )
  .unwrap();
  writeln!(output, "  |").unwrap();

  let mut current_file = Some(diagnostic.primary.file);

  for label in labels {
    if Some(label.span.file) != current_file {
      let (line, col) = line_and_column(
        provider.file_text(label.span.file),
        label.span.range.start as usize,
      );
      writeln!(output, " --> {}:{}:{}", provider.file_name(label.span.file), line, col).unwrap();
      writeln!(output, "  |").unwrap();
      current_file = Some(label.span.file);
    }
    render_label(provider, &mut output, &label, gutter_width);
  }

  for note in &diagnostic.notes {
    writeln!(output, "= note: {}", note).unwrap();
  }

  output
}

fn render_label(
  provider: &dyn SourceProvider,
  output: &mut String,
  label: &Label,
  gutter_width: usize,
) {
  let text = provider.file_text(label.span.file);
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
