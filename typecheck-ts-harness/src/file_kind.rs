use typecheck_ts::lib_support::FileKind;

/// Infer a `typecheck-ts` [`FileKind`] from a virtual TypeScript-style path.
///
/// Paths are typically normalized via `diagnostics::paths::normalize_ts_path`
/// (e.g. `/a.ts`, `/dir/file.tsx`, `c:/foo/bar.ts`).
pub(crate) fn infer_file_kind(path: &str) -> FileKind {
  let lower = path.to_ascii_lowercase();

  if lower.ends_with(".d.ts") || lower.ends_with(".d.mts") || lower.ends_with(".d.cts") {
    return FileKind::Dts;
  }
  if lower.ends_with(".tsx") {
    return FileKind::Tsx;
  }
  if lower.ends_with(".ts") {
    return FileKind::Ts;
  }
  if lower.ends_with(".jsx") {
    return FileKind::Jsx;
  }
  if lower.ends_with(".js") {
    return FileKind::Js;
  }
  // `typecheck-ts` does not currently distinguish module-suffixed extensions,
  // so map them to the closest supported kind.
  if lower.ends_with(".mts") || lower.ends_with(".cts") {
    return FileKind::Ts;
  }
  if lower.ends_with(".mjs") || lower.ends_with(".cjs") {
    return FileKind::Js;
  }

  FileKind::Ts
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn infers_known_file_kinds() {
    assert_eq!(infer_file_kind("/a.d.ts"), FileKind::Dts);
    assert_eq!(infer_file_kind("/a.d.mts"), FileKind::Dts);
    assert_eq!(infer_file_kind("/a.d.cts"), FileKind::Dts);
    assert_eq!(infer_file_kind("/a.tsx"), FileKind::Tsx);
    assert_eq!(infer_file_kind("/a.ts"), FileKind::Ts);
    assert_eq!(infer_file_kind("/a.jsx"), FileKind::Jsx);
    assert_eq!(infer_file_kind("/a.js"), FileKind::Js);
    assert_eq!(infer_file_kind("/a.mts"), FileKind::Ts);
    assert_eq!(infer_file_kind("/a.cts"), FileKind::Ts);
    assert_eq!(infer_file_kind("/a.mjs"), FileKind::Js);
    assert_eq!(infer_file_kind("/a.cjs"), FileKind::Js);
  }
}
