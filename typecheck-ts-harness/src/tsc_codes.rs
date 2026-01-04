//! Helpers for aligning Rust checker diagnostic codes with TypeScript's numeric codes.
//!
//! The `typecheck-ts` checker emits stable string codes (for example `TC0007`) that are
//! meaningful within this repository, but `tsc` uses numeric codes (`TS2322` / `2322`).
//!
//! When comparing Rust diagnostics against `tsc` output, we want semantically equivalent
//! diagnostics to be considered a code match even if the Rust checker uses an internal
//! identifier. This module provides a deterministic mapping layer used by the harness
//! comparison logic.
//!
//! Some internal codes correspond to multiple possible `tsc` codes depending on context
//! (for example, the Rust checker uses the same `TC0007` for both assignments and
//! call-argument checks, while `tsc` uses `TS2322` and `TS2345` respectively). In those
//! cases we treat *any* of the mapped numeric codes as a match.
//!
//! The mapping table is intentionally small and only covers the most common diagnostics
//! needed for conformance/difftsc progress tracking. Add entries conservatively and keep
//! them stable.
/// Parse a diagnostic code string into a TypeScript numeric code.
///
/// Accepts:
/// - Raw numbers (`"2345"`)
/// - TypeScript-style prefixes (`"TS2345"`, `"ts2345"`)
pub(crate) fn parse_tsc_numeric_code(raw: &str) -> Option<u32> {
  let trimmed = raw
    .trim()
    .trim_start_matches(|c| c == 't' || c == 'T')
    .trim_start_matches(|c| c == 's' || c == 'S');
  trimmed.parse().ok()
}

/// Map a Rust checker diagnostic code (e.g. `TC0007`) to the corresponding `tsc` numeric codes.
///
/// Returns `None` when there is no known equivalent.
pub(crate) fn mapped_tsc_codes_for_rust_code(raw: &str) -> Option<&'static [u32]> {
  match raw.trim() {
    // Cannot find name 'x'.
    "TC0005" => Some(&[2304]),
    // Object literal may only specify known properties...
    "TC0006" => Some(&[2353]),
    // Type is not assignable to type...
    //
    // Used for general assignability checks; `tsc` uses different codes for
    // assignment expressions vs call arguments.
    "TC0007" => Some(&[2322, 2345]),
    // Property 'x' does not exist on type...
    "TC0008" => Some(&[2339]),
    // Variable is used before being assigned.
    "TC0009" => Some(&[2454]),
    // Cannot find module '...'.
    "TC1001" => Some(&[2307]),
    // Module '"..."' has no exported member '...'.
    "TC1002" => Some(&[2305]),
    // Expected N arguments, but got M.
    "TC1006" => Some(&[2554]),
    // Call errors:
    // - No overload matches this call.
    // - This expression is not callable.
    // - Some call-site constraint failures are reported by `tsc` as TS2345.
    "TC2000" => Some(&[2345, 2349, 2769]),
    // Multiple applicable overloads / ambiguity.
    "TC2001" => Some(&[2769]),
    // Cannot find name 'Foo' (type reference).
    "TC2008" => Some(&[2304]),
    // `import()` type resolution failures.
    "TC2010" => Some(&[2307]),
    // `typeof` type query failures generally surface as missing-name diagnostics in tsc.
    "TC2011" => Some(&[2304]),
    // `--noImplicitAny` family (multiple codes depending on context).
    "TC3000" => Some(&[7005, 7006, 7031, 7034]),
    // JSX diagnostics.
    "TC3001" => Some(&[17004]),
    "TC3002" => Some(&[2339]),
    "TC3003" => Some(&[2503, 7026]),
    // Variance annotation mismatch as implied by variance annotation.
    "TC3004" => Some(&[2636]),
    // `export =` combined with other exports.
    "BIND1005" => Some(&[2309]),
    _ => None,
  }
}

pub(crate) fn rust_code_matches_tsc(rust_code: &str, tsc_code: u32) -> bool {
  if let Some(num) = parse_tsc_numeric_code(rust_code) {
    return num == tsc_code;
  }
  mapped_tsc_codes_for_rust_code(rust_code)
    .map(|codes| codes.contains(&tsc_code))
    .unwrap_or(false)
}

#[cfg(test)]
mod tests {
  use super::*;

  #[test]
  fn parses_ts_prefixed_codes() {
    assert_eq!(parse_tsc_numeric_code("TS2345"), Some(2345));
    assert_eq!(parse_tsc_numeric_code("ts2345"), Some(2345));
    assert_eq!(parse_tsc_numeric_code("2345"), Some(2345));
  }

  #[test]
  fn maps_internal_codes_to_tsc() {
    assert!(rust_code_matches_tsc("TC0007", 2322));
    assert!(rust_code_matches_tsc("TC0007", 2345));
    assert!(!rust_code_matches_tsc("TC0007", 9999));

    assert!(rust_code_matches_tsc("TC0008", 2339));
    assert!(rust_code_matches_tsc("TC1001", 2307));
    assert!(rust_code_matches_tsc("TC1002", 2305));
    assert!(rust_code_matches_tsc("TC1006", 2554));
    assert!(rust_code_matches_tsc("TC2010", 2307));
    assert!(rust_code_matches_tsc("TC2011", 2304));
    assert!(rust_code_matches_tsc("TC3000", 7006));
    assert!(rust_code_matches_tsc("TC3001", 17004));
    assert!(rust_code_matches_tsc("TC3002", 2339));
    assert!(rust_code_matches_tsc("TC3003", 2503));
    assert!(rust_code_matches_tsc("TC3004", 2636));
    assert!(rust_code_matches_tsc("BIND1005", 2309));
  }
}
