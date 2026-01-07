export interface DiagnosticRange {
  start: number;
  end: number;
}

export interface DiagnosticSpan {
  file: number;
  range: DiagnosticRange;
}

export interface DiagnosticLabel {
  span: DiagnosticSpan;
  message: string;
  is_primary: boolean;
}

export interface Diagnostic {
  code: string;
  /**
   * Severity as serialized from the Rust `diagnostics` crate.
   *
   * Note: values are lowercase (`"error"`, `"warning"`, ...) to match the JSON
   * representation produced by serde.
   */
  severity: "error" | "warning" | "note" | "help";
  message: string;
  primary: DiagnosticSpan;
  labels: DiagnosticLabel[];
  notes: string[];
}

/**
 * Minifies JavaScript or TypeScript code.
 *
 * TypeScript/TSX inputs are accepted; type-only syntax is erased before
 * minification so the output is always JavaScript.
 *
 * Throws `Error & { diagnostics?: Diagnostic[] }` when minification fails. The
 * `diagnostics` property contains structured diagnostics describing the error.
 *
 * @param topLevelType - Parse mode for the top level ("global" or "module")
 * @param src - Source JS/TS code as a string or UTF-8 Buffer
 * @param options - Optional parsing / TypeScript lowering options
 * @returns Minified JS code as a UTF-8 Buffer
 */
export interface MinifyOptions {
  /**
   * Explicit parser dialect.
   *
   * - `"auto"` (default) matches the existing behaviour (try TS then TSX).
   * - Other values force a single dialect.
   */
  dialect?: "auto" | "js" | "jsx" | "ts" | "tsx" | "dts";

  /**
   * Whether to lower TypeScript/JS class fields into constructor assignments or
   * `Object.defineProperty` calls.
   */
  tsLowerClassFields?: boolean;

  /**
   * Class field lowering semantics. When `true` (default), lowering uses
   * `Object.defineProperty`.
   */
  tsUseDefineForClassFields?: boolean;
}

export function minify(
  topLevelType: "global" | "module",
  src: string | Buffer,
  options?: MinifyOptions,
): Buffer;
