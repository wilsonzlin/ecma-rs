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
  severity: "Error" | "Warning" | "Note" | "Help";
  message: string;
  primary: DiagnosticSpan;
  labels: DiagnosticLabel[];
  notes: string[];
}

/**
 * Minifies JavaScript code.
 *
 * Throws `Error & { diagnostics?: Diagnostic[] }` when minification fails. The
 * `diagnostics` property contains structured diagnostics describing the error.
 *
 * @param topLevelType - Parse mode for the top level ("global" or "module")
 * @param src - Source JS code as a string or UTF-8 Buffer
 * @returns Minified JS code as a UTF-8 Buffer
 */
export function minify(topLevelType: "global" | "module", src: string | Buffer): Buffer;
